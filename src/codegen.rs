use anyhow::{anyhow, Result};
use std::collections::HashMap;
use std::mem;
use std::str::FromStr;

use cranelift::codegen::ir::InstBuilder;
use cranelift::codegen::settings::Configurable;
use cranelift::prelude::{
    isa, settings, types, AbiParam, FloatCC, FunctionBuilder, FunctionBuilderContext, Value,
    Variable,
};
use cranelift_codegen::binemit::{NullStackMapSink, NullTrapSink};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{default_libcall_names, FuncId, Linkage, Module};
use cranelift_preopt::optimize;
use target_lexicon::triple;

use crate::ast::{Ast, BinaryOp, Function, Prototype, StmtExpr};

pub struct Generator<'ast> {
    builder_context: FunctionBuilderContext,
    functions: HashMap<String, CompiledFunction>,
    module: JITModule,
    variable_builder: VariableBuilder,
    ast: &'ast [Ast],
}

impl<'ast> Generator<'ast> {
    pub fn new(ast: &'ast [Ast]) -> Self {
        let mut flag_builder = settings::builder();
        // You can set opt_level: any among none, speed or speed_and_size.
        flag_builder
            .set("opt_level", "speed_and_size")
            .expect("set optlevel");

        let isa_builder = isa::lookup(triple!("x86_64-unknown-unknown-elf")).expect("isa");
        let isa = isa_builder.finish(settings::Flags::new(flag_builder));
        let libcall_names = default_libcall_names();

        Self {
            builder_context: FunctionBuilderContext::new(),
            functions: HashMap::new(),
            module: JITModule::new(JITBuilder::with_isa(isa, libcall_names)),
            variable_builder: VariableBuilder::new(),
            ast,
        }
    }

    pub fn gen(&mut self) -> Result<Option<f64>> {
        let mut result: Option<f64> = None;
        for node in self.ast.iter() {
            result = match node {
                Ast::Function(f) => match self.function(f) {
                    Ok(func) => Some(func()),
                    Err(e) => return Err(e),
                },
                Ast::Prototype(p) => match self.prototype(p, Linkage::Import) {
                    Ok(_proto) => None,
                    Err(e) => return Err(e),
                },
            };
        }
        Ok(result)
    }

    pub fn function(&mut self, function: &Function) -> Result<fn() -> f64> {
        let mut context = self.module.make_context();
        let signature = &mut context.func.signature;
        let params = &function.prototype.parameters;

        // This kaleidoscope lang has only f64 type.
        for _param in params {
            signature.params.push(AbiParam::new(types::F64));
        }
        signature.returns.push(AbiParam::new(types::F64));

        let func_name = function.prototype.function_name.to_string();
        // Create a function via `prototype()` and then insert it into self.functions.
        let func_id = self.prototype(&function.prototype, Linkage::Export)?;

        let mut builder = FunctionBuilder::new(&mut context.func, &mut self.builder_context);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        // After this instruction, specify where a next instruction.
        builder.switch_to_block(entry_block);
        // Sealing means that we tell cranelift that all the deprodecessors of the block
        // are known. This block is a entry block, then call `seal_block` func.
        builder.seal_block(entry_block);

        // Create a variable hash map with (func-name, variable index).
        let mut variables = HashMap::new();
        for (i, name) in params.iter().enumerate() {
            let val = builder.block_params(entry_block)[i];
            let variable = self.variable_builder.create_var(&mut builder, val);
            variables.insert(name.clone(), variable);
        }

        // To do re-definition error at `prototype()`, check if function exists.
        if let Some(ref mut func) = self.functions.get_mut(&func_name) {
            func.defined = true;
        }

        let mut generator = FunctionGenerator {
            builder,
            functions: &self.functions,
            module: &mut self.module,
            variables,
        };
        // Expr function body and then return a opaque to an SSA value as return value.
        let return_value = match generator.translate(&function.body) {
            Ok(value) => value,
            Err(e) => {
                generator.builder.finalize();
                self.functions.remove(&func_name);
                return Err(e);
            }
        };

        generator.builder.ins().return_(&[return_value]);
        generator.builder.finalize();

        // Generate optimized CLIF.
        optimize(&mut context, &*self.module.isa())?;
        println!("{}", context.func.display().to_string());

        // TrapSink is to receive trap code and offsets.
        let mut trap_sink = NullTrapSink {};
        // StackMapSink is to emit stack maps.
        let mut stack_map_sink = NullStackMapSink {};

        self.module
            .define_function(func_id, &mut context, &mut trap_sink, &mut stack_map_sink)?;
        self.module.clear_context(&mut context);
        self.module.finalize_definitions();

        if func_name.starts_with("__anon_") {
            self.functions.remove(&func_name);
        }

        // Finally, we get the pointer to the generated code and cast it to a Rust function.
        unsafe { Ok(mem::transmute(self.module.get_finalized_function(func_id))) }
    }

    pub fn prototype(&mut self, prototype: &Prototype, linkage: Linkage) -> Result<FuncId> {
        let func_name = &prototype.function_name;
        let params = &prototype.parameters;
        match self.functions.get(func_name) {
            // Already exists a function.
            Some(func) => {
                if func.defined {
                    return Err(anyhow!(format!("Redefinition of function: {}", func_name)));
                }
                if func.param_count != params.len() {
                    return Err(anyhow!(format!(
                        "`{}`: redefinition of function's parameters defferent, {}(before) vs {}(after)",
                        func_name,
                        func.param_count,
                        params.len()
                    )));
                }
                Ok(func.id)
            }
            None => {
                let mut signature = self.module.make_signature();
                for _param in params {
                    signature.params.push(AbiParam::new(types::F64));
                }
                signature.returns.push(AbiParam::new(types::F64));

                let id = match self.module.declare_function(func_name, linkage, &signature) {
                    Ok(id) => id,
                    Err(e) => return Err(anyhow!(e)),
                };
                self.functions.insert(
                    func_name.to_string(),
                    CompiledFunction {
                        defined: false,
                        id,
                        param_count: params.len(),
                    },
                );
                Ok(id)
            }
        }
    }
}

struct CompiledFunction {
    defined: bool,
    id: FuncId,
    param_count: usize,
}

pub struct FunctionGenerator<'a> {
    builder: FunctionBuilder<'a>,
    functions: &'a HashMap<String, CompiledFunction>,
    module: &'a mut JITModule,
    variables: HashMap<String, Variable>,
}

impl<'a> FunctionGenerator<'a> {
    fn translate(&mut self, stmts: &[StmtExpr]) -> Result<Value> {
        let mut return_value: Option<Value> = None;
        for expr in stmts {
            return_value = Some(self.translate_expr(&*expr)?);
        }
        if return_value.is_none() {
            return Err(anyhow!("Failed expr a body"));
        }

        Ok(return_value.unwrap())
    }

    fn translate_expr(&mut self, expr: &StmtExpr) -> Result<Value> {
        let value = match expr {
            StmtExpr::Number(num) => self.builder.ins().f64const(*num),
            StmtExpr::Variable(name) => match self.variables.get(&*name) {
                Some(&variable) => self.builder.use_var(variable),
                None => return Err(anyhow!(format!("Undefined variable {}", name))),
            },
            StmtExpr::Assign(name, expr) => self.translate_assign(&*name, &*expr)?,
            StmtExpr::Binary(op, left, right) => self.translate_binary(*op, left, right)?,
            StmtExpr::Call(name, args) => self.translate_call(name, args)?,
            StmtExpr::If(cond, then_body, else_body) => {
                self.translate_if(cond, then_body, else_body)?
            }
            StmtExpr::While(cond, loop_body) => self.translate_while_loop(cond, loop_body)?,
        };
        Ok(value)
    }

    fn translate_binary(
        &mut self,
        op: BinaryOp,
        left: &StmtExpr,
        right: &StmtExpr,
    ) -> Result<Value> {
        let left = self.translate_expr(&*left)?;
        let right = self.translate_expr(&*right)?;
        let value = match op {
            BinaryOp::Plus => self.builder.ins().fadd(left, right),
            BinaryOp::Minus => self.builder.ins().fsub(left, right),
            BinaryOp::Multiply => self.builder.ins().fmul(left, right),
            BinaryOp::Divide => self.builder.ins().fdiv(left, right),
            BinaryOp::Eq => {
                let boolean = self.builder.ins().fcmp(FloatCC::Equal, left, right);
                self.builder.ins().bint(types::I32, boolean)
            }
            BinaryOp::Ne => {
                let boolean = self.builder.ins().fcmp(FloatCC::NotEqual, left, right);
                self.builder.ins().bint(types::I32, boolean)
            }
            BinaryOp::LessThan => {
                let boolean = self.builder.ins().fcmp(FloatCC::LessThan, left, right);
                self.builder.ins().bint(types::I32, boolean)
            }
            BinaryOp::MoreThan => {
                let boolean = self.builder.ins().fcmp(FloatCC::GreaterThan, left, right);
                self.builder.ins().bint(types::I32, boolean)
            }
        };
        Ok(value)
    }

    fn translate_assign(&mut self, name: &str, expr: &StmtExpr) -> Result<Value> {
        let assign_value = self.translate_expr(expr)?;
        let variable = self.variables.get(name).unwrap();
        self.builder.def_var(*variable, assign_value);
        Ok(assign_value)
    }

    fn translate_call(&mut self, name: &str, args: &[StmtExpr]) -> Result<Value> {
        match self.functions.get(&*name) {
            Some(func) => {
                if func.param_count != args.len() {
                    return Err(anyhow!(format!(
                        "Wrong function's argument count, expect: {}, got: {}",
                        func.param_count,
                        args.len()
                    )));
                }
                let local_func = self.module.declare_func_in_func(func.id, self.builder.func);
                let arguments: Result<Vec<_>> =
                    args.iter().map(|arg| self.translate_expr(&*arg)).collect();
                let arguments = arguments?;
                let call = self.builder.ins().call(local_func, &arguments);
                Ok(self.builder.inst_results(call)[0])
            }
            None => return Err(anyhow!(format!("Undefined function: {}", name))),
        }
    }

    fn translate_if(
        &mut self,
        cond: &StmtExpr,
        then_body: &[StmtExpr],
        else_body: &[StmtExpr],
    ) -> Result<Value> {
        let cond_value = self.translate_expr(cond)?;

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Add a block parameters as PHI function in SSA.
        self.builder.append_block_param(merge_block, types::F64);

        self.builder.ins().brz(cond_value, else_block, &[]);
        self.builder.ins().jump(then_block, &[]);
        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);

        let mut then_return = self.builder.ins().f64const(0.);
        for expr in then_body {
            then_return = self.translate_expr(expr)?;
        }
        // Jump to the merge block, passing it the block return value.
        self.builder.ins().jump(merge_block, &[then_return]);

        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);

        let mut else_return = self.builder.ins().f64const(0.);
        for expr in else_body {
            else_return = self.translate_expr(expr)?;
        }
        // Jump to the merge block, passing it the block return value.
        self.builder.ins().jump(merge_block, &[else_return]);

        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        let phi = self.builder.block_params(merge_block)[0];

        Ok(phi)
    }

    fn translate_while_loop(&mut self, cond: &StmtExpr, loop_body: &[StmtExpr]) -> Result<Value> {
        let header_block = self.builder.create_block();
        let body_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header_block, &[]);
        self.builder.switch_to_block(header_block);

        let cond_value = self.translate_expr(cond)?;
        self.builder.ins().brz(cond_value, exit_block, &[]);
        self.builder.ins().jump(body_block, &[]);

        self.builder.switch_to_block(body_block);
        self.builder.seal_block(body_block);

        for expr in loop_body {
            self.translate_expr(expr)?;
        }
        self.builder.ins().jump(header_block, &[]);

        self.builder.switch_to_block(exit_block);
        self.builder.seal_block(header_block);
        self.builder.seal_block(exit_block);

        Ok(self.builder.ins().f64const(0.))
    }
}

struct VariableBuilder {
    index: u32,
}

impl VariableBuilder {
    fn new() -> Self {
        Self { index: 0 }
    }

    fn create_var(&mut self, builder: &mut FunctionBuilder, value: Value) -> Variable {
        let variable = Variable::with_u32(self.index);
        builder.declare_var(variable, types::F64);
        self.index += 1;
        builder.def_var(variable, value);
        variable
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use std::fs::File;

    fn setup(file_path: &str) -> Vec<Ast> {
        let f = File::open(file_path).unwrap();
        let mut lexer = Lexer::new(f);
        let tokens = lexer.tokenize().unwrap();
        let mut parser = Parser::new(&tokens);
        parser.parse().unwrap()
    }

    #[test]
    fn test_1() {
        let ast = setup("tests/test_1.kal");
        let mut gen = Generator::new(&ast);
        let result = gen.gen().unwrap().unwrap();
        assert_eq!(result, 10020.5);
    }
}
