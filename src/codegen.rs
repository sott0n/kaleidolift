use anyhow::{anyhow, Result};
use std::collections::HashMap;
use std::mem;

use cranelift::codegen::ir::InstBuilder;
use cranelift::prelude::{
    types, AbiParam, FloatCC, FunctionBuilder, FunctionBuilderContext, Value, Variable,
};
use cranelift_codegen::binemit::{NullStackMapSink, NullTrapSink};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{default_libcall_names, FuncId, Linkage, Module};

use crate::ast::{Ast, BinaryOp, Expr, Function, Prototype};

pub struct Generator<'ast> {
    builder_context: FunctionBuilderContext,
    functions: HashMap<String, CompiledFunction>,
    module: JITModule,
    variable_builder: VariableBuilder,
    ast: &'ast [Ast],
}

impl<'ast> Generator<'ast> {
    pub fn new(ast: &'ast [Ast]) -> Self {
        Self {
            builder_context: FunctionBuilderContext::new(),
            functions: HashMap::new(),
            module: JITModule::new(JITBuilder::new(default_libcall_names())),
            variable_builder: VariableBuilder::new(),
            ast,
        }
    }

    pub fn gen(&mut self) -> Result<()> {
        for node in self.ast.iter() {
            match node {
                Ast::Function(f) => match self.function(f) {
                    Ok(_func) => (),
                    Err(e) => return Err(e),
                },
                Ast::Prototype(p) => match self.prototype(p, Linkage::Import) {
                    Ok(_proto) => (),
                    Err(e) => return Err(e),
                },
            };
        }
        Ok(())
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
        let func_id = self.prototype(&function.prototype, Linkage::Export)?;

        let mut builder = FunctionBuilder::new(&mut context.func, &mut self.builder_context);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let mut values = HashMap::new();
        for (i, name) in params.iter().enumerate() {
            let val = builder.block_params(entry_block)[i];
            let variable = self.variable_builder.create_var(&mut builder, val);
            values.insert(name.clone(), variable);
        }

        if let Some(ref mut func) = self.functions.get_mut(&func_name) {
            func.defined = true;
        }

        let mut generator = FunctionGenerator {
            builder,
            functions: &self.functions,
            module: &mut self.module,
            values,
        };
        let return_value = match generator.expr(&function.body) {
            Ok(value) => value,
            Err(e) => {
                generator.builder.finalize();
                self.functions.remove(&func_name);
                return Err(e);
            }
        };

        generator.builder.ins().return_(&[return_value]);
        generator.builder.finalize();
        println!("{}", context.func.display().to_string());

        let mut trap_sink = NullTrapSink {};
        let mut stack_map_sink = NullStackMapSink {};

        self.module
            .define_function(func_id, &mut context, &mut trap_sink, &mut stack_map_sink)?;
        self.module.clear_context(&mut context);
        self.module.finalize_definitions();

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
    values: HashMap<String, Variable>,
}

impl<'a> FunctionGenerator<'a> {
    fn expr(&mut self, expr: &Expr) -> Result<Value> {
        let value = match expr {
            Expr::Number(num) => self.builder.ins().f64const(*num),
            Expr::Variable(name) => match self.values.get(&*name) {
                Some(&variable) => self.builder.use_var(variable),
                None => return Err(anyhow!(format!("Undefined variable {}", name))),
            },
            Expr::Binary(op, left, right) => {
                let left = self.expr(&*left)?;
                let right = self.expr(&*right)?;
                match op {
                    BinaryOp::Plus => self.builder.ins().fadd(left, right),
                    BinaryOp::Minus => self.builder.ins().fsub(left, right),
                    BinaryOp::Multiply => self.builder.ins().fmul(left, right),
                    BinaryOp::Divide => self.builder.ins().fdiv(left, right),
                    BinaryOp::LessThan => {
                        let boolean = self.builder.ins().fcmp(FloatCC::LessThan, left, right);
                        let int = self.builder.ins().bint(types::I32, boolean);
                        self.builder.ins().fcvt_from_sint(types::F64, int)
                    }
                    BinaryOp::MoreThan => {
                        let boolean = self.builder.ins().fcmp(FloatCC::LessThan, right, left);
                        let int = self.builder.ins().bint(types::I32, boolean);
                        self.builder.ins().fcvt_from_sint(types::F64, int)
                    }
                }
            }
            Expr::Call(name, args) => match self.functions.get(&*name) {
                Some(func) => {
                    if func.param_count != args.len() {
                        return Err(anyhow!(format!(
                            "Wrong function's argument count, expect: {}, got: {}",
                            func.param_count,
                            args.len()
                        )));
                    }
                    let local_func = self.module.declare_func_in_func(func.id, self.builder.func);
                    let arguments: Result<Vec<_>> = args.iter().map(|arg| self.expr(arg)).collect();
                    let arguments = arguments?;
                    let call = self.builder.ins().call(local_func, &arguments);
                    self.builder.inst_results(call)[0]
                }
                None => return Err(anyhow!(format!("Undefined function: {}", name))),
            },
        };
        Ok(value)
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
