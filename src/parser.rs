use anyhow::{anyhow, Result};
use std::collections::HashMap;
use std::iter::Peekable;
use std::slice::Iter;

use crate::ast::{Ast, BinaryOp, Function, Prototype, StmtExpr};
use crate::lexer::Token;

pub struct Parser<'token> {
    bin_precedence: HashMap<BinaryOp, i32>,
    index: usize,
    tokens: Peekable<Iter<'token, Token>>,
}

impl<'token> Parser<'token> {
    pub fn new(tokens: &'token [Token]) -> Self {
        let mut bin_precedence = HashMap::new();
        bin_precedence.insert(BinaryOp::Eq, 10);
        bin_precedence.insert(BinaryOp::Ne, 20);
        bin_precedence.insert(BinaryOp::LessThan, 30);
        bin_precedence.insert(BinaryOp::MoreThan, 40);
        bin_precedence.insert(BinaryOp::Plus, 50);
        bin_precedence.insert(BinaryOp::Minus, 60);
        bin_precedence.insert(BinaryOp::Multiply, 70);
        bin_precedence.insert(BinaryOp::Divide, 80);
        Self {
            bin_precedence,
            index: 0,
            tokens: tokens.iter().peekable(),
        }
    }

    pub fn parse(&mut self) -> Result<Vec<Ast>> {
        let mut ast = vec![];
        while let Some(token) = self.tokens.peek() {
            match token {
                Token::Eof => break,
                Token::Semicolon => {
                    self.tokens.next();
                    continue;
                }
                Token::Def => {
                    let definition = self.definition()?;
                    ast.push(Ast::Function(definition));
                }
                Token::Extern => {
                    let prototype = self.extern_()?;
                    ast.push(Ast::Prototype(prototype));
                }
                _ => {
                    let func = self.toplevel()?;
                    ast.push(Ast::Function(func));
                }
            }
        }

        Ok(ast)
    }

    fn eat(&mut self, expect_token: Token) -> Result<()> {
        let cur_token = self.next_token()?;
        if *cur_token != expect_token {
            return Err(anyhow!(format!(
                "Expected token is {:?}, but got {:?}",
                expect_token, cur_token
            )));
        }
        Ok(())
    }

    fn next_token(&mut self) -> Result<&Token> {
        match self.tokens.next() {
            Some(token) => Ok(token),
            None => Err(anyhow!("Not found any token")),
        }
    }

    fn peek(&mut self) -> Result<&Token> {
        match self.tokens.peek() {
            Some(token) => Ok(token),
            None => Err(anyhow!("Not found any token")),
        }
    }

    fn definition(&mut self) -> Result<Function> {
        self.eat(Token::Def)?;
        let prototype = self.prototype()?;
        self.eat(Token::OpenBlock)?;
        let body = self.stmt_expr()?;
        Ok(Function { prototype, body })
    }

    fn prototype(&mut self) -> Result<Prototype> {
        let function_name = self.ident()?;
        self.eat(Token::OpenParen)?;

        let parameters = self.parameters()?;
        self.eat(Token::CloseParen)?;

        Ok(Prototype {
            function_name,
            parameters,
        })
    }

    fn parameters(&mut self) -> Result<Vec<String>> {
        let mut params = vec![];
        while let Token::Identifier(_) = *self.peek()? {
            let ident = match self.next_token()? {
                Token::Identifier(ident) => ident,
                _ => unreachable!(),
            };
            params.push(ident.clone());
        }

        Ok(params)
    }

    fn ident(&mut self) -> Result<String> {
        let token = self.next_token()?;
        match token {
            Token::Identifier(ident) => Ok(ident.to_string()),
            _ => Err(anyhow!(format!(
                "Expected token is a identifier, but got {:?}",
                token
            ))),
        }
    }

    fn expr(&mut self) -> Result<StmtExpr> {
        let left = self.primary()?;
        self.binary_right(0, left)
    }

    fn binary_op(&mut self) -> Result<Option<BinaryOp>> {
        let op = match self.peek()? {
            Token::Eq => BinaryOp::Eq,
            Token::Ne => BinaryOp::Ne,
            Token::LessThan => BinaryOp::LessThan,
            Token::MoreThan => BinaryOp::MoreThan,
            Token::Minus => BinaryOp::Minus,
            Token::Plus => BinaryOp::Plus,
            Token::Star => BinaryOp::Multiply,
            Token::Div => BinaryOp::Divide,
            _ => return Ok(None),
        };
        Ok(Some(op))
    }

    fn binary_right(&mut self, expr_precedence: i32, left: StmtExpr) -> Result<StmtExpr> {
        match self.binary_op()? {
            Some(op) => {
                let token_precedence = self.precedence(op)?;
                if token_precedence < expr_precedence {
                    Ok(left)
                } else {
                    // Eat binary operator.
                    self.next_token()?;
                    let right = self.primary()?;
                    let right = match self.binary_op()? {
                        Some(op) => {
                            if token_precedence < self.precedence(op)? {
                                self.binary_right(token_precedence + 1, right)?
                            } else {
                                right
                            }
                        }
                        None => right,
                    };
                    let left = StmtExpr::Binary(op, Box::new(left), Box::new(right));
                    self.binary_right(expr_precedence, left)
                }
            }
            None => Ok(left),
        }
    }

    fn precedence(&mut self, op: BinaryOp) -> Result<i32> {
        match self.bin_precedence.get(&op) {
            Some(&precedence) => Ok(precedence),
            None => Err(anyhow!(format!("Undefined operator: {:?}", op))),
        }
    }

    fn ident_expr(&mut self) -> Result<StmtExpr> {
        let name = self.ident()?;
        let ast = match self.peek()? {
            Token::OpenParen => {
                self.eat(Token::OpenParen)?;
                let args = self.args()?;
                self.eat(Token::CloseParen)?;
                StmtExpr::Call(name, args)
            }
            Token::Assign => {
                self.eat(Token::Assign)?;
                let expr = self.expr()?;
                StmtExpr::Assign(name, Box::new(expr))
            }
            _ => StmtExpr::Variable(name),
        };
        Ok(ast)
    }

    fn args(&mut self) -> Result<Vec<StmtExpr>> {
        if *self.peek()? == Token::CloseParen {
            return Ok(vec![]);
        }
        let mut args = vec![self.expr()?];
        while *self.peek()? == Token::Comma {
            self.eat(Token::Comma)?;
            args.push(self.expr()?);
        }
        Ok(args)
    }

    fn primary(&mut self) -> Result<StmtExpr> {
        let peek_token = self.peek()?;
        match peek_token {
            Token::Number(_) => match self.next_token()? {
                Token::Number(num) => Ok(StmtExpr::Number(*num)),
                _ => Err(anyhow!("Expected token is a number")),
            },
            Token::OpenParen => {
                self.eat(Token::OpenParen)?;
                let expr = self.expr()?;
                self.eat(Token::CloseParen)?;
                Ok(expr)
            }
            Token::Identifier(_) => self.ident_expr(),
            _ => Err(anyhow!(format!(
                "Expected token is an expression, but got {:?}",
                peek_token
            ))),
        }
    }

    fn extern_(&mut self) -> Result<Prototype> {
        self.eat(Token::Extern)?;
        self.prototype()
    }

    fn stmt_expr(&mut self) -> Result<Vec<StmtExpr>> {
        let mut stmt_exprs: Vec<StmtExpr> = vec![];
        loop {
            let peek_token = self.peek()?;
            match peek_token {
                Token::CloseBlock => {
                    self.eat(Token::CloseBlock)?;
                    break;
                }
                Token::If => {
                    self.eat(Token::If)?;
                    let condition = self.expr()?;
                    self.eat(Token::OpenBlock)?;
                    let then_body = self.stmt_expr()?;
                    let else_body: Vec<StmtExpr> = match self.peek()? {
                        Token::Else => {
                            self.eat(Token::Else)?;
                            self.eat(Token::OpenBlock)?;
                            self.stmt_expr()?
                        }
                        _ => vec![],
                    };
                    stmt_exprs.push(StmtExpr::If(Box::new(condition), then_body, else_body))
                }
                Token::While => {
                    self.eat(Token::While)?;
                    let condition = self.expr()?;
                    self.eat(Token::OpenBlock)?;
                    let loop_body = self.stmt_expr()?;
                    stmt_exprs.push(StmtExpr::While(Box::new(condition), loop_body))
                }
                Token::Semicolon | Token::Eof => {
                    break;
                }
                _ => {
                    let expr = self.expr()?;
                    stmt_exprs.push(expr)
                }
            }
        }

        Ok(stmt_exprs)
    }

    fn toplevel(&mut self) -> Result<Function> {
        let body = self.stmt_expr()?;
        self.index += 1;
        Ok(Function {
            prototype: Prototype {
                function_name: format!("__anon_{}", self.index),
                parameters: vec![],
            },
            body,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::{Ast, BinaryOp, StmtExpr};
    use crate::lexer::Lexer;
    use std::fs::File;

    macro_rules! extract_var {
        ($value:expr, $variant:path, $( $val:ident ),+) => {
            match $value {
                $variant($( $val ),+) => ($( $val ),+),
                _ => panic!("Missing specific variant, {:?}", $value),
            }
        };
    }

    macro_rules! assert_func {
        ($func:expr, $name:expr, $params:expr) => {
            let f = extract_var!($func, Ast::Function, x);
            assert_eq!(*&f.prototype.function_name, $name.to_string());
            assert_eq!(*&f.prototype.parameters, $params);
        };

        ($func:expr, $name:expr, $params:expr, $body:pat_param) => {
            let f = extract_var!($func, Ast::Function, x);
            assert_eq!(*&f.prototype.function_name, $name.to_string());
            assert_eq!(*&f.prototype.parameters, $params);
            assert!(matches!(*&f.body[0], $body));
        };
    }

    macro_rules! assert_binary {
        ($expr:expr, $op:path, $left:pat_param, $right:pat_param) => {
            assert_eq!(*$expr.0, $op);
            assert!(matches!(**$expr.1, $left));
            assert!(matches!(**$expr.2, $right));
        };
    }

    fn setup(file_path: &str) -> Vec<Ast> {
        let f = File::open(file_path).unwrap();
        let mut lexer = Lexer::new(f);
        let tokens = lexer.tokenize().unwrap();
        let mut parser = Parser::new(&tokens);
        parser.parse().unwrap()
    }

    #[test]
    fn test_arithmetic() {
        let ast = setup("tests/test_1.kal");
        assert!(matches!(&ast[0], Ast::Function(..)));

        let expect_params: Vec<String> = vec![];
        assert_func!(&ast[0], "compute", expect_params, StmtExpr::Binary(..));

        let func = extract_var!(&ast[0], Ast::Function, x);
        let binary = extract_var!(&func.body[0], StmtExpr::Binary, x, y, z);
        assert_binary!(
            &binary,
            BinaryOp::Plus,
            StmtExpr::Number(..),
            StmtExpr::Binary(..)
        );

        let right_1 = extract_var!(&**binary.2, StmtExpr::Binary, x, y, z);
        assert_binary!(
            &right_1,
            BinaryOp::Minus,
            StmtExpr::Binary(..),
            StmtExpr::Binary(..)
        );
        let right_1_left = extract_var!(&**right_1.1, StmtExpr::Binary, x, y, z);
        assert_binary!(
            &right_1_left,
            BinaryOp::Plus,
            StmtExpr::Number(..),
            StmtExpr::Number(..)
        );
        let right_1_right = extract_var!(&**right_1.2, StmtExpr::Binary, x, y, z);
        assert_binary!(
            &right_1_right,
            BinaryOp::Multiply,
            StmtExpr::Number(..),
            StmtExpr::Binary(..)
        );
        let right_2 = extract_var!(&**right_1_right.2, StmtExpr::Binary, x, y, z);
        assert_binary!(
            &right_2,
            BinaryOp::Divide,
            StmtExpr::Number(..),
            StmtExpr::Number(..)
        );

        assert!(matches!(&ast[1], Ast::Function(..)));
        let expect_params: Vec<String> = Vec::new();
        assert_func!(&ast[1], "__anon_1", expect_params, StmtExpr::Call(..));
    }

    #[test]
    fn test_less_more_than() {
        // # tests/test_2.kal
        // def than(x) {
        //   if x < 20 {  <- if1_cond
        //     1          <- if1_then
        //   }
        //   if x > 30 {  <- if2_cond
        //     2          <- if2_then
        //   } else {
        //     3          <- if2_else
        //   }
        // }
        //
        // than(10);      <- anon_call_1
        // than(40);      <- anon_call_2
        // than(30);      <- anon_call_3
        let ast = setup("tests/test_2.kal");
        assert!(matches!(&ast[0], Ast::Function(..)));

        let expect_params: Vec<String> = vec!["x".to_string()];
        assert_func!(&ast[0], "than", expect_params);

        let func = extract_var!(&ast[0], Ast::Function, x);

        // Test: if1_cond
        let if1 = extract_var!(&func.body[0], StmtExpr::If, x, y, z);
        let if1_cond = extract_var!(&**if1.0, StmtExpr::Binary, x, y, z);
        assert_binary!(
            &if1_cond,
            BinaryOp::LessThan,
            StmtExpr::Variable(..),
            StmtExpr::Number(..)
        );
        let if1_cond_lhs = extract_var!(&**if1_cond.1, StmtExpr::Variable, x);
        assert_eq!(*if1_cond_lhs, "x".to_string());
        let if1_cond_rhs = extract_var!(&**if1_cond.2, StmtExpr::Number, x);
        assert_eq!(*if1_cond_rhs, 20.);

        // Test: if1_then
        let if1_then = extract_var!(&(**if1.1)[0], StmtExpr::Number, x);
        assert_eq!(*if1_then, 1.);

        // Test: if2_cond
        let if2 = extract_var!(&func.body[1], StmtExpr::If, x, y, z);
        let if2_cond = extract_var!(&**if2.0, StmtExpr::Binary, x, y, z);
        assert_binary!(
            &if2_cond,
            BinaryOp::MoreThan,
            StmtExpr::Variable(..),
            StmtExpr::Number(..)
        );
        let if2_cond_lhs = extract_var!(&**if2_cond.1, StmtExpr::Variable, x);
        assert_eq!(*if2_cond_lhs, "x".to_string());
        let if2_cond_rhs = extract_var!(&**if2_cond.2, StmtExpr::Number, x);
        assert_eq!(*if2_cond_rhs, 30.);

        // Test: if2_then
        let if2_then = extract_var!(&(**if2.1)[0], StmtExpr::Number, x);
        assert_eq!(*if2_then, 2.);
        // Test: if2_else
        let if2_else = extract_var!(&(**if2.2)[0], StmtExpr::Number, x);
        assert_eq!(*if2_else, 3.);

        let empty_params: Vec<String> = Vec::new();
        // Test: anon_call_1
        assert_func!(&ast[1], "__anon_1", empty_params, StmtExpr::Call(..));
        // Test: anon_call_2
        assert_func!(&ast[2], "__anon_2", empty_params, StmtExpr::Call(..));
        // Test: anon_call_3
        assert_func!(&ast[3], "__anon_3", empty_params, StmtExpr::Call(..));
    }
}
