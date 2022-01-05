use anyhow::{anyhow, Result};
use std::collections::HashMap;
use std::iter::Peekable;
use std::slice::Iter;

use crate::ast::{Ast, BinaryOp, Cond, Expr, Function, Prototype, Stmt, StmtExpr};
use crate::lexer::Token;

pub struct Parser<'token> {
    bin_precedence: HashMap<BinaryOp, i32>,
    index: usize,
    tokens: Peekable<Iter<'token, Token>>,
}

impl<'token> Parser<'token> {
    pub fn new(tokens: &'token [Token]) -> Self {
        let mut bin_precedence = HashMap::new();
        bin_precedence.insert(BinaryOp::LessThan, 10);
        bin_precedence.insert(BinaryOp::MoreThan, 20);
        bin_precedence.insert(BinaryOp::Plus, 30);
        bin_precedence.insert(BinaryOp::Minus, 40);
        bin_precedence.insert(BinaryOp::Multiply, 50);
        bin_precedence.insert(BinaryOp::Divide, 60);
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

    fn expr(&mut self) -> Result<Expr> {
        let left = self.primary()?;
        self.binary_right(0, left)
    }

    fn binary_op(&mut self) -> Result<Option<BinaryOp>> {
        let op = match self.peek()? {
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

    fn binary_right(&mut self, expr_precedence: i32, left: Expr) -> Result<Expr> {
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
                    let left = Expr::Binary(op, Box::new(left), Box::new(right));
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

    fn ident_expr(&mut self) -> Result<Expr> {
        let name = self.ident()?;
        let ast = match self.peek()? {
            Token::OpenParen => {
                self.eat(Token::OpenParen)?;
                let args = self.args()?;
                self.eat(Token::CloseParen)?;
                Expr::Call(name, args)
            }
            _ => Expr::Variable(name),
        };
        Ok(ast)
    }

    fn args(&mut self) -> Result<Vec<Expr>> {
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

    fn primary(&mut self) -> Result<Expr> {
        let peek_token = self.peek()?;
        match peek_token {
            Token::Number(_) => match self.next_token()? {
                Token::Number(num) => Ok(Expr::Number(*num)),
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

    fn stmt_expr(&mut self) -> Result<StmtExpr> {
        let peek_token = self.peek()?;
        match peek_token {
            Token::If => {
                self.eat(Token::If)?;
                let condition = self.expr()?;
                self.eat(Token::Then)?;
                let block = self.expr()?;
                let else_expr: Option<Box<Expr>> = match self.peek()? {
                    Token::Else => {
                        self.eat(Token::Else)?;
                        let else_block = self.expr()?;
                        Some(Box::new(else_block))
                    }
                    _ => None,
                };
                Ok(StmtExpr::Stmt(Stmt::Cond(Cond {
                    cond: Box::new(condition),
                    then: Box::new(block),
                    else_then: else_expr,
                })))
            }
            _ => {
                let expr = self.expr()?;
                Ok(StmtExpr::Expr(expr))
            }
        }
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
    use crate::ast::{Ast, BinaryOp, Expr, StmtExpr};
    use crate::lexer::Lexer;
    use std::fs::File;

    macro_rules! extract_var {
        ($value:expr, $variant:path, $( $val:ident ),+) => {
            match $value {
                $variant($( $val ),+) => ($( $val ),+),
                _ => panic!("Missing specific variant"),
            }
        };
    }

    macro_rules! assert_func {
        ($func:expr, $name:expr, $params:expr, $body:pat_param) => {
            let f = extract_var!($func, Ast::Function, x);
            assert_eq!(*&f.prototype.function_name, $name.to_string());
            assert_eq!(*&f.prototype.parameters, $params);
            assert!(matches!(*&f.body, $body));
        };
    }

    macro_rules! assert_expr {
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
        assert_func!(
            &ast[0],
            "compute",
            expect_params,
            StmtExpr::Expr(Expr::Binary(..))
        );

        let func = extract_var!(&ast[0], Ast::Function, x);
        let expr = extract_var!(&func.body, StmtExpr::Expr, x);
        let binary = extract_var!(expr, Expr::Binary, x, y, z);
        assert_expr!(&binary, BinaryOp::Plus, Expr::Number(..), Expr::Binary(..));

        let right_1 = extract_var!(&**binary.2, Expr::Binary, x, y, z);
        assert_expr!(
            &right_1,
            BinaryOp::Minus,
            Expr::Binary(..),
            Expr::Binary(..)
        );
        let right_1_left = extract_var!(&**right_1.1, Expr::Binary, x, y, z);
        assert_expr!(
            &right_1_left,
            BinaryOp::Plus,
            Expr::Number(..),
            Expr::Number(..)
        );
        let right_1_right = extract_var!(&**right_1.2, Expr::Binary, x, y, z);
        assert_expr!(
            &right_1_right,
            BinaryOp::Multiply,
            Expr::Number(..),
            Expr::Binary(..)
        );
        let right_2 = extract_var!(&**right_1_right.2, Expr::Binary, x, y, z);
        assert_expr!(
            &right_2,
            BinaryOp::Divide,
            Expr::Number(..),
            Expr::Number(..)
        );

        assert!(matches!(&ast[1], Ast::Function(..)));
        let expect_params: Vec<String> = Vec::new();
        assert_func!(
            &ast[1],
            "__anon_1",
            expect_params,
            StmtExpr::Expr(Expr::Call(..))
        );
    }

    //#[test]
    //fn test_less_more_than() {
    //    let ast = setup("tests/test_2.kal");
    //    assert!(matches!(&ast[0], Ast::Function(..)));

    //    let expect_params: Vec<String> = vec!["x".to_string()];
    //    assert_func!(&ast[0], "than", expect_params, Expr::Variable(..));

    //    assert!(matches!(&ast[1], Ast::Function(..)));
    //    let expect_params: Vec<String> = vec![];
    //    assert_func!(&ast[1], "__anon_1", expect_params, Expr::Binary(..));

    //    let func = extract_var!(&ast[1], Ast::Function, x);
    //    let binary = extract_var!(&func.body, Expr::Binary, x, y, z);
    //    assert_expr!(
    //        &binary,
    //        BinaryOp::LessThan,
    //        Expr::Variable(..),
    //        Expr::Number(..)
    //    );

    //    assert!(matches!(&ast[4], Ast::Function(..)));
    //    let expect_params: Vec<String> = vec![];
    //    assert_func!(&ast[4], "__anon_4", expect_params, Expr::Binary(..));

    //    let func = extract_var!(&ast[4], Ast::Function, x);
    //    let binary = extract_var!(&func.body, Expr::Binary, x, y, z);
    //    assert_expr!(
    //        &binary,
    //        BinaryOp::MoreThan,
    //        Expr::Variable(..),
    //        Expr::Number(..)
    //    );
    //}
}
