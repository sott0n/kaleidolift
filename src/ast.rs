#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum BinaryOp {
    LessThan,
    MoreThan,
    Plus,
    Minus,
    Multiply,
    Divide,
}

#[derive(Debug, PartialEq)]
pub enum Expr {
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    Call(String, Vec<Expr>),
    Number(f64),
    Variable(String),
}

#[derive(Debug, PartialEq)]
pub struct Function {
    pub prototype: Prototype,
    pub body: Expr,
}

#[derive(Debug, PartialEq)]
pub struct Prototype {
    pub function_name: String,
    pub parameters: Vec<String>,
}

#[derive(Debug, PartialEq)]
pub enum Ast {
    Function(Function),
    Prototype(Prototype),
}