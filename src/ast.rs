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
pub enum Stmt {
    // "if" "(" condition ")" "then" expr ("else" expr)?
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
}

#[derive(Debug, PartialEq)]
pub enum StmtExpr {
    Expr(Expr),
    Stmt(Stmt),
}

#[derive(Debug, PartialEq)]
pub struct Function {
    pub prototype: Prototype,
    pub body: Vec<StmtExpr>,
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
