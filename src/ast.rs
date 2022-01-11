#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum BinaryOp {
    Eq,       // ==
    Ne,       // !=
    LessThan, // <
    MoreThan, // >
    Plus,     // +
    Minus,    // -
    Multiply, // *
    Divide,   // /
}

#[derive(Debug, PartialEq)]
pub enum StmtExpr {
    Binary(BinaryOp, Box<StmtExpr>, Box<StmtExpr>),
    Call(String, Vec<StmtExpr>),
    Number(f64),
    Variable(String),
    Assign(String, Box<StmtExpr>),
    // "if" condition "{" Vec<expr> "}" ("else" "{" Vec<expr> "}")?
    If(Box<StmtExpr>, Vec<StmtExpr>, Vec<StmtExpr>),
    // "while" "condition" "{" Vec<expr> "}"
    While(Box<StmtExpr>, Vec<StmtExpr>),
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
