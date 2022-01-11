#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum BinaryOp {
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
    // "if" "(" condition ")" "then" expr ("else" expr)?
    If(Box<StmtExpr>, Vec<StmtExpr>, Vec<StmtExpr>),
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
