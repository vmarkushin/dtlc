use logos::Logos;
use std::fmt::{Display, Formatter};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Logos)]
pub enum Token<'input> {
    #[regex("Type[0-9]*")]
    Universe(&'input str),
    #[token("forall")]
    #[token("Π")]
    Pi,
    #[token("exists")]
    #[token("Σ")]
    Sigma,
    #[regex("[a-zA-Z][a-zA-Z0-9]*")]
    Ident(&'input str),
    #[token("data")]
    Data,
    #[token("codata")]
    Codata,
    #[token("@")]
    At,
    #[token(":")]
    Colon,
    #[token(",")]
    Comma,
    #[token(".")]
    Dot,
    #[token("=>")]
    DArrow,
    #[token("lam")]
    #[token("λ")]
    Lam,
    #[token("let")]
    Let,
    #[token("|")]
    Pipe,
    #[token("->")]
    #[token("→")]
    RArrow,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Whitespace,
    // #[regex(r"[ \t\n\f]+")]
    // Error,
}

impl<'a> Display for Token<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("{:?}", self))
    }
}
