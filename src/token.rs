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
}

impl<'a> Display for Token<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Universe(n) => write!(f, "Type{}", n),
            Token::Pi => f.write_str("forall"),
            Token::Sigma => f.write_str("exists"),
            Token::Ident(s) => f.write_str(s),
            Token::Data => f.write_str("data"),
            Token::Codata => f.write_str("codata"),
            Token::At => f.write_str("@"),
            Token::Colon => f.write_str(":"),
            Token::Comma => f.write_str(","),
            Token::Dot => f.write_str("."),
            Token::DArrow => f.write_str("=>"),
            Token::Lam => f.write_str("lam"),
            Token::Let => f.write_str("let"),
            Token::Pipe => f.write_str("|"),
            Token::RArrow => f.write_str("->"),
            Token::LBrace => f.write_str("{"),
            Token::RBrace => f.write_str("}"),
            Token::LBracket => f.write_str("["),
            Token::RBracket => f.write_str("]"),
            Token::LParen => f.write_str("("),
            Token::RParen => f.write_str(")"),
            Token::Whitespace => f.write_str(" "),
        }
    }
}
