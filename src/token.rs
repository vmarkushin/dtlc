use logos::Logos;
use std::fmt::{Display, Formatter};

#[derive(Clone, Debug, Logos, PartialEq, Eq)]
pub enum Token<'input> {
    #[regex("Type[0-9]*")]
    Universe(&'input str),
    #[token("forall")]
    #[token("Π")]
    Pi,
    #[token("exists")]
    #[token("Σ")]
    Sigma,
    #[regex("[a-zA-Z_][a-zA-Z0-9_']*")]
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
    #[token("fn")]
    Let,
    #[token("|")]
    Pipe,
    #[token("->")]
    #[token("→")]
    RArrow,
    #[token("_")]
    Underscore,
    #[regex("\\?[a-zA-Z0-9_]+")]
    MetaIdent(&'input str),
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
    #[token(":=")]
    Assignment,

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Whitespace,
}

impl<'a> Display for Token<'a> {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Token::*;

        match self {
            Universe(n)  => write!(f, "Type{}", n),
            Ident(s)     => f.write_str(s),
            Pi                  => f.write_str("forall"),
            Sigma               => f.write_str("exists"),
            Data                => f.write_str("data"),
            Codata              => f.write_str("codata"),
            At                  => f.write_str("@"),
            Colon               => f.write_str(":"),
            Assignment          => f.write_str(":="),
            Comma               => f.write_str(","),
            Dot                 => f.write_str("."),
            DArrow              => f.write_str("=>"),
            Lam                 => f.write_str("lam"),
            Let                 => f.write_str("fn"),
            Pipe                => f.write_str("|"),
            RArrow              => f.write_str("->"),
            LBrace              => f.write_str("{"),
            RBrace              => f.write_str("}"),
            LBracket            => f.write_str("["),
            RBracket            => f.write_str("]"),
            LParen              => f.write_str("("),
            RParen              => f.write_str(")"),
            Whitespace          => f.write_str(" "),
            Underscore          => f.write_str("_"),
            MetaIdent(s) => f.write_str(s),
        }
    }
}
