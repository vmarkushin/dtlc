use chumsky::Span;
pub use codespan::{
    ByteIndex, ByteIndex as BytePos, ByteOffset, ColumnIndex as Column, ColumnOffset,
    LineIndex as Line, LineOffset, RawIndex,
};
use std::fmt::{Display, Formatter};
use std::ops::Range;

struct Foo;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Token<'input> {
    Universe(String),
    Pi,
    Ident(String),
    Data,
    Codata,
    Match,
    At,
    Hash,
    Colon,
    Comma,
    Dot,
    DArrow,
    Lam,
    Fn,
    Let,
    Pipe,
    RArrow,
    Underscore,
    Bang,
    Question,
    MetaIdent(String),
    Nat(String),
    Str(String),
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    LParen,
    RParen,
    Assignment,
    Whitespace,
    Comment,
    // Will be used as a lifetime of the input later
    __Unused(&'input ()),
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Position {
    pub abs: usize,
    pub line: Line,
    pub col: Column,
}

impl<L: Into<Line>, C: Into<Column>> From<(usize, L, C)> for Position {
    fn from((p, l, c): (usize, L, C)) -> Self {
        Position::new(p, l.into(), c.into())
    }
}

impl Position {
    pub fn new(abs: usize, line: impl Into<Line>, col: impl Into<Column>) -> Self {
        Self {
            abs,
            line: line.into(),
            col: col.into(),
        }
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

impl Span for Position {
    type Context = ();
    type Offset = usize;

    fn new((): Self::Context, range: Range<usize>) -> Self {
        Self {
            abs: range.start,
            line: Default::default(),
            col: Default::default(),
        }
    }
    fn context(&self) -> Self::Context {}
    fn start(&self) -> Self::Offset {
        self.abs.clone()
    }
    fn end(&self) -> Self::Offset {
        self.abs.clone()
    }
}

impl<'a> Display for Token<'a> {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Token::*;

        match self {
            Universe(n)         => write!(f, "Type{}", n),
            Ident(s)            => f.write_str(s),
            Pi                  => f.write_str("forall"),
            Data                => f.write_str("data"),
            Codata              => f.write_str("codata"),
            Match               => f.write_str("match"),
            At                  => f.write_str("@"),
            Hash                => f.write_str("#"),
            Colon               => f.write_str(":"),
            Assignment          => f.write_str(":="),
            Comma               => f.write_str(","),
            Dot                 => f.write_str("."),
            DArrow              => f.write_str("=>"),
            Lam                 => f.write_str("lam"),
            Fn                  => f.write_str("fn"),
            Let                 => f.write_str("let"),
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
            MetaIdent(s)        => f.write_str(s),
            Bang                => f.write_str("!"),
            Question            => f.write_str("?"),
            Comment             => Ok(()),
            Nat(n)              => write!(f, "{}", n),
            Str(s)              => f.write_str(s),
            __Unused(_) => {unreachable!()}
        }
    }
}
