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
    // #[regex("Type[0-9]*")]
    Universe(String),
    // #[token("forall")]
    // #[token("Π")]
    Pi,
    // #[token("exists")]
    // #[token("Σ")]
    // Sigma,
    // #[regex("[~!@#$%^&*\\-+=<>?/|:a-zA-Z_∀-⋿Ͱ-Ͽ←-⇿'0-9]*")]
    Ident(String),
    // Ident(String),
    // #[token("data")]
    Data,
    // #[token("codata")]
    Codata,
    // #[token("match")]
    Match,
    // #[token("@")]
    At,
    // #[token("#")]
    Hash,
    // #[token(":")]
    Colon,
    // #[token(",")]
    Comma,
    // #[token(".")]
    Dot,
    // #[token("=>")]
    DArrow,
    // #[token("lam")]
    // #[token("λ")]
    Lam,
    // #[token("fn")]
    Fn,
    // #[token("let")]
    Let,
    // #[token("|")]
    Pipe,
    // #[token("->")]
    // #[token("→")]
    RArrow,
    // #[token("_")]
    Underscore,
    // #[token("!")]
    Bang,
    // #[token("?")]
    Question,
    // #[regex("\\?[a-zA-Z0-9_-]+")]
    MetaIdent(String),
    // #[regex("[0-9]+")]
    Nat(String),
    // #[regex("\"[a-zA-Z0-9_-]*\"")]
    Str(String),
    // #[token("{")]
    LBrace,
    // #[token("}")]
    RBrace,
    // #[token("[")]
    LBracket,
    // #[token("]")]
    RBracket,
    // #[token("(")]
    LParen,
    // #[token(")")]
    RParen,
    // #[token(":=")]
    Assignment,
    // #[token("=")]
    // MetaAssignment,
    // #[error]
    // #[regex(r"[ \t\n\f]+", logos::skip)]
    Whitespace,
    // #[regex(r"--.*", logos::skip)]
    Comment,
    // #[regex(r"\{-(.|\n)*-\}", logos::skip)]
    // BlockComment,
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

pub struct SpannedIter<'source> {
    //    lexer: Lexer<'source, Token<'source>>,
    _phantom: std::marker::PhantomData<&'source ()>,
    line: Line,
    col: Column,
    last_pos: usize,
}

// impl<'source> Iterator for SpannedIter<'source> {
//     type Item = (Position, Token<'source>, Position);
//
//     fn next(&mut self) -> Option<Self::Item> {
//         self.lexer.next().map(|token| {
//             let range = self.lexer.span();
//             if self.last_pos < range.start {
//                 let raw = &self.lexer.source()[(self.last_pos + 1)..range.start];
//                 for ch in raw.chars() {
//                     if ch == '\n' {
//                         self.line += LineOffset(1);
//                         self.col = Column(1);
//                     } else {
//                         self.col += ColumnOffset(1);
//                     }
//                 }
//                 if self.col == Column(0) {
//                     self.col = Column(1);
//                 }
//             }
//
//             let line_start = self.line;
//             let col_start = self.col;
//
//             let raw = &self.lexer.source()[range.start..range.end];
//             for ch in raw.chars() {
//                 if ch == '\n' {
//                     self.line += LineOffset(1);
//                     self.col = Column(1);
//                 } else {
//                     self.col += ColumnOffset(1);
//                 }
//             }
//             if self.col == Column(0) {
//                 self.col = Column(1);
//             }
//
//             let line_end = self.line;
//             let col_end = self.col;
//
//             self.last_pos = range.end - 1;
//
//             (
//                 Position::new(range.start, line_start, col_start),
//                 token,
//                 Position::new(range.end, line_end, col_end),
//             )
//         })
//     }
// }

// pub fn lexer(input: &str) -> SpannedIter {
//     todo!()
//     //     SpannedIter {
//     //         lexer: Token::lexer(input),
//     //         line: Line(1),
//     //         col: Column(1),
//     //         last_pos: 0,
//     //     }
// }

impl<'a> Display for Token<'a> {
    #[rustfmt::skip]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Token::*;

        match self {
            Universe(n)         => write!(f, "Type{}", n),
            Ident(s)            => f.write_str(s),
            Pi                  => f.write_str("forall"),
            // Sigma               => f.write_str("exists"),
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
            // MetaAssignment      => f.write_str("="),
            Str(s)              => f.write_str(s),
            // BlockComment        => Ok(()),
            __Unused(_) => {unreachable!()}
        }
    }
}
