use crate::syntax::core::Term;
use crate::syntax::token::Position;
use chumsky::Span;
use codespan::{ColumnIndex, LineIndex};
use derive_more::{Add, AsRef, Deref, From};
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::{Add, Range};
use std::str::FromStr;

pub mod abs;
pub mod core;
pub mod desugar;
pub mod parser;
pub mod pattern;
pub mod surf;
pub mod token;

/// Plicitness (plɪsɪtnəs), noun - the quality of being explicit or implicit (Oxford dictionary (no)).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Plicitness {
    Explicit,
    Implicit,
}

#[derive(Clone, Copy, Eq, Default, Hash)]
pub struct Loc {
    pub start: usize,
    pub end: usize,
    pub line: LineIndex,
    pub col: ColumnIndex,
}

impl Debug for Loc {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "_")
    }
}

impl Span for Loc {
    type Context = ();
    type Offset = usize;

    fn new((): Self::Context, range: Range<Self::Offset>) -> Self {
        Self {
            start: range.start,
            end: range.end,
            line: LineIndex::from(0),
            col: ColumnIndex::from(0),
        }
    }
    fn context(&self) -> Self::Context {}
    fn start(&self) -> Self::Offset {
        self.start
    }
    fn end(&self) -> Self::Offset {
        self.end
    }
}

impl ariadne::Span for Loc {
    type SourceId = ();

    fn source(&self) -> &Self::SourceId {
        &()
    }
    fn start(&self) -> usize {
        self.start
    }
    fn end(&self) -> usize {
        self.end
    }
}

impl PartialEq for Loc {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl From<(Position, Position)> for Loc {
    fn from((s, e): (Position, Position)) -> Self {
        Self::new2(s, e)
    }
}

impl Loc {
    pub fn new(start: usize, end: usize) -> Self {
        Loc {
            start,
            end,
            line: LineIndex(0),
            col: ColumnIndex(0),
        }
    }

    pub fn new2(start: Position, end: Position) -> Self {
        Loc {
            start: start.abs,
            end: end.abs,
            line: start.line,
            col: start.col,
        }
    }
}

impl From<Range<usize>> for Loc {
    fn from(v: Range<usize>) -> Self {
        Loc::new(v.start, v.end)
    }
}

impl Add for Loc {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::Output {
            start: self.start,
            end: rhs.end,
            line: self.line,
            col: rhs.col,
        }
    }
}

impl Display for Loc {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}-{}", self.start, self.end)
    }
}

#[derive(Debug, Clone, Eq, Deref, AsRef, From, Hash)]
pub struct Ident {
    #[deref]
    #[as_ref]
    pub text: String,
    pub loc: Loc,
}

impl From<&'static str> for Ident {
    fn from(v: &'static str) -> Self {
        Ident {
            text: v.to_string(),
            loc: Loc::default(),
        }
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.text == other.text
    }
}

impl Ident {
    pub fn new(text: impl Into<String>, loc: impl Into<Loc>) -> Self {
        Ident {
            loc: loc.into(),
            text: text.into(),
        }
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.text)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Default, From, Add)]
pub struct Universe(pub u32);

impl Universe {
    pub fn max(self, u: Universe) -> Universe {
        Universe(self.0.max(u.0))
    }
}

impl Display for Universe {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.0 == u32::MAX {
            write!(f, "Type∞")
        } else {
            write!(f, "Type{}", self.0)
        }
    }
}

/// De Bruijn Indices. Checkout [Wikipedia](https://en.wikipedia.org/wiki/De_Bruijn_index) if you
/// are curious but have no idea about it.
pub type DBI = usize;

pub fn dbi_nat(dbi: DBI) -> Option<DBI> {
    if dbi == 0 {
        None
    } else {
        Some(dbi - 1)
    }
}

#[track_caller]
pub fn dbi_pred(dbi: DBI) -> DBI {
    dbi_nat(dbi).unwrap()
}

/// Unique identifiers for variables.
pub type UID = usize;
/// Global reference indices.
pub type GI = usize;
/// Meta indices.
pub type MI = usize;

/// Parameter information -- with type and visibility.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Bind<T> {
    pub licit: Plicitness,
    pub name: UID,
    pub ty: T,
    pub ident: Ident,
}

impl<T> Bind<T> {
    pub(crate) fn loc(&self) -> Loc {
        self.ident.loc
    }
}

impl<T> From<(UID, T)> for Bind<T> {
    fn from((name, ty): (UID, T)) -> Self {
        Bind {
            licit: Plicitness::Explicit,
            name,
            ty,
            ident: Ident::new(format!("{}", name), Loc::default()),
        }
    }
}

impl Display for Bind<Term> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.licit == Plicitness::Implicit {
            write!(f, "{{{}:{}}}", self.ident, self.ty)
        } else {
            write!(f, "{}:{}", self.ident, self.ty)
        }
    }
}

impl<T> Bind<T> {
    pub fn new(licit: Plicitness, name: UID, ty: T, _loc: Loc) -> Self {
        Self {
            licit,
            name,
            ty,
            ident: Ident::new(format!("{}", name), Loc::default()),
        }
    }

    pub fn identified(licit: Plicitness, name: UID, ty: T, ident: Ident) -> Self {
        Self {
            licit,
            name,
            ty,
            ident,
        }
    }

    pub fn is_implicit(&self) -> bool {
        self.licit == Plicitness::Implicit
    }

    pub fn into_implicit(mut self) -> Self {
        self.licit = Plicitness::Implicit;
        self
    }

    pub fn boxed(self) -> Bind<Box<T>> {
        self.map_term(|t| Box::new(t))
    }

    pub fn map_term<R>(self, f: impl FnOnce(T) -> R) -> Bind<R> {
        Bind::identified(self.licit, self.name, f(self.ty), self.ident)
    }

    pub fn ident(self) -> Ident {
        self.ident
    }
}

impl<T> Bind<Box<T>> {
    pub fn unboxed(self) -> Bind<T> {
        self.map_term(|t| *t)
    }
}

/// Let binding.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Let<T> {
    pub bind: Bind<T>,
    pub val: T,
}

impl<T> Let<T> {
    pub fn new(bind: Bind<T>, val: T) -> Self {
        Self { bind, val }
    }
}

/// Constructor information.
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.Syntax.Internal.html#ConHead).
#[derive(Debug, Eq, Clone)]
pub struct ConHead {
    /// Constructor name.
    pub name: Ident,
    /// Index of the constructor.
    pub cons_gi: GI,
}

impl PartialEq for ConHead {
    fn eq(&self, other: &Self) -> bool {
        self.cons_gi == other.cons_gi
    }
}

impl ConHead {
    pub fn pseudo(name: Ident) -> Self {
        Self::new(name, Default::default())
    }

    pub fn new(name: impl Into<Ident>, ix: GI) -> Self {
        Self {
            name: name.into(),
            cons_gi: ix,
        }
    }
}

#[macro_export]
macro_rules! uid_basic_operations_impl {
    ($name:ident) => {
        impl std::ops::Add<usize> for $name {
            type Output = $name;

            fn add(self, rhs: usize) -> Self::Output {
                Self(self.0 + rhs)
            }
        }

        impl std::ops::Sub<usize> for $name {
            type Output = $name;

            fn sub(self, rhs: usize) -> Self::Output {
                Self(self.0 - rhs)
            }
        }

        impl std::ops::Add<u32> for $name {
            type Output = $name;

            fn add(self, rhs: u32) -> Self::Output {
                self.add(rhs as usize)
            }
        }

        impl std::ops::Sub<u32> for $name {
            type Output = $name;

            fn sub(self, rhs: u32) -> Self::Output {
                self.sub(rhs as usize)
            }
        }

        impl std::ops::Add<i32> for $name {
            type Output = $name;

            fn add(self, rhs: i32) -> Self::Output {
                Self(((self.0 as i32) + rhs) as usize)
            }
        }

        impl std::ops::Sub<i32> for $name {
            type Output = $name;

            fn sub(self, rhs: i32) -> Self::Output {
                Self(((self.0 as i32) - rhs) as usize)
            }
        }

        impl std::ops::Add for $name {
            type Output = $name;

            fn add(self, rhs: $name) -> Self::Output {
                Self(self.0 + rhs.0)
            }
        }

        impl std::ops::AddAssign<usize> for $name {
            fn add_assign(&mut self, rhs: usize) {
                self.0 += rhs
            }
        }

        impl std::ops::Sub for $name {
            type Output = $name;

            fn sub(self, rhs: $name) -> Self::Output {
                Self(self.0 - rhs.0)
            }
        }

        impl std::ops::SubAssign<usize> for $name {
            fn sub_assign(&mut self, rhs: usize) {
                self.0 -= rhs
            }
        }

        impl std::ops::AddAssign for $name {
            fn add_assign(&mut self, rhs: $name) {
                self.0 += rhs.0
            }
        }

        impl std::ops::SubAssign for $name {
            fn sub_assign(&mut self, rhs: $name) {
                self.0 -= rhs.0
            }
        }

        impl $name {
            /// Successor.
            pub fn succ(mut self) -> Self {
                self.0 += 1;
                self
            }

            /// Predecessor.
            pub fn pred(self) -> Self {
                self.nat().unwrap()
            }

            /// Pattern matcher.
            pub fn nat(self) -> Option<Self> {
                if self.0 == 0 {
                    None
                } else {
                    Some(Self(self.0 - 1))
                }
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::result::Result<(), std::fmt::Error> {
                self.0.fmt(f)
            }
        }
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangItem {
    Nat,
    NatZ,
    NatS,
    List,
    Telescope,
    Id,
    Ap,
    CorrUp,
    CorrDown,
    Did,
    NatAdd,
    Pair,
}

impl FromStr for LangItem {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "nat" => Ok(Self::Nat),
            "list" => Ok(Self::List),
            "telescope" => Ok(Self::Telescope),
            "id" => Ok(Self::Id),
            "ap" => Ok(Self::Ap),
            "corr-up" => Ok(Self::CorrUp),
            "corr-down" => Ok(Self::CorrDown),
            "did" => Ok(Self::Did),
            "nat-add" => Ok(Self::NatAdd),
            "pair" => Ok(Self::Pair),
            _ => Err(()),
        }
    }
}

impl LangItem {
    pub fn skip_check(&self) -> bool {
        use LangItem::*;
        match self {
            Nat | NatZ | NatS | List => false,
            _ => true,
        }
    }
}
