use crate::syntax::core::{Tele, Term, TermInfo};
use crate::syntax::{Ident, Loc, Universe, GI};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ProjInfo {
    pub loc: Loc,
    pub name: Ident,
    pub codata: GI,
    pub ty: Term,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FuncInfo {
    pub loc: Loc,
    pub name: Ident,
    pub signature: Term,
    pub body: Term,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ConsInfo {
    pub loc: Loc,
    pub name: Ident,
    pub params: Tele,
    pub data: GI,
    pub signature: Term,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataInfo {
    pub loc: Loc,
    pub name: Ident,
    pub params: Tele,
    /// References to its constructors.
    pub conses: Vec<GI>,
    pub universe: Universe,
    pub signature: Term,
}

/// Declaration.
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Monad.Base.html#Function).
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl {
    /// Datatypes.
    Data(DataInfo),
    Cons(ConsInfo),
    Proj(ProjInfo),
    /// Function definitions.
    Func(FuncInfo),
}

impl Decl {
    pub(crate) fn ident(&self) -> Ident {
        match self {
            Decl::Data(d) => d.name.clone(),
            Decl::Cons(c) => c.name.clone(),
            Decl::Proj(p) => p.name.clone(),
            Decl::Func(f) => f.name.clone(),
        }
    }
}

impl Decl {
    pub fn def_name(&self) -> &Ident {
        match self {
            Decl::Proj(i) => &i.name,
            Decl::Data(i) => &i.name,
            Decl::Cons(i) => &i.name,
            Decl::Func(i) => &i.name,
        }
    }

    pub fn def_type(&self) -> Term {
        match self {
            Decl::Proj(i) => i.ty.clone(),
            Decl::Data(i) => i.signature.clone(),
            Decl::Cons(i) => i.signature.clone(),
            Decl::Func(i) => i.signature.clone(),
        }
    }

    #[allow(unused)]
    fn loc(&self) -> Loc {
        match self {
            Decl::Proj(i) => i.loc(),
            Decl::Data(i) => i.loc(),
            Decl::Cons(i) => i.loc(),
            Decl::Func(i) => i.loc(),
        }
    }
}

macro_rules! simple_to_loc {
    ($name:ident) => {
        impl $name {
            pub fn loc(&self) -> Loc {
                self.loc
            }
        }
    };
}

simple_to_loc!(DataInfo);
simple_to_loc!(ConsInfo);
simple_to_loc!(ProjInfo);
simple_to_loc!(TermInfo);
simple_to_loc!(FuncInfo);
