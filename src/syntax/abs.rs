use crate::syntax;
use crate::syntax::core::pretty_application;
use crate::syntax::{Ident, Loc, Plicitness, Universe, GI, MI, UID};
use std::fmt::{Display, Formatter};
use vec1::Vec1;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Param {
    pub name: Option<Ident>,
    pub ty: Option<Type>,
    pub plic: Plicitness,
}

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub struct NamedTele {
//     pub name: Ident,
//     pub tele: Vec<Param>,
//     pub ret_ty: Option<Type>,
// }

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Data {
    def: Tele,
    pub(crate) conses: Vec<GI>,
    universe: Option<Universe>,
    name: Ident,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataInfo {
    pub loc: Loc,
    pub name: Ident,
    pub uni: Option<Universe>,
    pub tele: Tele,
    pub conses: Vec<GI>,
}

impl DataInfo {
    pub fn new(loc: Loc, name: Ident, uni: Option<Universe>, tele: Tele, conses: Vec<GI>) -> Self {
        Self {
            loc,
            name,
            uni,
            tele,
            conses,
        }
    }

    pub fn ident(&self) -> &Ident {
        &self.name
    }
}

impl Display for DataInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Data {
    pub fn new(def: Tele, conses: Vec<GI>, universe: Option<Universe>, name: Ident) -> Self {
        Data {
            def,
            conses,
            universe,
            name,
        }
    }

    pub fn ident(&self) -> &Ident {
        &self.name
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Func {
    pub id: Ident,
    pub expr: Expr,
    pub(crate) ty: Option<Type>,
}

impl Func {
    pub fn new(id: Ident, expr: Expr, ty: Option<Expr>) -> Self {
        Func { id, expr, ty }
    }

    pub fn ident(&self) -> &Ident {
        &self.id
    }
}

impl Display for Func {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn {}", self.id)?;
        if let Some(ty) = &self.ty {
            write!(f, " : {}", ty)?;
        }
        write!(f, " := {}", self.expr)
    }
}

#[derive(Debug, Clone)]
pub struct LamParam {
    pub name: Ident,
    pub ty: Option<Expr>,
}

impl LamParam {
    pub fn new(name: Ident, ty: Option<Expr>) -> Self {
        LamParam { name, ty }
    }
}

pub type Bind<T = Option<Expr>> = syntax::Bind<T>;
pub type Tele = Vec<Bind>;
pub type Type = Expr;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Var(Ident, UID),
    Lam(Loc, Bind<Box<Option<Self>>>, Box<Self>),
    App(Box<Self>, Vec1<Self>),
    Pi(Loc, Bind<Box<Option<Self>>>, Box<Self>),
    Universe(Loc, Universe),
    Fn(Ident, GI),
    Def(Ident, GI),
    Cons(Ident, GI),
    Proj(Ident, GI),
    Meta(Ident, MI),
}

/// Application's internal view.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AppView {
    pub fun: Expr,
    pub args: Vec<Expr>,
}

impl AppView {
    pub fn new(fun: Expr, args: Vec<Expr>) -> Self {
        Self { fun, args }
    }

    pub fn into_abs(self) -> Expr {
        if self.args.is_empty() {
            self.fun
        } else {
            Expr::app(self.fun, Vec1::try_from_vec(self.args).unwrap())
        }
    }
}

impl Expr {
    pub fn into_app_view(self) -> AppView {
        match self {
            Self::App(f, arg) => {
                let mut view = f.into_app_view();
                view.args.append(&mut arg.into_vec());
                view
            }
            e => AppView::new(e, vec![]),
        }
    }

    pub fn into_tele_view(self) -> (Tele, Expr) {
        let mut expr = self;
        let mut tele = vec![];
        while let Self::Lam(_loc, bind, body) = expr {
            tele.push(bind.map_term(|x| *x));
            expr = *body;
        }
        (tele, expr)
    }

    pub fn loc(&self) -> Loc {
        use Expr::*;
        match self {
            App(f, a) => f.loc() + a.last().loc(),
            Lam(loc, _, _) | Pi(loc, _, _) | Universe(loc, _) => *loc,
            Proj(ident, ..)
            | Fn(ident, ..)
            | Var(ident, _)
            | Cons(ident, ..)
            | Def(ident, ..)
            | Meta(ident, ..) => ident.loc,
        }
    }

    pub fn app(f: Self, args: Vec1<Self>) -> Self {
        Expr::App(Box::new(f), args)
    }

    pub fn get_gi(&self) -> Option<GI> {
        use Expr::*;
        match self {
            Def(_ident, gi) => Some(*gi),
            Fn(_ident, gi) => Some(*gi),
            Cons(_ident, gi) => Some(*gi),
            Proj(_ident, gi) => Some(*gi),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ConsInfo {
    pub loc: Loc,
    pub name: Ident,
    pub tele: Tele,
    /// Corresponding datatype's index.
    pub data_ix: GI,
}

impl ConsInfo {
    pub(crate) fn ident(&self) -> &Ident {
        &self.name
    }

    pub fn new(loc: Loc, name: Ident, tele: Tele, data_ix: GI) -> Self {
        ConsInfo {
            loc,
            name,
            tele,
            data_ix,
        }
    }
}

impl Display for ConsInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Decl {
    Data(DataInfo),
    Fn(Func),
    Cons(ConsInfo),
}

impl Decl {
    pub fn ident(&self) -> &Ident {
        match self {
            Decl::Data(data) => data.ident(),
            Decl::Fn(f) => f.ident(),
            Decl::Cons(i) => i.ident(),
        }
    }
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Decl::Data(data) => write!(f, "{}", data),
            Decl::Fn(ff) => write!(f, "{}", ff),
            Decl::Cons(i) => write!(f, "{}", i),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Expr::*;
        match self {
            Var(ident, uid) => write!(f, "{}({})", uid, ident),
            Lam(_loc, bind, body) => {
                write!(f, "λ{}", bind.name)?;
                if let Some(ty) = &*bind.ty {
                    write!(f, ":{}", ty)?;
                }
                write!(f, ". {}", body)
            }
            App(ff, args) => pretty_application(f, ff, args),
            Pi(_loc, bind, body) => {
                write!(f, "Π{}", bind.name)?;
                if let Some(ty) = &*bind.ty {
                    write!(f, ":{}", ty)?;
                }
                write!(f, ", {}", body)
            }
            Universe(_loc, universe) => write!(f, "{}", universe),
            Fn(ident, _) => write!(f, "{}", ident),
            Def(ident, _) => write!(f, "{}", ident),
            Cons(ident, _) => write!(f, "{}", ident),
            Proj(ident, _) => write!(f, "{}", ident),
            Meta(ident, _) => write!(f, "?{}", ident),
        }
    }
}
