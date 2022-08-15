use crate::syntax;
use crate::syntax::core::pretty_application;
use crate::syntax::{pattern, Ident, Loc, Plicitness, Universe, GI, MI, UID};
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use vec1::Vec1;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Param {
    pub name: Option<Ident>,
    pub ty: Option<Type>,
    pub plic: Plicitness,
}

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
    /// May be `None` if not fully desugared.
    pub expr: Option<Expr>,
    pub(crate) ty: Option<Type>,
}

impl Func {
    pub fn new(id: Ident, expr: Option<Expr>, ty: Option<Expr>) -> Self {
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
        if let Some(body) = &self.expr {
            write!(f, " := {}", body)
        } else {
            write!(f, " := <unknown>")
        }
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
pub type Pat<T = Expr> = pattern::Pat<UID, T>;

impl Case {
    pub fn subst_abs(&mut self, subst: Rc<HashMap<UID, Expr>>) {
        self.body
            .as_mut()
            .iter_mut()
            .for_each(|x| x.subst_abs(subst.clone()));
        self.tele.iter_mut().for_each(|b| {
            b.ty.iter_mut().for_each(|x| x.subst_abs(subst.clone()));
            if let Some(Expr::Var(_, uid)) = subst.get(&b.name) {
                b.name = *uid;
            }
        });
    }
}

impl Expr {
    pub fn subst_abs(&mut self, subst: Rc<HashMap<UID, Expr>>) {
        match self {
            Expr::Var(_, x) => {
                if let Some(x) = subst.get(x).cloned() {
                    *self = x;
                }
            }
            Expr::Lam(_, b, t) => {
                b.ty.iter_mut().for_each(|x| x.subst_abs(subst.clone()));
                if let Some(Expr::Var(_, uid)) = subst.get(&b.name) {
                    b.name = *uid;
                }
                t.subst_abs(subst);
            }
            Expr::App(a, b) => {
                a.subst_abs(subst.clone());
                b.iter_mut().for_each(|x| x.subst_abs(subst.clone()));
            }
            Expr::Pi(_, b, r) => {
                b.ty.iter_mut().for_each(|x| x.subst_abs(subst.clone()));
                if let Some(Expr::Var(_, uid)) = subst.get(&b.name) {
                    b.name = *uid;
                }
                r.subst_abs(subst);
            }
            Expr::Universe(_, _) => {}
            Expr::Fn(_, _) => {}
            Expr::Def(_, _) => {}
            Expr::Cons(_, _) => {}
            Expr::Proj(_, _) => {}
            Expr::Meta(_, _) => {}
            Expr::Match(Match { xs, cases: cs }) => {
                xs.iter_mut().for_each(|x| x.subst_abs(subst.clone()));
                cs.iter_mut().for_each(|x| x.subst_abs(subst.clone()));
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Case {
    /// Δ. The types of the pattern variables in dependency order.
    pub tele: Tele,
    /// Δ ⊢ ps. The de Bruijn indices refer to Δ.
    pub patterns: Vec<Pat>,
    /// `Some(v)` if `Δ ⊢ v`, while `None` if the pattern is absurd.
    pub body: Option<Expr>,
}

impl Case {
    pub fn new(tele: Tele, patterns: Vec<Pat>, body: Option<Expr>) -> Self {
        Self {
            tele,
            patterns,
            body,
        }
    }
}

impl Display for Case {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "  | {}", self.patterns.iter().join(", "))?;
        if let Some(body) = &self.body {
            writeln!(f, " => {}", body)
        } else {
            writeln!(f)
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Match {
    pub xs: Vec1<Expr>,
    pub cases: Vec<Case>,
}

impl Match {
    pub fn loc(&self) -> Loc {
        self.xs.last().loc()
    }

    pub fn new(xs: Vec1<Expr>, cases: Vec<Case>) -> Self {
        Self { xs, cases }
    }
}

impl Display for Match {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "match {} {{ {} }}",
            self.xs.iter().join(", "),
            self.cases.iter().join("")
        )
    }
}

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
    Match(Match),
}

impl Expr {
    pub(crate) fn lam_tele(tele: Tele, body: Expr) -> Expr {
        tele.into_iter()
            .rfold(body, |expr, param| Self::lam(param.boxed(), box expr))
    }
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
            Match(m) => m.loc(),
        }
    }

    pub fn app(f: Self, args: Vec1<Self>) -> Self {
        Expr::App(Box::new(f), args)
    }

    pub fn lam(param: Bind<Box<Option<Self>>>, body: Box<Self>) -> Self {
        Expr::Lam(Loc::default(), param, body)
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
    pub(crate) fn as_func_mut(&mut self) -> &mut Func {
        match self {
            Decl::Fn(f) => f,
            _ => panic!("not a function"),
        }
    }

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
            Match(m) => {
                write!(f, "{}", m)
            }
        }
    }
}
