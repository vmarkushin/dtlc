use crate::check::TypeCheckState;
use crate::syntax::core::redex::Subst;
use crate::syntax::core::subst::Substitution;
use crate::syntax::core::{DeBruijn, SubstWith, Tele};
use crate::syntax::pattern;
use crate::syntax::{ConHead, Ident, Loc, Plicitness, Universe, DBI, GI, MI, UID};
use derive_more::From;
use itertools::Either;
use itertools::Either::*;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub type Pat<Ix = DBI, T = Term> = pattern::Pat<Ix, T>;

impl DeBruijn for Pat {
    fn dbi_view(&self) -> Option<DBI> {
        match self {
            Pat::Var(dbi) => Some(*dbi),
            _ => None,
        }
    }

    fn from_dbi(dbi: DBI) -> Self {
        Pat::Var(dbi)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ValData {
    pub def: GI,
    pub args: Vec<Term>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Lambda(pub Bind<Box<Term>>, pub Closure);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Var {
    Bound(DBI),
    Free(UID),
}

/// Weak-head-normal-form terms, canonical values.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Val {
    /// Type universe.
    Universe(Universe),
    /// (Co)Data types, fully applied.
    Data(ValData),
    /// Pi-like types (dependent types), with parameter explicitly typed.
    /// Pi Bind, Closure.
    Pi(Bind<Box<Term>>, Closure),
    /// Lambda.
    Lam(Lambda),
    /// Constructor invocation, fully applied.
    Cons(ConHead, Vec<Term>),
    /// Meta reference, with eliminations.
    /// This does not appear in Cockx18, but we can find it in the
    /// [implementation](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/Agda-Syntax-Internal.html#v:MetaV).
    Meta(MI, Vec<Elim>),
    /// Variable elimination, in spine-normal form.
    /// (so we have easy access to application arguments).<br/>
    /// This is convenient for meta resolution and termination check.
    Var(Var, Vec<Elim>),
}

impl Val {
    pub(crate) fn is_cons(&self) -> bool {
        matches!(self, Val::Cons(..))
    }

    #[allow(unused)]
    pub(crate) fn into_pi(self) -> Either<Val, (Bind<Box<Term>>, Closure)> {
        match self {
            Val::Pi(b, c) => Right((b, c)),
            v => Left(v),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Func {
    Index(GI),
    Lam(Lambda),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Case {
    pub pattern: Pat,
    pub body: Term,
}

impl Display for Case {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "  | {} => {}", self.pattern, self.body)
    }
}

impl Case {
    pub fn new(pattern: Pat, body: Term) -> Self {
        Self { pattern, body }
    }
}

/// Type for terms.
#[derive(Debug, PartialEq, Eq, Clone, From)]
pub enum Term {
    Whnf(Val),
    Redex(Func, Ident, Vec<Elim>),
    /// Data elimination.
    Match(Box<Term>, Vec<Case>),
}

pub trait TryIntoPat<Ix, T> {
    fn try_into_pat(self) -> Option<Pat<Ix, T>>;
}

impl<Ix: From<DBI>, T: Subst<Term>> TryIntoPat<Ix, T> for Term {
    fn try_into_pat(self) -> Option<Pat<Ix, T>> {
        match self {
            Term::Whnf(Val::Cons(con_head, params)) => Some(Pat::cons(
                con_head,
                params
                    .into_iter()
                    .map(Term::try_into_pat)
                    .collect::<Option<Vec<_>>>()?,
            )),
            Term::Whnf(Val::Var(Var::Bound(ix), _)) => Some(Pat::Var(Ix::from(ix))),
            _ => None,
        }
    }
}

impl Pat {
    pub fn into_term(self) -> Term {
        match self {
            Pat::Var(v) => Term::from_dbi(v),
            Pat::Wildcard => panic!(),
            Pat::Absurd => {
                panic!()
            }
            Pat::Cons(_, head, args) => {
                let args = args.into_iter().map(Pat::into_term).collect::<Vec<_>>();
                Term::cons(head, args)
            }
            Pat::Forced(t) => t,
        }
    }
}

impl From<DBI> for Term {
    fn from(dbi: DBI) -> Self {
        Term::from_dbi(dbi)
    }
}

pub trait BoundFreeVars {
    fn bound_free_vars(&mut self, vars: &HashMap<UID, DBI>, depth: usize);
}

impl<T: BoundFreeVars> BoundFreeVars for Vec<T> {
    fn bound_free_vars(&mut self, vars: &HashMap<UID, DBI>, depth: usize) {
        for t in self {
            t.bound_free_vars(vars, depth);
        }
    }
}

impl BoundFreeVars for Elim {
    fn bound_free_vars(&mut self, vars: &HashMap<UID, DBI>, depth: usize) {
        match self {
            Elim::App(a) => {
                a.bound_free_vars(vars, depth);
            }
            Elim::Proj(_) => {}
        }
    }
}

impl BoundFreeVars for Closure {
    fn bound_free_vars(&mut self, vars: &HashMap<UID, DBI>, depth: usize) {
        let Closure::Plain(p) = self;
        p.bound_free_vars(vars, depth + 1);
    }
}

impl BoundFreeVars for Term {
    fn bound_free_vars(&mut self, vars: &HashMap<UID, DBI>, depth: usize) {
        match self {
            Term::Whnf(Val::Var(var, args)) => {
                args.bound_free_vars(vars, depth);
                let uid = if let Var::Free(uid) = var {
                    *uid
                } else {
                    return;
                };
                if let Some(ix) = vars.get(&uid) {
                    let new_dbi = *ix + depth;
                    debug!("bound {} := {}", uid, new_dbi);
                    *var = Var::Bound(new_dbi);
                }
            }
            Term::Redex(Func::Lam(lam), _, args) => {
                lam.0.ty.bound_free_vars(vars, depth);
                lam.1.bound_free_vars(vars, depth);
                args.bound_free_vars(vars, depth);
            }
            Term::Redex(Func::Index(_), _, args) => {
                args.bound_free_vars(vars, depth);
            }
            Term::Match(t, cases) => {
                t.bound_free_vars(vars, depth);
                for case in cases {
                    let len = case.pattern.vars().len();
                    if len == 0 {
                        case.body.bound_free_vars(vars, depth);
                    } else {
                        let min = *case.pattern.vars().last().unwrap();
                        let vars_new = vars
                            .clone()
                            .into_iter()
                            .map(|(k, v)| if k >= min { (k, v + len) } else { (k, v) })
                            .collect();
                        case.body.bound_free_vars(&vars_new, depth);
                    }
                }
            }
            Term::Whnf(Val::Universe(_)) => {}
            Term::Whnf(Val::Data(data)) => {
                data.args.bound_free_vars(vars, depth);
            }
            Term::Whnf(Val::Pi(x, ret)) => {
                x.ty.bound_free_vars(vars, depth);
                ret.bound_free_vars(vars, depth);
            }
            Term::Whnf(Val::Lam(lam)) => {
                lam.0.ty.bound_free_vars(vars, depth);
                lam.1.bound_free_vars(vars, depth);
            }
            Term::Whnf(Val::Cons(_, args)) => {
                args.bound_free_vars(vars, depth);
            }
            Term::Whnf(Val::Meta(_, args)) => {
                args.bound_free_vars(vars, depth);
            }
        }
    }
}

impl Term {
    pub fn free_var(uid: UID) -> Self {
        Term::Whnf(Val::Var(Var::Free(uid), Vec::new()))
    }

    pub(crate) fn is_cons(&self) -> bool {
        matches!(self, Term::Whnf(Val::Cons(..)))
    }

    pub(crate) fn is_eta_var(&self) -> bool {
        matches!(self, Term::Whnf(Val::Var(_, es)) if es.is_empty())
    }

    #[allow(unused)]
    pub(crate) fn tele_len(&self) -> usize {
        match self {
            Self::Whnf(v) => match v {
                Val::Pi(_, Closure::Plain(t)) => t.tele_len() + 1,
                _ => 0,
            },
            Self::Redex(..) => 0,
            Self::Match(..) => 0,
        }
    }

    pub(crate) fn lam(p0: Bind<Box<Term>>, p1: Term) -> Term {
        Term::Whnf(Val::Lam(Lambda(p0, Closure::Plain(box p1))))
    }

    pub fn match_case(t: impl Into<Box<Term>>, cs: impl Into<Vec<Case>>) -> Self {
        Term::Match(t.into(), cs.into())
    }

    pub fn match_elim(x: DBI, cs: impl Into<Vec<Case>>) -> Self {
        Self::match_case(box Term::from_dbi(x), cs)
    }

    pub fn is_meta(&self) -> bool {
        matches!(self, Term::Whnf(Val::Meta(_, _)))
    }

    pub fn as_meta(&self) -> Option<(MI, &Vec<Elim>)> {
        match self {
            Term::Whnf(Val::Meta(i, elims)) => Some((*i, elims)),
            _ => None,
        }
    }

    pub fn fun_app(gi: GI, name: impl Into<Ident>, args: impl IntoIterator<Item = Term>) -> Term {
        Term::Redex(
            Func::Index(gi),
            name.into(),
            args.into_iter().map(Elim::from).collect(),
        )
    }
}

pub type Bind<T = Term> = super::super::Bind<T>;

/// Type for eliminations.
#[derive(Debug, PartialEq, Eq, Clone, From)]
pub enum Elim {
    #[from(forward)]
    App(Box<Term>),
    Proj(String),
}

/// A closure with open terms.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Closure {
    Plain(Box<Term>),
}

impl Closure {
    pub fn instantiate(self, arg: Term) -> Term {
        self.instantiate_safe(arg)
            .unwrap_or_else(|e| panic!("Cannot split on `{}`.", e))
    }

    pub fn instantiate_safe(self, arg: Term) -> Result<Term, Term> {
        let Closure::Plain(body) = self;
        Ok(body.subst(Substitution::one(arg)))
    }

    pub fn instantiate_with(self, arg: Term, tcs: &mut TypeCheckState) -> Term {
        self.instantiate_safe_with(arg, tcs)
            .unwrap_or_else(|e| panic!("Cannot split on `{}`.", e))
    }

    pub fn instantiate_safe_with(self, arg: Term, tcs: &mut TypeCheckState) -> Result<Term, Term> {
        let Closure::Plain(body) = self;
        Ok(body.subst_with(Substitution::one(arg), tcs))
    }
}

impl ValData {
    pub fn new(def: GI, args: Vec<Term>) -> Self {
        Self { def, args }
    }
}

impl Val {
    pub fn inductive(ix: GI, params: Vec<Term>) -> Self {
        Val::Data(ValData::new(ix, params))
    }
}

/// Constructors and traversal functions.
impl Term {
    pub fn is_type(&self) -> bool {
        use Val::*;
        match match self {
            Term::Whnf(val) => val,
            Term::Redex(..) => return false,
            Term::Match(..) => return false,
        } {
            Pi(..) | Data(..) | Universe(..) => true,
            Var(..) | Meta(..) | Cons(..) | Lam(..) => false,
        }
    }

    pub fn is_universe(&self) -> bool {
        matches!(self, Term::Whnf(Val::Universe(..)))
    }

    pub fn cons(name: ConHead, params: Vec<Self>) -> Self {
        Term::Whnf(Val::Cons(name, params))
    }

    pub fn data(info: ValData) -> Self {
        Term::Whnf(Val::Data(info))
    }

    pub fn meta(index: MI, params: Vec<Elim>) -> Self {
        Term::Whnf(Val::Meta(index, params))
    }

    pub fn universe(uni: Universe) -> Self {
        Term::Whnf(Val::Universe(uni))
    }

    pub fn def(gi: GI, ident: Ident, elims: Vec<Elim>) -> Self {
        Term::Redex(Func::Index(gi), ident, elims)
    }

    pub fn simple_def(gi: GI, ident: Ident) -> Self {
        Self::def(gi, ident, vec![])
    }

    pub fn pi_from_tele(tele: Tele, ret: Self) -> Self {
        tele.into_iter().rfold(ret, |ret, param| {
            Self::pi2(param.boxed(), Closure::plain(ret))
        })
    }

    /// # Returns
    ///
    /// The telescope and the return type.
    pub fn tele_view(self) -> (Tele, Self) {
        self.tele_view_n(usize::MAX)
    }

    /// Returns telescope with _at most_ `n` members.
    pub fn tele_view_n(self, n: usize) -> (Tele, Self) {
        match self {
            Term::Whnf(Val::Pi(bind, Closure::Plain(r))) if n != 0 => {
                let (mut view, r) = r.tele_view_n(n - 1);
                view.push(bind.unboxed());
                (view, r)
            }
            Term::Whnf(Val::Lam(Lambda(bind, Closure::Plain(r)))) if n != 0 => {
                let (mut view, r) = r.tele_view_n(n - 1);
                view.push(bind.unboxed());
                (view, r)
            }
            // The capacity is an arbitrarily estimated value.
            e => (Tele(Vec::with_capacity(2)), e),
        }
    }

    pub fn pi(licit: Plicitness, name: UID, param_type: Term, body: Closure, loc: Loc) -> Self {
        Self::pi2(Bind::boxing(licit, name, param_type, loc), body)
    }

    pub fn pi2(param: Bind<Box<Term>>, body: Closure) -> Self {
        Term::Whnf(Val::Pi(param, body))
    }
}

impl Closure {
    pub fn plain(body: Term) -> Self {
        Closure::Plain(Box::new(body))
    }
}

impl Elim {
    pub fn app(term: Term) -> Self {
        Elim::App(Box::new(term))
    }

    pub fn is_proj(&self) -> bool {
        match self {
            Elim::App(..) => false,
            Elim::Proj(..) => true,
        }
    }

    pub fn into_app(self) -> Term {
        self.try_into_app().unwrap()
    }

    pub fn try_into_app(self) -> Result<Term, String> {
        match self {
            Elim::App(term) => Ok(*term),
            Elim::Proj(field) => Err(field),
        }
    }
}
