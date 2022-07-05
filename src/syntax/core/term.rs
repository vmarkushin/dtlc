use crate::check::TypeCheckState;
use crate::syntax::core::redex::Subst;
use crate::syntax::core::subst::Substitution;
use crate::syntax::core::{DeBruijn, FoldVal, SubstWith, Tele};
use crate::syntax::pattern;
use crate::syntax::{ConHead, Ident, Loc, Plicitness, Universe, DBI, GI, MI, UID};
use derive_more::From;
use itertools::Either::*;
use itertools::{Either, Itertools};
use std::fmt::{Display, Formatter};
use std::rc::Rc;

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
    Var(DBI, Vec<Elim>),
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

impl SubstWith<'_> for Case {
    fn subst_with(mut self, subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Self {
        let old_pat_vars = self.pattern.vars();
        self.pattern = self.pattern.subst_with(subst.clone(), tcs);
        let pat_vars = self.pattern.vars();
        // self.body = self.body.subst(subst.clone());

        debug!("Substituting in case {} with {}", self, subst);
        let new_subst = if let Some(s) = pat_vars.iter().sum1::<DBI>() {
            let min = *pat_vars.last().unwrap();
            let max = *pat_vars.first().unwrap();
            if min != max {
                let n = max - min;
                debug_assert_eq!(s, n * (n + 1) / 2);
            }
            let _split_var = *old_pat_vars.last().unwrap();
            // let (subst1, subst2) = subst.clone().split(split_var);
            // let subst = subst1.drop_by(1).union(subst2);

            let split_var = min;
            let (subst1, subst2) = subst.clone().split(split_var);
            debug!(
                "split substitution (by {}): {} ⊎ {} = {}",
                split_var, subst1, subst2, subst
            );

            let len = pat_vars.len();
            // let subst2_lifted = subst2.clone().lift_by(len);
            let subst1_lifted = subst1.clone().lift_by(len - 1);
            // let new_subst = subst1.clone().union(subst2_lifted.clone());
            let new_subst = subst1_lifted.clone().union(subst2.clone());
            // debug!(
            //     "unify substitution: {} = {} ⊎ {} = lift({}, {}) ⊎ {}",
            //     new_subst, subst1_lifted, subst2, subst1, len, subst2,
            // );
            debug!("unify substitution: {}", new_subst);
            new_subst
        } else {
            subst
            // subst.drop_by(1)
        };
        self.body = self.body.subst_with(new_subst.clone(), tcs);
        self
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
            Term::Whnf(Val::Var(ix, _)) => Some(Pat::Var(Ix::from(ix))),
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

impl Term {
    pub(crate) fn fresh_mi(&self) -> MI {
        self.try_fold_val::<!, _>(0, |max_mi, val| {
            Ok(match val {
                Val::Meta(mi, _) => max_mi.max(*mi + 1),
                _ => max_mi,
            })
        })
        .unwrap()
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
    // pub fn instantiate(self, arg: Term) -> Term {
    //     self.instantiate_safe(arg)
    //         .unwrap_or_else(|e| panic!("Cannot split on `{}`.", e))
    // }

    // pub fn instantiate_safe(self, arg: Term) -> Result<Term, Term> {
    //     let Closure::Plain(body) = self;
    //     Ok(body.subst(Substitution::one(arg)))
    // }

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
