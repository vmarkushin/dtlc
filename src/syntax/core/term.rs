use crate::syntax::core::redex::Subst;
use crate::syntax::core::subst::Substitution;
use crate::syntax::core::Tele;
use crate::syntax::{ConHead, Ident, Loc, Plicitness, Universe, DBI, GI, MI, UID};
use derive_more::From;
use itertools::Either;
use itertools::Either::*;

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
    #[allow(unused)]
    pub(crate) fn into_pi(self) -> Either<(Bind<Box<Term>>, Closure), Val> {
        match self {
            Val::Pi(b, c) => Left((b, c)),
            v => Right(v),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Func {
    Index(GI),
    Lam(Lambda),
}

/// Type for terms.
#[derive(Debug, PartialEq, Eq, Clone, From)]
pub enum Term {
    Whnf(Val),
    Redex(Func, Ident, Vec<Elim>),
}

impl Term {
    pub(crate) fn lam(p0: Bind<Box<Term>>, p1: Term) -> Term {
        Term::Whnf(Val::Lam(Lambda(p0, Closure::Plain(box p1))))
    }

    pub fn is_meta(&self) -> bool {
        match self {
            Term::Whnf(Val::Meta(_, _)) => true,
            _ => false,
        }
    }

    pub fn as_meta(&self) -> Option<(MI, &Vec<Elim>)> {
        match self {
            Term::Whnf(Val::Meta(i, elims)) => Some((*i, elims)),
            _ => None,
        }
    }
}

pub type Bind<T = Term> = super::super::Bind<T>;

/// Type for eliminations.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Elim {
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
        } {
            Pi(..) | Data(..) | Universe(..) => true,
            Var(..) | Meta(..) | Cons(..) | Lam(..) => false,
        }
    }

    pub fn is_universe(&self) -> bool {
        match self {
            Term::Whnf(Val::Universe(..)) => true,
            _ => false,
        }
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
        match self {
            Term::Whnf(Val::Pi(bind, Closure::Plain(r))) => {
                let (mut view, r) = r.tele_view();
                view.insert(0, bind.unboxed());
                (view, r)
            }
            Term::Whnf(Val::Lam(Lambda(bind, Closure::Plain(r)))) => {
                let (mut view, r) = r.tele_view();
                view.insert(0, bind.unboxed());
                (view, r)
            }
            // The capacity is an arbitrarily estimated value.
            e => (Vec::with_capacity(2), e),
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
