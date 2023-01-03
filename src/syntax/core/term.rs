use crate::check::TypeCheckState;
use crate::syntax::abs::Expr;
use crate::syntax::core::redex::Subst;
use crate::syntax::core::subst::Substitution;
use crate::syntax::core::{Boxed, DeBruijn, SubstWith, Tele};
use crate::syntax::pattern;
use crate::syntax::{ConHead, Ident, Universe, DBI, GI, MI, UID};
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

/// Dependent identity type.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Id {
    pub tele: Tele,
    /// Depends on the telescope elements.
    pub ty: Box<Term>,
    /// Identity telescope elements.
    pub paths: Vec<Term>,
    pub a1: Box<Term>,
    pub a2: Box<Term>,
}

impl Id {
    pub fn new(
        tele: impl Into<Tele>,
        ty: impl Into<Box<Term>>,
        paths: impl Into<Vec<Term>>,
        a1: impl Into<Box<Term>>,
        a2: impl Into<Box<Term>>,
    ) -> Self {
        Self {
            tele: tele.into(),
            ty: ty.into(),
            paths: paths.into(),
            a1: a1.into(),
            a2: a2.into(),
        }
    }
}

/// Weak-head-normal-form terms, canonical values.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Val {}

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
    /// Identity (equality) type.
    ///
    /// ## Homogeneous (non-dependent) identity type
    /// `Id_A(a, a')`. The elements of the type are identifications.
    ///
    /// ## Non-dependent Function identification
    /// `Id_B->C(f, g) ≡ Π(u:B) Π(v:B) Π(q:Id_B(u,v)) Id_C(f(u), g(v))`.
    ///
    /// ## Dependent identity type
    /// The non-dependent version is definitionally just a special case
    /// of the dependent version, so we'll be using only the latter internally.
    ///
    /// `Id (\z.B) p (u,v) :≡ π1((ap (\z.B) p)↓)(u,v)`
    ///
    /// Heterogeneous identity types over refl reduce to homogeneous ones:
    /// `Id (\z.B) (refl a) (u,v) ≡ Id B[a/z] (u, v)`
    ///
    /// Similarly, dependent identity types in constant families also reduce to homogeneous ones:
    /// `Id (\z.B) p (u,v) ≡ Id B (u,v) (if z doesn't appear in B)`
    Id(Id),
    /// A special case of `ap` that cannot be reduced further.
    Refl(Box<Term>),
    Redex(Func, Ident, Vec<Elim>),
    /// Data elimination.
    Match(Box<Term>, Vec<Case>),
    /// General congruence term.
    ///
    /// ```text
    ///    x : A |- f : B   p : Id_A(a, a')
    /// -------------------------------------
    ///  ap (\x. f) p : Id_B(f[a/x], f[a'/x]).
    /// ```
    ///
    /// ## Reflexivity
    /// A special case is `ap (\x. y) p ≡ refl y (if y is a variable ≠ x)`.
    ///
    /// ## Identity
    /// `ap (\x. x) p ≡ p`.
    ///
    /// ## Functorial laws
    /// Since `ap` always reduces (even on redex terms), we can deduce the following equalities:
    /// ```text
    /// 1. ap (\x. f) (refl a) ≡ refl f[a/x];
    /// 2. ap (\y. g) (ap (\x. f) p) ≡ ap (\x. g[f/y]) p;
    /// 3. ap (\x. t) p ≡ refl t (x does not appear in t).
    /// ```
    ///
    /// ## Identity of functions:
    /// `ap (\x. f) p : Π(u:B) Π(v:B) Π(q:Id_B(u,v)) Id_C(f[a/x](u), g[a'/x](v))`
    /// `ap (\x. b) p : Id_C(b[a/x], b[a'/x])`
    ///
    /// With the rules defined above we can compute:
    /// `ap (\x. f b) p : Id_C(f[a/x](b[a/x], f[a'/x](b[a'/x])))`
    /// `ap (\x. f b) p ≡ (ap (\x. f) p) b[a/x] b[a'/x] (ap (\x. b) p)`
    ///
    /// ## Multi-variable ap
    /// `ap` is actually multi-variable, so we can 'bind' multiple variables and simultaneously
    /// substitute with multiple arguments:
    /// ```text
    ///               x1:A1, ... , xn:An |- t:C
    ///        p1 : Id_A1(a1,b1) ··· pn : Id_An(an,bn)
    /// --------------------------------------------------------
    /// ap (\x1.···\xn. t) (p1,...,pn) : Id_C(t[as/xs],t[bs/xs])
    /// ```
    /// `ap (\x.(λy.t)) p ≡ λu.λv.λq. ap (\x.\y. t) (p,q)`
    ///
    /// In addition, we can define `refl` as a 0-ary ap:
    /// `refl a ≡ ap (ε. a) ε`
    ///
    /// One can think of `ap` as a higher-dimensional explicit substitution.
    Ap(Tele, Vec<Term>, Box<Term>),
}

impl Term {
    pub(crate) fn to_expr(&self) -> Expr {
        todo!("Term::to_expr")
    }
}

impl Term {
    /// Recursively η-contracts a term.
    ///
    /// (λx. t x) ≡ t
    /// (fst a, snd a) ≡ a
    pub(crate) fn eta_contract(self) -> Term {
        match self {
            Term::Lam(Lambda(x, n)) => {
                let Closure::Plain(n) = n;
                let n = n.unboxed();
                match n {
                    Term::Var(y, mut es)
                        if !es.is_empty()
                            && es.last().unwrap().is_app()
                            && es.last().unwrap().clone().into_app() == Term::from_dbi(0) =>
                    {
                        es.pop();
                        es = es.subst(Substitution::strengthen(1));
                        return Term::Var(y, es);
                    }
                    Term::Cons(c, mut args)
                        if !args.is_empty() && args.last().unwrap() == &Term::from_dbi(0) =>
                    {
                        let _z = args.pop().unwrap();
                        args = args.subst(Substitution::strengthen(1));
                        return Term::Cons(c, args);
                    }
                    Term::Data(ValData { def, mut args })
                        if !args.is_empty() && args.last().unwrap() == &Term::from_dbi(0) =>
                    {
                        let _z = args.pop().unwrap();
                        args = args.subst(Substitution::strengthen(1));
                        return Term::Data(ValData { def, args });
                    }
                    Term::Meta(mi, mut es)
                        if !es.is_empty()
                            && es.last().unwrap().is_app()
                            && es.last().unwrap().clone().into_app() == Term::from_dbi(0) =>
                    {
                        let _z = es.pop().unwrap();
                        es = es.subst(Substitution::strengthen(1));
                        return Term::Meta(mi, es);
                    }
                    Term::Redex(f, x, mut es)
                        if !es.is_empty()
                            && es.last().unwrap().is_app()
                            && es.last().unwrap().clone().into_app() == Term::from_dbi(0) =>
                    {
                        let _z = es.pop().unwrap();
                        es = es.subst(Substitution::strengthen(1));
                        let is_empty = es.is_empty();
                        let contracted = Term::Redex(f, x, es);
                        if !is_empty {
                            return contracted.eta_contract();
                        }
                        return contracted;
                    }
                    n => Term::Lam(Lambda(x, Closure::Plain(n.boxed()))),
                }
            }
            t => t,
        }
    }
}

pub trait TryIntoPat<Ix, T> {
    fn try_into_pat(self) -> Option<Pat<Ix, T>>;
}

impl<Ix: From<DBI>, T: Subst<Term>> TryIntoPat<Ix, T> for Term {
    fn try_into_pat(self) -> Option<Pat<Ix, T>> {
        match self {
            Term::Cons(con_head, params) => Some(Pat::cons(
                con_head,
                params
                    .into_iter()
                    .map(Term::try_into_pat)
                    .collect::<Option<Vec<_>>>()?,
            )),
            Term::Var(Var::Bound(ix), _) => Some(Pat::Var(Ix::from(ix))),
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
            Term::Var(var, args) => {
                args.bound_free_vars(vars, depth);
                let uid = if let Var::Free(uid) = var {
                    *uid
                } else {
                    return;
                };
                if let Some(ix) = vars.get(&uid) {
                    let new_dbi = *ix + depth;
                    trace!("bound {} := {}", uid, new_dbi);
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
            Term::Universe(_) => {}
            Term::Data(data) => {
                data.args.bound_free_vars(vars, depth);
            }
            Term::Pi(x, ret) => {
                x.ty.bound_free_vars(vars, depth);
                ret.bound_free_vars(vars, depth);
            }
            Term::Lam(lam) => {
                lam.0.ty.bound_free_vars(vars, depth);
                lam.1.bound_free_vars(vars, depth);
            }
            Term::Cons(_, args) => {
                args.bound_free_vars(vars, depth);
            }
            Term::Meta(_, args) => {
                args.bound_free_vars(vars, depth);
            }
            Term::Id(_id) => {
                todo!("bound_free_vars for id")
            }
            Term::Refl(t) => {
                t.bound_free_vars(vars, depth);
            }
            Term::Ap(_tele, _ps, _t) => {
                // tele.bound_free_vars(vars, depth);
                // ps.bound_free_vars(vars, depth);
                // t.bound_free_vars(vars, depth);
                todo!("bound_free_vars for ap")
            }
        }
    }
}

impl Term {
    pub fn ap(
        tele: impl Into<Tele>,
        terms: impl Into<Vec<Term>>,
        term: impl Into<Box<Term>>,
    ) -> Self {
        let tele = tele.into();
        let terms = terms.into();
        assert_eq!(tele.len(), terms.len());
        Self::Ap(tele, terms, term.into())
    }

    pub fn as_id(&self) -> Option<&Id> {
        match self {
            Term::Id(id) => Some(id),
            _ => None,
        }
    }

    pub fn free_var(uid: UID) -> Self {
        Term::Var(Var::Free(uid), Vec::new())
    }

    pub(crate) fn is_cons(&self) -> bool {
        matches!(self, Term::Cons(..))
    }

    pub(crate) fn as_cons(&self) -> Option<(&ConHead, &Vec<Term>)> {
        match self {
            Term::Cons(con_head, args) => Some((con_head, args)),
            _ => None,
        }
    }

    pub(crate) fn is_eta_var(&self) -> bool {
        matches!(self, Term::Var(_, es) if es.is_empty())
    }

    pub fn is_whnf(&self) -> bool {
        matches!(
            self,
            Term::Universe(_)
                | Term::Data(_)
                | Term::Pi(..)
                | Term::Lam(..)
                | Term::Cons(..)
                | Term::Meta(..)
                | Term::Var(..)
                | Term::Id(..)
                | Term::Refl(..)
        )
    }

    #[allow(unused)]
    pub(crate) fn tele_len(&self) -> usize {
        match self {
            Term::Pi(_, Closure::Plain(t)) => t.tele_len() + 1,
            _ => 0,
        }
    }

    pub(crate) fn lam(p0: Bind<Box<Term>>, p1: Term) -> Term {
        Term::Lam(Lambda(p0, Closure::Plain(box p1)))
    }

    pub fn match_case(t: impl Into<Box<Term>>, cs: impl Into<Vec<Case>>) -> Self {
        Term::Match(t.into(), cs.into())
    }

    pub fn match_elim(x: DBI, cs: impl Into<Vec<Case>>) -> Self {
        Self::match_case(box Term::from_dbi(x), cs)
    }

    pub fn is_meta(&self) -> bool {
        matches!(self, Term::Meta(_, _))
    }

    pub fn as_meta(&self) -> Option<(MI, &Vec<Elim>)> {
        match self {
            Term::Meta(i, elims) => Some((*i, elims)),
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

    pub fn print(&self, _tcs: &TypeCheckState) {}

    #[allow(unused)]
    pub(crate) fn into_pi(self) -> Either<Term, (Bind<Box<Term>>, Closure)> {
        match self {
            Term::Pi(b, c) => Right((b, c)),
            v => Left(v),
        }
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

/// Constructors and traversal functions.
impl Term {
    // pub fn is_type(&self) -> bool {
    //     use Term::*;
    //     match match self {
    //         Term::Whnf(val) => val,
    //         Term::Redex(..) => return false,
    //         Term::Match(..) => return false,
    //
    //     } {
    //         Pi(..) | Data(..) | Universe(..) => true,
    //         Var(..) | Meta(..) | Cons(..) | Lam(..) => false,
    //     }
    // }

    pub fn inductive(ix: GI, params: Vec<Term>) -> Self {
        Term::Data(ValData::new(ix, params))
    }

    pub fn is_universe(&self) -> bool {
        matches!(self, Term::Universe(..))
    }

    pub fn cons(name: ConHead, params: Vec<Self>) -> Self {
        Term::Cons(name, params)
    }

    pub fn data(info: ValData) -> Self {
        Term::Data(info)
    }

    pub fn meta(index: MI, params: Vec<Elim>) -> Self {
        Term::Meta(index, params)
    }

    pub fn universe(uni: Universe) -> Self {
        Term::Universe(uni)
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
            Term::Pi(bind, Closure::Plain(r)) if n != 0 => {
                let (mut view, r) = r.tele_view_n(n - 1);
                view.push(bind.unboxed());
                (view, r)
            }
            Term::Lam(Lambda(bind, Closure::Plain(r))) if n != 0 => {
                let (mut view, r) = r.tele_view_n(n - 1);
                view.push(bind.unboxed());
                (view, r)
            }
            // The capacity is an arbitrarily estimated value.
            e => (Tele(Vec::with_capacity(2)), e),
        }
    }

    /// Returns E\[H\] view.
    pub fn head_elims_view(self) -> (Self, Vec<Elim>) {
        match self {
            Term::Var(v, es) => (Term::Var(v, vec![]), es),
            Term::Redex(Func::Index(gi), i, es) => (Term::Redex(Func::Index(gi), i, vec![]), es),
            Term::Redex(Func::Lam(lam), _, es) => (Term::Lam(lam), es),
            Term::Cons(c, es) => (
                Term::Cons(c, vec![]),
                es.into_iter().map(Elim::from).collect(),
            ),
            Term::Data(ValData { def, args }) => (
                Term::Data(ValData { def, args: vec![] }),
                args.into_iter().map(Elim::from).collect(),
            ),
            // Term::Meta(m, es) => (Term::Meta(m, vec![]), es),
            e => (e, vec![]),
        }
    }

    // pub fn pi(licit: Plicitness, name: UID, param_type: Term, body: Closure, loc: Loc) -> Self {
    //     Self::pi2(Bind::boxing(licit, name, param_type, loc), body)
    // }

    pub fn pi2(param: Bind<Box<Term>>, body: Closure) -> Self {
        Term::Pi(param, body)
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

    pub fn is_app(&self) -> bool {
        match self {
            Elim::App(..) => true,
            Elim::Proj(..) => false,
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
