use crate::check::{Error, Result, TypeCheckState};
use crate::syntax::core::{
    Bind, Binder, Boxed, Closure, Ctx, DeBruijn, Elim, Func, Lambda, PrimSubst, Subst, SubstWith,
    Substitution, Tele, Term, Type, Var,
};
use crate::syntax::{Plicitness, Universe, DBI, MI};
use itertools::Either;
use itertools::Either::{Left, Right};
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    Hole,
    // A solution?
    Defn(Term),
}

impl Occurrence for Decl {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        match self {
            Decl::Hole => HashSet::new(),
            Decl::Defn(t) => t.free(flavour),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Blocked,
    Active,
}

/*
> data Param     =  P Type | Twins Type Type
> type Params    =  Bwd (Nom, Param)
>
> data Equation  =  EQN Type Tm Type Tm
> data Problem   =  Unify Equation | All Param (Bind Nom Problem)
> data Entry     =  E (Name Tm) (Type, Decl Tm) | Q Status Problem
 */

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Param {
    /// T
    P(Term),
    /// S‡T
    Twins(Term, Term),
}

impl Display for Param {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Param::P(ty) => write!(f, "{}", ty),
            Param::Twins(ty1, ty2) => write!(f, "{}&{}", ty1, ty2),
        }
    }
}

impl Occurrence for Param {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        match self {
            Param::P(ty) => ty.free(flavour),
            Param::Twins(ty1, ty2) => (ty1, ty2).free(flavour),
        }
    }
}

impl Display for Bind<Param> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.licit == Plicitness::Implicit {
            write!(f, "{{{}:{}}}", self.ident, self.ty)
        } else {
            write!(f, "{}:{}", self.ident, self.ty)
        }
    }
}

type Params = Ctx<Bind<Param>>;

impl Binder for Bind<Param> {
    type Param = Param;
    type Var = Var;

    fn lookup(&self, var: &Self::Var) -> Option<Bind<&Type>> {
        match (self, var) {
            (
                Bind {
                    licit,
                    name,
                    ty: Param::Twins(ty_l, ty_r),
                    ident,
                },
                Var::Twin(_, f),
            ) => {
                if *f {
                    Some(Bind {
                        licit: *licit,
                        name: name.clone(),
                        ty: ty_r,
                        ident: ident.clone(),
                    })
                } else {
                    Some(Bind {
                        licit: *licit,
                        name: name.clone(),
                        ty: ty_l,
                        ident: ident.clone(),
                    })
                }
            }
            (
                Bind {
                    licit,
                    name,
                    ty: Param::P(ty),
                    ident,
                },
                Var::Bound(_),
            ) => Some(Bind {
                licit: *licit,
                name: name.clone(),
                ty,
                ident: ident.clone(),
            }),
            _ => None,
        }
    }
}

enum ApplyStatus {
    Changed,
    NotChanged,
}

/// (s : S) ≡ (t : T)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Equation {
    tm1: Term,
    ty1: Term,
    tm2: Term,
    ty2: Term,
}

impl Equation {
    fn new(tm1: Term, ty1: Term, tm2: Term, ty2: Term) -> Self {
        Self { ty1, tm1, ty2, tm2 }
    }

    fn sym(self) -> Self {
        Self::new(self.tm2, self.ty2, self.tm1, self.ty1)
    }

    /*
    > orthogonal :: Equation -> Bool
    > orthogonal (EQN SET (Pi _ _) SET (Sig _ _))     = True
    > orthogonal (EQN SET (Pi _ _) SET BOOL)          = True
    > orthogonal (EQN SET (Sig _ _) SET (Pi _ _))     = True
    > orthogonal (EQN SET (Sig _ _) SET BOOL)         = True
    > orthogonal (EQN SET BOOL SET (Pi _ _))          = True
    > orthogonal (EQN SET BOOL SET (Sig _ _))         = True
    > orthogonal (EQN BOOL TT BOOL FF)                = True
    > orthogonal (EQN BOOL FF BOOL TT)                = True
    >
    > orthogonal (EQN SET (Pi _ _)  _ (N (V _ _) _))  = True
    > orthogonal (EQN SET (Sig _ _) _ (N (V _ _) _))  = True
    > orthogonal (EQN SET BOOL _ (N (V _ _) _))       = True
    > orthogonal (EQN BOOL TT _ (N (V _ _) _))        = True
    > orthogonal (EQN BOOL FF _ (N (V _ _) _))        = True
    >
    > orthogonal (EQN _ (N (V _ _) _) SET (Pi _ _))   = True
    > orthogonal (EQN _ (N (V _ _) _) SET (Sig _ _))  = True
    > orthogonal (EQN _ (N (V _ _) _) SET BOOL)       = True
    > orthogonal (EQN _ (N (V _ _) _) BOOL TT)        = True
    > orthogonal (EQN _ (N (V _ _) _) BOOL FF)        = True
    >
    > orthogonal _                                    = False
     */
    fn orthogonal(&self) -> bool {
        let Equation { ty1, tm1, ty2, tm2 } = self;
        matches!(
            (ty1, tm1, ty2, tm2),
            (Term::Universe(_), Term::Pi(..), _, Term::Var(..))
                | (_, Term::Var(..), Term::Universe(_), Term::Pi(..))
        )
    }
}

impl Occurrence for Equation {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        let Self { ty1, tm1, ty2, tm2 } = self;
        (ty1, tm1, ty2, tm2).free(flavour)
    }
}

impl Display for Equation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let Self { ty1, tm1, ty2, tm2 } = self;
        write!(f, "({tm1} : {ty1}) == ({tm2} : {ty2})")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Problem {
    /// (s : S) ≡ (t : T)
    Unify(Equation),
    /// ∀Γ. P
    All(Bind<Param>, Box<Problem>),
}

impl SubstWith<'_> for Equation {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Self {
        let Equation { ty1, tm1, ty2, tm2 } = self;
        Equation {
            ty1: ty1.subst_with(subst.clone(), tcs),
            tm1: tm1.subst_with(subst.clone(), tcs),
            ty2: ty2.subst_with(subst.clone(), tcs),
            tm2: tm2.subst_with(subst, tcs),
        }
    }
}

impl SubstWith<'_> for Param {
    fn subst_with(self, subst: Rc<PrimSubst<Term>>, state: &'_ mut TypeCheckState) -> Self {
        match self {
            Param::P(t) => Param::P(t.subst_with(subst, state)),
            Param::Twins(t, u) => Param::Twins(
                t.subst_with(subst.clone(), state),
                u.subst_with(subst, state),
            ),
        }
    }
}

impl SubstWith<'_> for Problem {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Self {
        match self {
            Problem::Unify(t) => Problem::Unify(t.subst_with(subst, tcs)),
            Problem::All(bind, p) => {
                let bind = bind.subst_with(subst.clone(), tcs);
                let p = p.subst_with(subst.lift_by(1), tcs);
                Problem::All(bind, Box::new(p))
            }
        }
    }
}

impl Occurrence for Problem {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        match self {
            Problem::Unify(eq) => eq.free(flavour),
            Problem::All(param, prob) => (prob, param).free(flavour),
        }
    }
}

impl Problem {
    pub fn all(param: Bind<Param>, prob: Problem) -> Self {
        Self::All(param, Box::new(prob))
    }

    pub fn alls(params: Vec<Bind<Param>>, prob: Problem) -> Self {
        params
            .into_iter()
            .rev()
            .fold(prob, |prob, param| Self::all(param, prob))
    }
}

impl Display for Problem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Problem::Unify(eq) => write!(f, "{eq}"),
            Problem::All(param, prob) => write!(f, "{param} -> {prob}"),
        }
    }
}

type MetaSubst = HashMap<MI, Term>;

/// Meta context.
pub type Context = (Ctx<Entry>, Tele<Either<MetaSubst, Entry>>);

/// Entry in the context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Entry {
    // Meta Equation
    E(MI, Type, Decl),
    // Question
    Q(Status, Problem),
}

impl Occurrence for Entry {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        match self {
            Entry::E(_, ty, decl) => ty
                .free(flavour)
                .union(&decl.free(flavour))
                .into_iter()
                .cloned()
                .collect(),
            Entry::Q(_, prob) => prob.free(flavour),
        }
    }
}

impl Display for Entry {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Entry::E(x, ty, Decl::Hole) => write!(f, "?{x} : {ty}"),
            Entry::E(x, ty, Decl::Defn(v)) => write!(f, "?{x} : {ty} := {v}"),
            Entry::Q(s, p) => write!(f, "?{s:?} {p}"),
        }
    }
}

pub struct State {
    mctx: Context,
    params: Params,
}

enum OccurrenceResult {
    Strong,
    Nothing,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Flavour {
    Vars,
    RigVars,
    Metas,
}

type Instantiation = (MI, Type, Box<dyn FnOnce(Term) -> Term>);

pub trait MetaSubstitution {
    fn meta_subst(&mut self, subst: &MetaSubst);
}

impl<T: MetaSubstitution> MetaSubstitution for Vec<T> {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        for t in self {
            t.meta_subst(subst)
        }
    }
}

impl MetaSubstitution for Term {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        match self {
            Term::Universe(_) => {}
            Term::Meta(mi, es) | Term::Var(Var::Meta(mi), es) => {
                if let Some(t) = subst.get(mi) {
                    es.meta_subst(subst);
                    *self = t.clone().apply_elim(es.clone())
                }
            }
            Term::Var(_, es) => {
                es.meta_subst(subst);
            }
            Term::Pi(param, body) => {
                param.meta_subst(subst);
                body.meta_subst(subst);
            }
            Term::Lam(lam) => {
                lam.meta_subst(subst);
            }
            Term::Redex(f, _, es) => {
                f.meta_subst(subst);
                es.meta_subst(subst);
            }
            t => unimplemented!("meta_subst: {:?}", t),
        }
    }
}

impl MetaSubstitution for Param {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        match self {
            Param::P(t) => t.meta_subst(subst),
            Param::Twins(t, u) => {
                t.meta_subst(subst);
                u.meta_subst(subst);
            }
        }
    }
}

impl MetaSubstitution for Bind<Box<Term>> {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        self.ty.meta_subst(subst)
    }
}

impl MetaSubstitution for Bind<Box<Param>> {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        self.ty.meta_subst(subst)
    }
}

impl MetaSubstitution for Bind<Param> {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        self.ty.meta_subst(subst)
    }
}

impl MetaSubstitution for Closure {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        self.as_inner_mut().meta_subst(subst)
    }
}

impl MetaSubstitution for Lambda {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        self.0.meta_subst(subst);
        self.1.meta_subst(subst);
    }
}

impl MetaSubstitution for Elim {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        match self {
            Elim::App(t) => t.meta_subst(subst),
            Elim::Proj(_) => {}
        }
    }
}

impl MetaSubstitution for Func {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        match self {
            Func::Index(_) => {}
            Func::Lam(lam) => lam.meta_subst(subst),
        }
    }
}

impl MetaSubstitution for Problem {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        match self {
            Problem::Unify(eq) => eq.meta_subst(subst),
            Problem::All(param, prob) => {
                param.meta_subst(subst);
                prob.meta_subst(subst);
            }
        }
    }
}

impl MetaSubstitution for Equation {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        self.tm1.meta_subst(subst);
        self.ty1.meta_subst(subst);
        self.tm2.meta_subst(subst);
        self.ty2.meta_subst(subst);
    }
}

impl MetaSubstitution for Entry {
    fn meta_subst(&mut self, subst: &MetaSubst) {
        match self {
            Entry::E(_, ty, decl) => {
                ty.meta_subst(subst);
                match decl {
                    Decl::Hole => {}
                    Decl::Defn(v) => v.meta_subst(subst),
                }
            }
            Entry::Q(_, prob) => prob.meta_subst(subst),
        }
    }
}

pub trait Occurrence {
    fn free(&self, flavour: Flavour) -> HashSet<Var>;

    fn fvs(&self) -> HashSet<Var> {
        self.free(Flavour::Vars)
    }

    fn fvrigs(&self) -> HashSet<Var> {
        self.free(Flavour::RigVars)
    }

    fn fmvs(&self) -> HashSet<MI> {
        self.free(Flavour::Metas)
            .into_iter()
            .map(|v| match v {
                Var::Meta(x) => x,
                _ => unreachable!(),
            })
            .collect()
    }
}

impl<T1, T2> Occurrence for (T1, T2)
where
    T1: Occurrence,
    T2: Occurrence,
{
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        let (t1, t2) = self;
        &t1.free(flavour) | &t2.free(flavour)
    }
}

impl<T1, T2, T3> Occurrence for (T1, T2, T3)
where
    T1: Occurrence,
    T2: Occurrence,
    T3: Occurrence,
{
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        let (t1, t2, t3) = self;
        &(&t1.free(flavour) | &t2.free(flavour)) | &t3.free(flavour)
    }
}

impl<T1, T2, T3, T4> Occurrence for (T1, T2, T3, T4)
where
    T1: Occurrence,
    T2: Occurrence,
    T3: Occurrence,
    T4: Occurrence,
{
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        let (t1, t2, t3, t4) = self;
        &(&(&t1.free(flavour) | &t2.free(flavour)) | &t3.free(flavour)) | &t4.free(flavour)
    }
}

impl Occurrence for Term {
    fn free(&self, f: Flavour) -> HashSet<Var> {
        use Flavour::*;
        match self {
            Term::Lam(lam) => lam.free(f),
            // TODO: cons, data, ...
            Term::Pi(a, b) => (a, b).free(f),
            Term::Var(x, es) if f == RigVars && matches!(x, Var::Twin(..) | Var::Bound(..)) => es
                .free(f)
                .union(&vec![x.clone()].into_iter().collect())
                .cloned()
                .collect(),
            Term::Meta(_, _) | Term::Var(Var::Meta(..), _) if f == RigVars => Default::default(),
            Term::Var(x, es) => (x, es).free(f),

            Term::Meta(_, es) if f == Vars => es.free(f),
            Term::Meta(_, es) if f == RigVars => es.free(f),
            Term::Meta(x, es) if f == Metas => es
                .free(f)
                .union(&vec![Var::Meta(*x)].into_iter().collect())
                .cloned()
                .collect(),
            t => panic!("[free] not implemented: {t:?}"),
        }
    }
}

/*
>     free Vars       (M _)      = Set.empty
>     free RigVars    (M _)      = Set.empty
>     free Metas      (M alpha)  = singleton alpha
>     free Vars       (V x _)    = singleton x
>     free RigVars    (V x _)    = singleton x
>     free Metas      (V _ _)    = Set.empty
 */
impl Occurrence for Var {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        use Flavour::*;
        match (flavour, self) {
            (Vars, Var::Meta(_)) => Default::default(),
            (RigVars, Var::Meta(_)) => Default::default(),
            (Metas, Var::Meta(alpha)) => vec![Var::Meta(*alpha)].into_iter().collect(),
            (Vars | RigVars, x) if matches!(x, Var::Bound(..) | Var::Twin(..)) => {
                vec![*x].into_iter().collect()
            }
            (Metas, _) => Default::default(),
            _ => Default::default(),
        }
    }
}

impl Occurrence for Lambda {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        self.0
            .free(flavour)
            .union(&self.1.free(flavour))
            .cloned()
            .collect()
    }
}

impl Occurrence for Closure {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        self.as_inner().free(flavour)
    }
}

impl Occurrence for Elim {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        match self {
            Elim::App(t) => t.free(flavour),
            Elim::Proj(_) => Default::default(),
        }
    }
}

impl<T: Occurrence> Occurrence for Box<T> {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        self.as_ref().free(flavour)
    }
}

impl<T: Occurrence> Occurrence for Vec<T> {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        self.iter()
            .fold(HashSet::default(), |acc, t| (acc, t).free(flavour))
    }
}

impl<T: Occurrence> Occurrence for HashSet<T> {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        self.iter()
            .fold(HashSet::default(), |acc, t| (acc, t).free(flavour))
    }
}

impl<T: Occurrence> Occurrence for Bind<T> {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        self.ty.free(flavour)
    }
}

impl<T: Occurrence> Occurrence for &T {
    fn free(&self, flavour: Flavour) -> HashSet<Var> {
        (*self).free(flavour)
    }
}

/*
> occurCheck :: Bool -> Nom -> Tm -> Bool
> occurCheck w alpha (L b)           =  occurCheck w alpha t
>                                           where (_, t) = unsafeUnbind b
> occurCheck w alpha (N (V _ _) e)   =  getAny $ foldMap
>                                           (foldMapElim (Any `o` occurCheck False alpha)) e
> occurCheck w alpha (N (M beta) e)  =  alpha == beta && (w || isJust (toVars e))
> occurCheck w alpha (C c)           =  getAny $ foldMap (Any `o` occurCheck w alpha) c
> occurCheck w alpha (Pi _S _T)      =  occurCheck w alpha _S || occurCheck w alpha _T'
>                                           where (_, _T') = unsafeUnbind _T
> occurCheck w alpha (Sig _S _T)      =  occurCheck w alpha _S || occurCheck w alpha _T'
>                                           where (_, _T') = unsafeUnbind _T
 */
fn occur_check(is_strong_rigid: bool, x: MI, t: &Term) -> bool {
    match t {
        Term::Lam(b) => {
            let t = b.1.as_inner();
            occur_check(is_strong_rigid, x, &t)
        }
        Term::Var(_, es) => es.iter().any(|e| match e {
            Elim::App(t) => occur_check(false, x, t),
            _ => false,
        }),
        Term::Meta(y, es) => x == *y && (is_strong_rigid || !to_vars(es.clone()).is_some()),
        // Term::Cons(c) => ..., // TODO: cons, data, ...
        Term::Pi(t1, t2) => {
            occur_check(is_strong_rigid, x, &t1.ty)
                || occur_check(is_strong_rigid, x, t2.as_inner())
        }
        t => {
            panic!("occur_check: {:?}", t);
        }
    }
}

fn believe<T>() -> T {
    unimplemented!()
}

type Id = u32;

impl TypeCheckState {
    /*
    > unify (EQN (Pi _A _B) f (Pi _S _T) g) = do
    >     x <- fresh (s2n "x")
    >     active $ allTwinsProb x _A _S (eqnProb (inst _B (twinL x)) (f $$ twinL x) (inst _T (twinR x)) (g $$ twinR x))
    > unify (EQN (Sig _A _B) t (Sig _C _D) w) = do
    >     active $ eqnProb _A (hd t) _C (hd w)
    >     active $ eqnProb (inst _B (hd t)) (tl t) (inst _D (hd w)) (tl w)
    >
    > unify q@(EQNO (N (M alpha) e) (N (M beta) e'))
    >     | alpha == beta =  tryPrune q <|| tryPrune (sym q) <|| flexFlexSame q
    > unify q@(EQNO (N (M alpha) e) (N (M beta) e'))  = tryPrune q <|| tryPrune (sym q) <|| flexFlex [] q
    > unify q@(EQNO (N (M alpha) e) t)                = tryPrune q <|| flexTerm [] q
    > unify q@(EQNO t (N (M alpha) e))                = tryPrune (sym q) <|| flexTerm [] (sym q)
    > unify q                                         = rigidRigid q

     */
    pub fn unify(&mut self, id: Id, equation: Equation) -> Result<()> {
        let Equation { ty1, tm1, ty2, tm2 } = equation.clone();
        match (ty1, ty2) {
            (Term::Pi(a1, b1), Term::Pi(a2, b2)) => {
                let a1 = *a1.clone().ty;
                let a2 = *a2.clone().ty;
                let p = Problem::All(
                    Bind::unnamed(Param::Twins(a1, a2)),
                    Box::new(Problem::Unify(Equation::new(
                        tm1.apply(vec![Term::from_dbi(0)]),
                        b1.into_inner(),
                        tm2.apply(vec![Term::from_dbi(0)]),
                        b2.into_inner(),
                    ))),
                );
                self.active(id, p)
            }
            (Term::Meta(m1, xs), Term::Meta(m2, ys)) if m1 == m2 => {
                if !self.try_prune(id, equation.clone())? {
                    if !self.try_prune(id, equation.clone().sym())? {
                        return self.flex_flex_same(id, equation);
                    }
                }
                Ok(())
            }
            (Term::Meta(m1, xs), Term::Meta(m2, ys)) => {
                if !self.try_prune(id, equation.clone())? {
                    if !self.try_prune(id, equation.clone().sym())? {
                        return self.flex_flex(vec![], id, equation);
                    }
                }
                Ok(())
            }
            (Term::Meta(m1, xs), _) => {
                if !self.try_prune(id, equation.clone())? {
                    self.flex_term(vec![], id, equation)?;
                }
                Ok(())
            }
            (_, Term::Meta(m2, ys)) => {
                if !self.try_prune(id, equation.clone().sym())? {
                    self.flex_term(vec![], id, equation)?;
                }
                Ok(())
            }
            _ => {
                self.rigid_rigid(equation.clone())?;
                Ok(())
            }
        }
    }

    /*
    > rigidRigid :: Equation -> Contextual ()
    > rigidRigid (EQN SET (Pi _A _B) SET (Pi _S _T)) = do
    >     x <- fresh (s2n "x")
    >     active $ eqnProb SET _A SET _S
    >     active $ allTwinsProb x _A _S (eqnProb SET (inst _B (twinL x)) SET (inst _T (twinR x)))
    >
    > rigidRigid (EQN SET (Sig _A _B) SET (Sig _S _T)) = do
    >     x <- fresh (s2n "x")
    >     active $ eqnProb SET _A SET _S
    >     active $ allTwinsProb x _A _S (eqnProb SET (inst _B (twinL x)) SET (inst _T (twinR x)))
    >
    > rigidRigid (EQNO (N (V x w) e) (N (V x' w') e')) =
    >     matchSpine x w e x' w' e' >> return ()
    >
    > rigidRigid q  | orthogonal q  = throwError "Rigid-rigid mismatch"
    >               | otherwise     = block $ Unify q


    */
    fn rigid_rigid(&mut self, equation: Equation) -> Result<()> {
        let Equation { ty1, tm1, ty2, tm2 } = equation.clone();
        match (tm1.clone(), tm2.clone()) {
            (Term::Pi(a1, b1), Term::Pi(a2, b2)) => {
                let xs = vec![Equation::new(
                    b1.clone().into_inner(),
                    Term::universe(Universe(0)),
                    b2.clone().into_inner(),
                    Term::universe(Universe(0)),
                )];
                self.active(
                    believe(),
                    Problem::Unify(Equation::new(
                        *a1.clone().ty,
                        Term::universe(Universe(0)),
                        *a2.clone().ty,
                        Term::universe(Universe(0)),
                    )),
                )?;
                self.active(
                    believe(),
                    Problem::All(
                        Bind::unnamed(Param::Twins(*a1.clone().ty, *a2.clone().ty)),
                        Box::new(Problem::Unify(Equation::new(
                            tm1.apply(vec![Term::from_dbi(0)]),
                            b1.into_inner(),
                            tm2.apply(vec![Term::from_dbi(0)]),
                            b2.into_inner(),
                        ))),
                    ),
                )?;
                Ok(())
            }
            (Term::Var(x, xs), Term::Var(y, ys)) if x == y => {
                self.match_spine(x, &xs, y, &ys)?;
                Ok(())
            }
            _ => {
                if equation.orthogonal() {
                    Err(Error::RigidRigidMismatch)
                } else {
                    self.block(believe(), Problem::Unify(equation))
                }
            }
        }
    }

    /*
    > matchSpine ::  Nom -> Twin -> Bwd Elim ->
    >                Nom -> Twin -> Bwd Elim ->
    >                    Contextual (Type, Type)
    > matchSpine x w B0 x' w' B0
    >   | x == x'    = (,) <$> lookupVar x w <*> lookupVar x' w'
    >   | otherwise  = throwError "rigid head mismatch"
    > matchSpine x w (e :< A a) x' w' (e' :< A s) = do
    >     (Pi _A _B, Pi _S _T) <- matchSpine x w e x' w' e'
    >     active $ eqnProb _A a _S s
    >     return (inst _B a, inst _T s)
    > matchSpine _ _ _ _ _ _ = throwError "spine mismatch"

    */
    fn match_spine(&mut self, x: Var, es1: &[Elim], y: Var, es2: &[Elim]) -> Result<(Type, Type)> {
        match (es1, es2) {
            ([], []) => {
                if DBI::from(x) == DBI::from(y) {
                    let ty1 = self.lookup2(x).ty.clone();
                    let ty2 = self.lookup2(y).ty.clone();
                    return Ok((ty1, ty2));
                } else {
                    return Err(Error::RigidRigidMismatch);
                }
            }
            ([es1 @ .., Elim::App(a1)], [es2 @ .., Elim::App(a2)]) => {
                let (Term::Pi(xx, t), Term::Pi(yy, u)) = self.match_spine(x, es1, y, es2)? else {
                    return Err(Error::SpineMismatch);
                };
                let a = *a1.clone();
                let b = *a2.clone();
                self.active(
                    believe(),
                    Problem::Unify(Equation::new(
                        a.clone(),
                        *xx.clone().ty,
                        b.clone(),
                        *yy.clone().ty,
                    )),
                )?;
                return Ok((t.into_inner(), u.into_inner()));
            }
            _ => {}
        }
        Err(Error::SpineMismatch)
    }

    /*
    > flexTerm ::  [Entry] -> Equation -> Contextual ()
    > flexTerm _Xi q@(EQNO (N (M alpha) _) _) = do
    >   _Gam <- fmap snd <$> ask
    >   popL >>= \ e -> case e of
    >     E beta (_T, HOLE)
    >       | alpha == beta && alpha `elem` fmvs _Xi   -> do  pushLs (e:_Xi)
    >                                                         block (Unify q)
    >       | alpha == beta                            -> do  pushLs _Xi
    >                                                         tryInvert q _T
    >                                                             <|| (block (Unify q) >> pushL e)
    >       | beta `elem` fmvs (_Gam, _Xi, q)          ->  flexTerm (e : _Xi) q
    >     _                                            -> do  pushR (Right e)
    >                                                         flexTerm _Xi q

     */
    fn flex_term(&mut self, mut entries: Vec<Entry>, id: Id, equation: Equation) -> Result<()> {
        let mut ctx = self.gamma2.clone();
        let e = self.pop_l()?;
        let (mi_a, _) = equation
            .tm1
            .as_meta()
            .expect("flex_rigid: tm1 is not a meta");

        match &e {
            Entry::E(mi_b, t, Decl::Hole) => {
                if mi_a == *mi_b {
                    let mi_in_b = entries.fmvs().contains(&mi_a);
                    if mi_in_b {
                        self.push_l(e)?;
                        for e in entries {
                            self.push_l(e)?;
                        }
                        self.block(id, Problem::Unify(equation))?;
                    } else {
                        for e in entries {
                            self.push_l(e)?;
                        }
                        if !self.try_invert(id, equation.clone(), t.clone())? {
                            self.block(id, Problem::Unify(equation))?;
                            self.push_l(e)?;
                        }
                    }
                    return Ok(());
                } else if (&(&ctx.fmvs() | &entries.fmvs()) | &equation.fmvs()).contains(mi_b) {
                    entries.insert(0, e);
                    self.flex_term(entries, id, equation)?;
                    return Ok(());
                }
            }
            _ => {}
        }

        self.push_r(Right(e))?;
        self.flex_term(entries, id, equation)
    }

    /*
    > flexFlexSame ::  Equation -> Contextual ()
    > flexFlexSame q@(EQNO (N (M alpha) e) (N (M alpha_) e')) = do
    >     (_Tel, _T) <- telescope =<< lookupMeta alpha
    >     case intersect _Tel e e' of
    >         Just _Tel' | fvs _T `isSubsetOf` vars _Tel'  -> instantiate (alpha, _Pis _Tel' _T, \ beta -> lams' _Tel (beta $*$ _Tel))
    >         _                                            -> block (Unify q)


     */
    fn flex_flex_same(&mut self, id: Id, equation: Equation) -> Result<()> {
        let Equation {
            tm1: Term::Meta(mi_a, es),
            ty1,
            tm2: Term::Meta(mi_b, es_),
            ty2,
        } = equation.clone() else {
            panic!("flex_flex_same: not a meta equation")
        };
        assert_eq!(mi_a, mi_b);
        let (tel, ty) = self.lookup_meta_ctx(mi_a)?.tele_view();
        match self.intersect(tel.clone(), &es, &es_) {
            Some(tel_) if is_subset_of(ty.fvs(), tel_.vars().into_iter().collect()) => self
                .instantiate((
                    mi_a,
                    Term::pis(tel_, ty),
                    Box::new(move |mi_b: Term| {
                        // TODO: maybe here is an error in tel.vars() (should be tel_)
                        Term::lams(
                            tel.clone(),
                            mi_b.apply(
                                tel.vars()
                                    .into_iter()
                                    .map(|x| Term::Var(x, vec![]))
                                    .collect(),
                            ),
                        )
                    }),
                )),
            _ => self.block(id, Problem::Unify(equation)),
        }
    }

    /*
    > flexFlex ::  [Entry] -> Equation -> Contextual ()
    > flexFlex _Xi q@(EQNO (N (M alpha) ds) (N (M beta) es)) = do
    >   _Gam <- fmap snd <$> ask
    >   popL >>= \ e -> case e of
    >     E gamma (_T, HOLE)
    >       | gamma `elem` [alpha, beta] && gamma `elem` fmvs(_Xi) -> do  pushLs (e : _Xi)
    >                                                                     block (Unify q)
    >       | gamma == alpha                     -> do  pushLs _Xi
    >                                                   tryInvert q _T <|| flexTerm [e] (sym q)
    >       | gamma == beta                      -> do  pushLs _Xi
    >                                                   tryInvert (sym q) _T <|| flexTerm [e] q
    >       | gamma `elem` fmvs (_Gam, _Xi, q)   -> flexFlex (e : _Xi) q
    >     _                                      -> do  pushR (Right e)
    >                                                   flexFlex _Xi q


     */
    fn flex_flex(&mut self, mut entries: Vec<Entry>, id: Id, equation: Equation) -> Result<()> {
        let Equation {
            tm1: Term::Meta(mi_a, ds),
            ty1,
            tm2: Term::Meta(mi_b, es),
            ty2,
        } = equation.clone() else {
            panic!("todo");
        };
        let mut ctx = self.gamma2.clone();
        let e = self.pop_l()?;
        match e.clone() {
            Entry::E(mi_c, _ty, Decl::Hole)
                if [mi_a, mi_b].contains(&mi_c) && entries.fmvs().contains(&mi_c) =>
            {
                self.push_l(e)?;
                self.push_ls(entries)?;
                self.block(id, Problem::Unify(equation))
            }
            Entry::E(mi_c, ty, Decl::Hole) if mi_c == mi_a => {
                self.push_ls(entries)?;
                if !self.try_invert(id, equation.clone(), ty)? {
                    self.flex_term(vec![e], id, equation.clone().sym())?;
                }
                Ok(())
            }
            Entry::E(mi_c, ty, Decl::Hole) if mi_c == mi_b => {
                if !self.try_invert(id, equation.clone().sym(), ty)? {
                    self.flex_term(vec![e], id, equation.clone())?;
                }
                Ok(())
            }
            Entry::E(mi_c, _ty, Decl::Hole)
                if (&(&ctx.fmvs() | &entries.fmvs()) | &equation.fmvs()).contains(&mi_c) =>
            {
                entries.insert(0, e);
                self.flex_flex(entries, id, equation)
            }
            _ => {
                self.push_r(Right(e))?;
                self.flex_flex(entries, id, equation)
            }
        }
    }

    /*
    > invert ::  Nom -> Type -> Bwd Elim -> Tm -> Contextual (Maybe Tm)
    > invert alpha _T e t  | occurCheck True alpha t = throwError "occur check"
    >                      | alpha `notMember` fmvs t, Just xs <- toVars e, linearOn t xs = do
    >                          b <- local (const B0) (typecheck _T (lams xs t))
    >                          return $ if b then Just (lams xs t) else Nothing
    >                      | otherwise = return Nothing

     */
    fn invert(&mut self, mi: MI, ty: &Term, es: &[Elim], t: &Term) -> Result<Option<Term>> {
        /*
        > linearOn :: Tm -> Bwd Nom -> Bool
        > linearOn _  B0       = True
        > linearOn t  (as:<a)  = not (a `elem` fvs t && a `elem` as) && linearOn t as
         */
        fn is_linear_on(t: &Term, vars: &[Var]) -> bool {
            let fvs = t.fvs();
            for fv in fvs {
                let mut occurred = false;
                for v in vars {
                    if *v == fv {
                        if occurred {
                            return false;
                        }
                        occurred = true;
                    }
                }
            }
            return true;
        }

        if occur_check(true, mi, t) {
            return Err(Error::Occurrence);
        }

        if let Some(xs) = to_vars(es.to_vec()) {
            let fmvs = t.fmvs();
            if !fmvs.contains(&mi) && is_linear_on(t, &xs) {
                let mut binds = vec![];
                for x in xs.iter().rev() {
                    binds.push(self.lookup2(*x).map_term(|x| x.clone().boxed()));
                }
                let lam = Term::lams(binds, t.clone());
                let b = self
                    .under_ctx2(Ctx::default(), |tcs| tcs.type_check(ty, &lam))
                    .is_ok();
                if b {
                    return Ok(Some(lam));
                }
            }
        }
        Ok(None)
    }

    /*
    > tryInvert ::  Equation -> Type -> Contextual Bool
    > tryInvert q@(EQNO (N (M alpha) e) s) _T = invert alpha _T e s >>= \ m -> case m of
    >         Nothing  ->  return False
    >         Just v   ->  do  active (Unify q)
    >                          define B0 alpha _T v
    >                          return True


     */
    fn try_invert(&mut self, id: Id, equation: Equation, ty: Term) -> Result<bool> {
        let Equation {
            tm1: Term::Meta(mi, es),
            ty1,
            tm2: s,
            ty2,
        } = equation.clone() else {
            panic!("try_invert: equation is not a meta equation");
        };
        match self.invert(mi, &ty, &es, &s)? {
            None => Ok(false),
            Some(v) => {
                self.active(id, Problem::Unify(equation))?;
                self.define(Default::default(), mi, ty, v)?;
                Ok(true)
            }
        }
    }

    /*
    > intersect ::  Telescope -> Bwd Elim -> Bwd Elim -> Maybe Telescope
    > intersect B0                 B0          B0           = return B0
    > intersect (_Tel :< (z, _S))  (e :< A s)  (e' :< A t)  = do
    >     _Tel'  <- intersect _Tel e e'
    >     x      <- toVar s
    >     y      <- toVar t
    >     if x == y then return (_Tel' :< (z, _S)) else return _Tel'
    > intersect _ _ _ = Nothing


     */
    fn intersect(&mut self, mut tele: Tele, es1: &[Elim], es2: &[Elim]) -> Option<Tele> {
        let bind = tele.0.pop();
        match (bind, es1, es2) {
            (Some(bind), [es1 @ .., Elim::App(a1)], [es2 @ .., Elim::App(a2)]) => {
                let mut tele = self.intersect(tele, es1, es2)?;
                let x = a1.clone().to_var();
                let y = a2.clone().to_var();
                if x == y {
                    tele.0.push(bind);
                }
                return Some(tele);
            }
            _ => None,
        }
    }

    /*
    > tryPrune ::  Equation -> Contextual Bool
    > tryPrune q@(EQNO (N (M alpha) e) t) = pruneTm (fvs e) t >>= \ u ->  case u of
    >         d:_  -> active (Unify q) >> instantiate d >> return True
    >         []   -> return False

    */
    fn try_prune(&mut self, id: Id, equation: Equation) -> Result<bool, Error> {
        let Equation {
            tm1: Term::Meta(mi, ds),
            ty1,
            tm2: t,
            ty2,
        } = equation.clone() else {
            panic!("try_prune: not a meta");
        };
        let mut u = self.prune_tm(ds.fvs(), t)?;

        if u.is_empty() {
            return Ok(false);
        }
        let d = u.remove(0);
        self.active(id, Problem::Unify(equation))?;
        self.instantiate(d)?;
        Ok(true)
    }

    /*
    > pruneUnder :: Set Nom -> Bind Nom Tm -> Contextual [Instantiation]
    > pruneUnder _Vs b = do  (x, t) <- unbind b
    >                        pruneTm (_Vs `union` singleton x) t

     */
    fn prune_under(&mut self, vs: HashSet<Var>, b: Closure) -> Result<Vec<Instantiation>> {
        let t = b.into_inner();
        let mut vs = vs;
        vs.insert(Var::Bound(0));
        self.prune_tm(vs, t)
    }

    /*
    > pruneElims :: Set Nom -> Bwd Elim -> Contextual [Instantiation]
    > pruneElims _Vs e = fold <$> traverse pruneElim e
    >   where
    >     pruneElim (A a)        = pruneTm _Vs a
    >     pruneElim (If _T s t)  = (++) <$> ((++)  <$> pruneTm _Vs s <*> pruneTm _Vs t)
    >                                                  <*> pruneUnder _Vs _T
    >     pruneElim _            = return []

     */
    fn prune_elims(&mut self, vs: HashSet<Var>, es: Vec<Elim>) -> Result<Vec<Instantiation>> {
        let mut res = vec![];
        for e in es {
            match e {
                Elim::App(a) => {
                    res.extend(self.prune_tm(vs.clone(), *a)?);
                }
                _ => {}
            }
        }
        Ok(res)
    }

    /*
    > pruneMeta :: Set Nom -> Nom -> Bwd Elim -> Contextual [Instantiation]
    > pruneMeta _Vs beta e = do
    >     (_Tel, _T) <- telescope =<< lookupMeta beta
    >     case prune _Vs _Tel e of
    >         Just _Tel'  | _Tel' /= _Tel, fvs _T `isSubsetOf` vars _Tel'
    >                         -> return [(beta, _Pis _Tel' _T, \ beta' -> lams' _Tel (beta' $*$ _Tel'))]
    >         _               -> return []

     */
    fn prune_meta(
        &mut self,
        vs: HashSet<Var>,
        mi: MI,
        es: Vec<Elim>,
    ) -> Result<Vec<Instantiation>> {
        let t = self.lookup_meta_ctx(mi)?;
        let (tel, ty) = t.tele_view();
        match self.prune(vs.clone(), tel.clone(), es) {
            Some(tel2) if tel2 != tel => {
                let vars = tel2.vars();
                if is_subset_of(ty.fvs(), vars.clone().into_iter().collect()) {
                    Ok(vec![(
                        mi,
                        Term::pis(tel2.clone(), ty),
                        Box::new(move |mi2: Term| {
                            Term::lams(
                                tel,
                                mi2.apply(
                                    vars.clone()
                                        .into_iter()
                                        .map(|x| Term::Var(x, vec![]))
                                        .collect(),
                                ),
                            )
                        }),
                    )])
                } else {
                    Ok(vec![])
                }
            }
            _ => Ok(vec![]),
        }
    }

    /*
    > prune :: Set Nom -> Telescope -> Bwd Elim -> Maybe Telescope
    > prune _Vs B0                 B0          = Just B0
    > prune _Vs (_Del :< (x, _S))  (e :< A s)  = do
    >     _Del' <- prune _Vs _Del e
    >     case toVar s of
    >       Just y  | y `member` _Vs, fvs _S `isSubsetOf` vars _Del'  -> Just (_Del' :< (x, _S))
    >       _       | fvrigs s `notSubsetOf` _Vs                      -> Just _Del'
    >               | otherwise                                       -> Nothing
    > prune _ _ _ = Nothing


    */
    fn prune(&mut self, vs: HashSet<Var>, tel: Tele, es: Vec<Elim>) -> Option<Tele> {
        let mut tel = tel;
        let mut es = es;
        if es.is_empty() && tel.is_empty() {
            return Some(Tele::default());
        }
        let bind = tel.0.pop()?;
        let Elim::App(s) = es.pop()? else {
            return None;
        };
        let mut tel2 = self.prune(vs.clone(), tel, es)?;
        match s.clone().to_var() {
            Some(y)
                if vs.contains(&Var::Bound(y))
                    && is_subset_of(s.fvs(), tel2.vars().into_iter().collect()) =>
            {
                tel2.0.push(bind);
                Some(tel2)
            }
            _ if !is_subset_of(s.fvrigs(), vs) => Some(tel2),
            _ => None,
        }
    }

    /*
    > pruneTm ::  Set Nom -> Tm -> Contextual [Instantiation]
    > pruneTm _Vs (Pi _S _T)      = (++) <$> pruneTm _Vs _S  <*> pruneUnder _Vs _T
    > pruneTm _Vs (Sig _S _T)     = (++) <$> pruneTm _Vs _S  <*> pruneUnder _Vs _T
    > pruneTm _Vs (PAIR s t)      = (++) <$> pruneTm _Vs s   <*> pruneTm _Vs t
    > pruneTm _Vs (L b)           = pruneUnder _Vs b
    > pruneTm _Vs (N (M beta) e)  = pruneMeta _Vs beta e
    > pruneTm _Vs (C _)           = return []
    > pruneTm _Vs (N (V z _) e)   | z `member` _Vs    = pruneElims _Vs e
    >                             | otherwise         = throwError "pruning error"

     */
    fn prune_tm(&mut self, vs: HashSet<Var>, t: Term) -> Result<Vec<Instantiation>> {
        match t.clone() {
            Term::Universe(_) => Ok(Vec::new()),
            Term::Pi(a, b) => {
                let a_ty = *a.ty;
                let mut u = self.prune_tm(vs.clone(), a_ty)?;
                let v = self.prune_under(vs, b)?;
                u.extend(v);
                Ok(u)
            }
            Term::Lam(lam) => {
                let body = lam.1;
                let v = self.prune_under(vs.clone(), body)?;
                Ok(v)
            }
            Term::Meta(mi, es) => self.prune_meta(vs.clone(), mi, es),
            Term::Var(z, es) => {
                if vs.contains(&z) {
                    self.prune_elims(vs.clone(), es)
                } else {
                    panic!("pruning error")
                }
            }
            t => {
                unimplemented!("prune_tm: {:?}", t)
            }
        }
    }

    /*
    > instantiate :: Instantiation -> Contextual ()
    > instantiate d@(alpha, _T, f) = popL >>= \ e -> case e of
    >       E beta (_U, HOLE)  | alpha == beta  ->  hole B0 _T (\ t -> define B0 beta _U (f t))
    >       _                                   ->  do  pushR (Right e)
    >                                                   instantiate d


     */
    fn instantiate(&mut self, (mi, ty, f): Instantiation) -> Result<()> {
        let e = self.pop_l()?;
        match e {
            Entry::E(mi2, ty2, Decl::Hole) if mi == mi2 => {
                self.hole(Default::default(), ty, |tcs, t| {
                    tcs.define(Default::default(), mi2, ty2, f(t))
                })
            }
            _ => {
                self.push_r(Right(e))?;
                self.instantiate((mi, ty, f))
            }
        }
    }

    /*
    > equaliseN ::  Head -> Bwd Elim -> Head -> Bwd Elim ->
    >                   Contextual (Head, Bwd Elim, Type)
    > equaliseN h B0 h' B0 | h == h'          = (h, B0,) <$> infer h

    > equaliseN h (e :< A s)  h' (e' :< A t)  = do
    >     (h'', e'', Pi _U _V)  <- equaliseN h e h' e'
    >     u                     <- equalise _U s t
    >     return (h'', e'' :< A u, inst _V u)

    > equaliseN h (e :< Hd)   h' (e' :< Hd)   = do
    >     (h'', e'', Sig _U _V) <- equaliseN h e h' e'
    >     return (h'', e'' :< Hd, _U)
    > equaliseN h (e :< Tl)   h' (e' :< Tl)   = do
    >     (h'', e'', Sig _U _V) <- equaliseN h e h' e'
    >     return (h'', e'' :< Tl, inst _V (N h'' (e'' :< Hd)))
    > equaliseN h (e :< If _T u v) h' (e' :< If _T' u' v') = do
    >     (h'', e'', BOOL)  <- equaliseN h e h' e'
    >     _U''              <- bindsInScope BOOL _T _T' (\ x _U _U' -> equalise TYPE _U _U')
    >     u''               <- equalise (inst _U'' TT) u u'
    >     v''               <- equalise (inst _U'' FF) v v'
    >     return (h'', e'' :< If _U'' u'' v'', inst _U'' (N h'' e''))
     */
    fn equalise_n(
        &mut self,
        v: &Var,
        es: Vec<Elim>,
        v2: &Var,
        es2: Vec<Elim>,
    ) -> Result<(Var, Vec<Elim>, Type)> {
        match (v, es, v2, es2) {
            (v, es, v2, es2) if v == v2 && es.is_empty() && es2.is_empty() => {
                Ok((v.clone(), es, self.lookup2(v.clone()).ty.clone()))
            }
            (v, mut es, v2, mut es2) if !es.is_empty() && !es2.is_empty() => {
                let Elim::App(s) = es.pop().unwrap() else {
                    panic!("equalise_n: expected app elim");
                };
                let Elim::App(t) = es2.pop().unwrap() else {
                    panic!("equalise_n: expected app elim");
                };
                let (v3, mut es3, Type::Pi(u_, v_)) = self.equalise_n(v, es.clone(), v2, es2)? else {
                    panic!("equalise_n: expected pi type");
                };
                // TODO: check pi binder type
                let u = self.equalise(&u_.ty, &*s, &*t)?;
                es3.push(Elim::app(u));
                Ok((v3, es3, v_.into_inner()))
            }
            (v, es, v2, es2) => {
                unimplemented!("equalise_n: {:?} {:?} {:?} {:?}", v, es, v2, es2)
            }
        }
    }

    /*
    > equalise :: Type -> Tm -> Tm -> Contextual Tm
    > equalise TYPE  SET   SET   = return SET
    > equalise TYPE  _S    _T    = equalise SET _S _T
    > equalise SET   BOOL  BOOL  = return BOOL
    > equalise BOOL  TT    TT    = return TT
    > equalise BOOL  FF    FF    = return FF
    > equalise SET   (Pi _A _B) (Pi _S _T) = do
    >     _U <- equalise SET _A _S
    >     Pi _U <$>   bindsInScope _U _B _T
    >                    (\ x _B' _T' -> equalise SET _B' _T')
    > equalise (Pi _U _V) f g =
    >     L <$>  bindInScope _U _V
    >                (\ x _V' -> equalise _V' (f $$ var x) (g $$ var x))
    > equalise SET (Sig _A _B) (Sig _S _T) = do
    >     _U <- equalise SET _A _S
    >     Sig _U <$>  bindsInScope _U _B _T
    >                    (\ x _B' _T' -> equalise SET _B' _T')
    > equalise (Sig _U _V) s t = do
    >     u0 <- equalise _U (hd s) (hd t)
    >     u1 <- equalise (inst _V u0) (tl s) (tl t)
    >     return (PAIR u0 u1)
    > equalise _U (N h e) (N h' e') = do
    >     (h'', e'', _V) <- equaliseN h e h' e'
    >     equalise TYPE _U _V
    >     return (N h'' e'')
     */
    fn equalise(&mut self, ty: &Type, s: &Term, t: &Term) -> Result<Term> {
        match (ty, s, t) {
            (Term::Universe(_), Term::Universe(_), Term::Universe(_)) => {
                Ok(Term::Universe(Universe(0)))
            }
            (Term::Universe(_), Term::Pi(a, b), Term::Pi(s, t)) => {
                let u = self.equalise(&Term::Universe(Universe(0)), &*a.ty, &*s.ty)?;
                let bind_a = a.clone().map_term(|_| u.clone().boxed());
                let b =
                    self.binds_in_scope(a.clone().map_term(|_| u.clone()), b, t, |tcs, b, t| {
                        tcs.equalise(&Term::Universe(Universe(0)), &b, &t)
                    })?;
                Ok(Term::Pi(bind_a, b))
            }
            (Term::Pi(a, b), f, g) => {
                let b = self.bind_in_scope(a.clone().map_term(|x| *x), b, |tcs, b| {
                    // TODO: check lambda binder type
                    let f_body = f.to_lam().1.as_inner();
                    let g_body = g.to_lam().1.as_inner();
                    tcs.equalise(&b, &f_body, &g_body)
                })?;
                Ok(Term::lam(a.clone(), b.into_inner()))
            }
            (ty, Term::Var(v, es), Term::Var(v2, es2)) => {
                let (v3, es3, ty2) = self.equalise_n(v, es.clone(), v2, es2.clone())?;
                self.equalise(&Type::universe(Universe(0)), ty, &ty2)?;
                Ok(Term::Var(v3, es3))
            }
            (ty, Term::Meta(v, es), Term::Meta(v2, es2)) => self.equalise(
                ty,
                &Term::Var(Var::Meta(*v), es.clone()),
                &Term::Var(Var::Meta(*v2), es2.clone()),
            ),
            (ty, t, u) => {
                unimplemented!("equalise {:?} {:?} {:?}", ty, t, u);
            }
        }
    }

    fn bind_in_scope(
        &mut self,
        x: Bind,
        b: &Closure,
        f: impl Fn(&mut Self, &Term) -> Result<Term, Error>,
    ) -> Result<Closure> {
        self.gamma.push(x.clone());
        self.gamma2.push(x.clone().map_term(Param::P));
        let Closure::Plain(bb) = &b;
        let res = f(self, &*bb);
        self.gamma2.pop();
        self.gamma.pop();
        res.map(|b| Closure::plain(b))
    }

    fn binds_in_scope(
        &mut self,
        x: Bind,
        b: &Closure,
        t: &Closure,
        f: impl Fn(&mut Self, &Term, &Term) -> Result<Term, Error>,
    ) -> Result<Closure> {
        self.gamma.push(x.clone());
        self.gamma2.push(x.clone().map_term(Param::P));
        let Closure::Plain(bb) = &b;
        let Closure::Plain(tt) = &t;
        let res = f(self, &*bb, &*tt);
        self.gamma2.pop();
        self.gamma.pop();
        res.map(|b| Closure::plain(b))
    }

    /*
    > equal :: Type -> Tm -> Tm -> Contextual Bool
    > equal _T s t =  (equalise _T s t >> return True) <|> (return False)
    >
    > typecheck :: Type -> Tm -> Contextual Bool
    > typecheck _T t = equal _T t t
     */
    fn equal(&mut self, ty: &Term, s: &Term, t: &Term) -> Result<bool> {
        match self.equalise(ty, s, t) {
            Ok(_) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    fn type_check(&mut self, ty: &Term, t: &Term) -> Result<bool> {
        self.equal(ty, t, t)
    }

    /*
    > isReflexive :: Equation -> Contextual Bool
    > isReflexive (EQN _S s _T t) =  optional (equalise TYPE _S _T) >>=
    >                                    maybe (return False) (\ _U -> equal _U s t)

     */
    fn is_reflexive(&mut self, eq: &Equation) -> Result<bool, Error> {
        match self.equalise(&Term::universe(Universe(0)), &eq.ty1, &eq.ty2) {
            Ok(u) => self.equal(&u, &eq.tm1, &eq.tm2),
            Err(_) => Ok(false),
        }
    }

    /*
    > solver :: Problem -> Contextual ()
    > solver (Unify q) = do  b <- isReflexive q
    >                        unless b (unify q)
    > solver (All p b) = do
    >     (x, q)  <- unbind b
    >     case p of
    >         _ |  x `notElem` fvs q -> active q
    >         P _S         -> splitSig B0 x _S >>= \ m -> case m of
    >             Just (y, _A, z, _B, s, _)  -> solver (allProb y _A  (allProb z _B (subst x s q)))
    >             Nothing                    -> inScope x (P _S) $ solver q
    >         Twins _S _T  -> equal SET _S _T >>= \ c ->
    >             if c  then  solver (allProb x _S (subst x (var x) q))
    >                   else  inScope x (Twins _S _T) $ solver q


     */
    fn solver(&mut self, id: Id, p: Problem) -> Result<(), Error> {
        match p {
            Problem::Unify(q) => {
                if self.is_reflexive(&q)? {
                    println!("Solved {:?}", q);
                    Ok(())
                    // self.solved(id, q)
                } else {
                    if let Err(e) = self.unify(id, q.clone()) {
                        panic!("failed: {:?}", q);
                        // self.failed(id, q)?;
                    }
                    Ok(())
                }
            }
            Problem::All(p, b) => {
                let q = *b.clone(); // TODO: lower?
                let fv_q = q.fvs();
                if !fv_q.contains(&Var::Bound(0)) {
                    self.active(id, q)
                } else {
                    match p.ty.clone() {
                        Param::P(s_ty) => {
                            let m = self.split_sig(Tele::default(), s_ty.clone())?;
                            match m {
                                Some((y, a, z, bb, s, _)) => {
                                    let problem = q.subst_with(Substitution::one(s), self); // x(p) := s
                                    self.solver(
                                        id,
                                        Problem::alls(
                                            vec![
                                                Bind::unnamed(Param::P(a.clone())),
                                                Bind::unnamed(Param::P(bb.clone())),
                                            ],
                                            problem,
                                        ),
                                    )
                                }
                                None => {
                                    let mut ctx = self.gamma2.clone();
                                    ctx.push(p);
                                    self.under_ctx2(ctx, |tcs| tcs.solver(id, q))
                                }
                            }
                        }
                        Param::Twins(s_ty, t_ty) => {
                            let c = self.equal(&Term::Universe(Universe(0)), &s_ty, &t_ty)?;
                            if c {
                                self.solver(id, Problem::All(p, q.boxed()))
                            } else {
                                let mut ctx = self.gamma2.clone();
                                ctx.push(p);
                                self.under_ctx2(ctx, |tcs| tcs.solver(id, q))
                            }
                        }
                    }
                }
            }
        }
    }

    fn lookup_meta_ctx(&self, x: MI) -> Result<Term> {
        let l = &self.meta_ctx2.0;
        l.iter()
            .filter_map(|e| match e {
                Entry::E(y, t, _) if x == *y => Some(t.clone()),
                _ => None,
            })
            .next()
            .ok_or_else(|| panic!())
    }

    /*
    > lower :: Telescope -> Nom -> Type -> Contextual Bool
    > lower _Phi alpha (Sig _S _T) =  hole _Phi _S $ \ s ->
    >                                 hole _Phi (inst _T s) $ \ t ->
    >                                 define _Phi alpha (Sig _S _T) (PAIR s t) >>
    >                                 return True
    >
    > lower _Phi alpha (Pi _S _T) = do  x <- fresh (s2n "x")
    >                                   splitSig B0 x _S >>= maybe
    >                                       (lower (_Phi :< (x, _S)) alpha (inst _T (var x)))
    >                                       (\ (y, _A, z, _B, s, (u, v)) ->
    >                                           hole _Phi (_Pi y _A  (_Pi z _B (inst _T s))) $ \ w ->
    >                                           define _Phi alpha (Pi _S _T) (lam x (w $$ u $$ v)) >>
    >                                           return True)
    >
    > lower _Phi alpha _T = return False


     */
    fn lower(&mut self, tele: Tele, mi: MI, term: Term) -> Result<bool, Error> {
        match term {
            Term::Pi(a, b) => {
                let m = self.split_sig(Tele::default(), *a.ty.clone())?;
                match m {
                    Some((y, aa, z, bb, s, (u, v))) => {
                        let t = Term::pis(
                            vec![Bind::unnamed(aa.clone()), Bind::unnamed(bb)],
                            b.clone().instantiate_with(s, self),
                        );
                        self.hole(tele.clone(), t, |tcs, w| {
                            tcs.define(
                                tele,
                                mi,
                                Term::Pi(a.clone(), b),
                                Term::lam(a.clone(), w.apply(vec![u]).apply(vec![v])),
                            )?;
                            Ok(true)
                        })
                    }
                    None => {
                        let mut tel = tele.clone();
                        tel.0.push(a.clone().map_term(|x| *x));
                        self.lower(tel, mi, b.into_inner())
                    }
                }
            }
            _ => Ok(false),
        }
    }

    /*
    > splitSig ::  Telescope -> Nom -> Type ->
    >                  Contextual (Maybe  (Nom, Type, Nom, Type, Tm, (Tm, Tm)))
    > splitSig _Phi x (Sig _S _T)  = do  y  <- fresh (s2n "y")
    >                                    z  <- fresh (s2n "z")
    >                                    return $ Just  (y, _Pis _Phi _S, z, _Pis _Phi (inst _T (var y $*$ _Phi)),
    >                                                   lams' _Phi (PAIR (var y $*$ _Phi) (var z $*$ _Phi)),
    >                                                   (lams' _Phi (var x $*$ _Phi %% Hd),
    >                                                        lams' _Phi (var x $*$ _Phi %% Tl)))
    > splitSig _Phi x (Pi _A _B)   = do  a <- fresh (s2n "a")
    >                                    splitSig (_Phi :< (a, _A)) x (inst _B (var a))
    > splitSig _ _ _ = return Nothing


     */
    fn split_sig(
        &mut self,
        mut tele: Tele,
        // x: Var,
        term: Term,
    ) -> Result<Option<(Var, Term, Var, Term, Term, (Term, Term))>> {
        match term {
            Term::Pi(a, b) => {
                tele.0.push(a.clone().map_term(|x| *x));
                self.split_sig(tele, b.into_inner())
            }
            _ => Ok(None),
        }
    }

    /*
    > ambulando :: Subs -> Contextual ()
    > ambulando theta = optional popR >>= \ x -> case x of
    >  Nothing             -> return ()
    >  Just (Left theta')  -> ambulando (theta *%* theta')
    >  Just (Right e)      -> case update theta e of
    >     e'@(E alpha (_T, HOLE))   ->  do  lower B0 alpha _T <|| pushL e'
    >                                       ambulando theta
    >     Q Active p                ->  do  pushR (Left theta)
    >                                       solver p
    >                                       ambulando []
    >     e'                        ->  do  pushL e'
    >                                       ambulando theta


     */
    fn ambulando(&mut self, subst: MetaSubst) -> Result<(), Error> {
        let Ok(x) = self.pop_r() else {
            return Ok(());
        };
        match x {
            Left(theta0) => {
                let mut composed = subst.clone();
                composed.extend(theta0);
                self.ambulando(composed)
            }
            Right(e) => match self.update(subst.clone(), e) {
                Entry::E(mi, term, Decl::Hole) => {
                    if !self.lower(Tele::default(), mi, term.clone())? {
                        self.push_l(Entry::E(mi, term, Decl::Hole))?;
                    }
                    self.ambulando(subst)
                }
                Entry::Q(Status::Active, p) => {
                    self.push_r(Left(subst))?;
                    let id = 0; // TODO: change ID
                    self.solver(id, p)?;
                    self.ambulando(MetaSubst::default())
                }
                e => {
                    self.push_l(e)?;
                    self.ambulando(subst)
                }
            },
        }
    }

    /*
    > update :: Subs -> Entry -> Entry
    > update theta (Q s p) = Q s' p'
    >   where  p'  = substs theta p
    >          s'  | p == p'    = s
    >              | otherwise  = Active
    > update theta e = substs theta e


     */
    fn update(&mut self, subst: MetaSubst, mut e: Entry) -> Entry {
        match e {
            Entry::Q(s, p) => {
                let mut p0 = p.clone();
                p0.meta_subst(&subst);
                let s0 = if p == p0 { s } else { Status::Active };
                Entry::Q(s0, p0)
            }
            _ => {
                e.meta_subst(&subst);
                e
            }
        }
    }

    fn push_l(&mut self, e: Entry) -> Result<()> {
        self.meta_ctx2.0.push(e);
        Ok(())
    }

    fn push_ls(&mut self, es: Vec<Entry>) -> Result<()> {
        self.meta_ctx2.0.extend(es);
        Ok(())
    }

    fn push_r(&mut self, e: Either<MetaSubst, Entry>) -> Result<()> {
        self.meta_ctx2.1.push(e);
        Ok(())
    }

    fn pop_l(&mut self) -> Result<Entry> {
        self.meta_ctx2.0.pop().ok_or_else(|| panic!())
    }

    fn pop_r(&mut self) -> Result<Either<MetaSubst, Entry>> {
        self.meta_ctx2.1.pop().ok_or_else(|| panic!())
    }

    fn postpone(&mut self, status: Status, problem: Problem) -> Result<()> {
        let wrapped_problem = self
            .gamma2
            .clone()
            .into_iter()
            .fold(problem, |problem, bind| Problem::All(bind, problem.boxed()));
        self.push_r(Right(Entry::Q(status, wrapped_problem)))
    }

    fn block(&mut self, _id: Id, problem: Problem) -> Result<()> {
        self.postpone(Status::Blocked, problem)
    }

    fn active(&mut self, _id: Id, problem: Problem) -> Result<()> {
        self.postpone(Status::Active, problem)
    }

    /*
    > hole :: Telescope -> Type -> (Tm -> Contextual a) -> Contextual a
    > hole _Gam _T f = do  alpha <- fresh (s2n "alpha")
    >                      pushL $ E alpha (_Pis _Gam _T, HOLE)
    >                      r <- f (meta alpha $*$ _Gam)
    >                      goLeft
    >                      return r

     */
    fn hole<T>(
        &mut self,
        tele: Tele,
        ty: Type,
        f: impl FnOnce(&mut Self, Term) -> Result<T>,
    ) -> Result<T> {
        let alpha = self.fresh_mi();
        self.push_l(Entry::E(alpha, Term::pis(tele.clone(), ty), Decl::Hole))?;
        let r = f(self, Term::Meta(alpha, tele.to_elims()))?;
        self.go_left()?;
        Ok(r)
    }

    fn fresh_mi(&mut self) -> MI {
        let mi = self.next_mi;
        self.next_mi = self.next_mi + 1;
        mi
    }

    /*
    > define :: Telescope -> Nom -> Type -> Tm -> Contextual ()
    > define _Gam alpha _S v = do  pushR $ Left [(alpha, t)]
    >                              pushR $ Right $ E alpha (_T, DEFN t)
    >   where  _T  = _Pis _Gam _S
    >          t   = lams' _Gam v

     */
    fn define(&mut self, tele: Tele, alpha: MI, ty: Type, v: Term) -> Result<()> {
        let tt = Term::pis(tele.clone(), ty);
        let t = Term::lams(tele, v);
        self.push_r(Left(vec![(alpha, t.clone())].into_iter().collect()))?;
        self.push_r(Right(Entry::E(alpha, tt, Decl::Defn(t))))?;
        Ok(())
    }

    /*
    > goLeft :: Contextual ()
    > goLeft = popL >>= pushR `o` Right
     */
    fn go_left(&mut self) -> Result<()> {
        let e = self.pop_l()?;
        self.push_r(Right(e))
    }
}

fn to_vars(params: Vec<Elim>) -> Option<Vec<Var>> {
    params
        .into_iter()
        .map(|t| match t {
            Elim::App(b) => match *b {
                Term::Var(v, args) if args.is_empty() => Some(v),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

// a ∈ b
fn is_subset_of(a: HashSet<Var>, b: HashSet<Var>) -> bool {
    a.iter().all(|x| b.contains(x))
}
