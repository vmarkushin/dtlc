use crate::syntax::core::dbi::DeBruijn;
use crate::syntax::core::redex::Subst;
use crate::syntax::core::Term;
use crate::syntax::{dbi_nat, dbi_pred, DBI};
use itertools::Either;
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::BuildHasher;
use std::rc::Rc;

pub type Substitution = PrimSubst<Term>;

/// Substitution type.
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.Syntax.Internal.html#Substitution%27).
#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum PrimSubst<T> {
    /// The identity substitution.
    /// $$
    /// \Gamma \vdash \text{IdS} : \Gamma
    /// $$
    IdS,
    Empty,
    /// The "add one more" substitution, or "substitution extension".
    /// $$
    /// \cfrac{\Gamma \vdash u : A \rho \quad \Gamma \vdash \rho : \Delta}
    /// {\Gamma \vdash \text{Cons}(u, \rho) : \Delta, A}
    /// $$
    Cons(T, Rc<Self>),
    /// Strengthening substitution.
    /// Apply this to a term which does not contain variable 0
    /// to lower all de Bruijn indices by one.
    /// $$
    /// \cfrac{\Gamma \vdash \rho : \Delta}
    /// {\Gamma \vdash \text{Succ} \rho : \Delta, A}
    /// $$
    Succ(Rc<Self>),
    /// Weakening substitution, lifts to an extended context.
    /// $$
    /// \cfrac{\Gamma \vdash \rho : \Delta}
    /// {\Gamma, \Psi \vdash \text{Weak}_\Psi \rho : \Delta}
    /// $$
    Weak(DBI, Rc<Self>),
    /// Lifting substitution. Use this to go under a binder.
    /// $\text{Lift}\_1 \rho := \text{Cons}(\texttt{Term::form\\\_dbi(0)},
    /// \text{Weak}\_1 \rho)$. $$
    /// \cfrac{\Gamma \vdash \rho : \Delta}
    /// {\Gamma, \Psi \rho \vdash \text{Lift}_\Psi \rho : \Delta, \Psi}
    /// $$
    Lift(DBI, Rc<Self>),
}

impl<T: Display> Display for PrimSubst<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            PrimSubst::IdS => write!(f, "ε"),
            PrimSubst::Cons(t, r) => write!(f, "Cons({}, {})", t, r),
            PrimSubst::Succ(r) => write!(f, "Succ({})", r),
            PrimSubst::Weak(dbi, r) => write!(f, "Weak({}, {})", dbi, r),
            PrimSubst::Lift(dbi, r) => write!(f, "Lift({}, {})", dbi, r),
            PrimSubst::Empty => write!(f, "⊥"),
        }
    }
}

impl<T> Default for PrimSubst<T> {
    fn default() -> Self {
        PrimSubst::IdS
    }
}

impl<Term: DeBruijn + Subst<Term, Term> + Clone> PrimSubst<Term> {
    pub fn lookup(&self, dbi: DBI) -> Term {
        self.lookup_impl(dbi).map_left(Clone::clone).into_inner()
    }

    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#raise).
    pub fn raise_term(k: DBI, term: Term) -> Term {
        Self::raise_from(0, k, term)
    }

    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#raiseFrom).
    pub fn raise_from(n: DBI, k: DBI, term: Term) -> Term {
        term.subst(Self::raise(k).lift_by(n))
    }

    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#composeS).
    pub fn compose(self: Rc<Self>, sgm: Rc<Self>) -> Rc<Self> {
        use PrimSubst::*;
        match (&*self, &*sgm) {
            (_, IdS) => self,
            (IdS, _) => sgm,
            (_, Weak(n, sgm)) => self.drop_by(*n).compose(sgm.clone()),
            (_, Cons(u, sgm)) => Rc::new(Cons(
                u.clone().subst(self.clone()),
                self.compose(sgm.clone()),
            )),
            (_, Succ(sgm)) => Rc::new(Succ(self.compose(sgm.clone()))),
            (_, Lift(0, _sgm)) => unreachable!(),
            (Cons(u, rho), Lift(n, sgm)) => Rc::new(Cons(
                u.clone(),
                rho.clone().compose(sgm.clone().lift_by(*n - 1)),
            )),
            (_, Lift(n, sgm)) => Rc::new(Cons(
                self.lookup(0),
                self.compose(sgm.clone().lift_by(*n - 1).weaken(1)),
            )),
            (_, Empty) => Empty.into(),
        }
    }

    /// If lookup failed, return the DBI.
    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#lookupS).
    pub fn lookup_impl(&self, dbi: DBI) -> Either<&Term, Term> {
        use Either::*;
        use PrimSubst::*;
        match self {
            IdS => Right(DeBruijn::from_dbi(dbi)),
            Cons(o, rest) => match dbi_nat(dbi) {
                None => Left(o),
                Some(dbi) => rest.lookup_impl(dbi),
            },
            Succ(rest) => rest.lookup_impl(dbi_pred(dbi)),
            Weak(i, rest) => match &**rest {
                IdS => Right(Term::from_dbi(dbi + *i)),
                rho => Right(rho.lookup(*i).subst(Self::raise(*i))),
            },
            Lift(n, _) if dbi < *n => Right(DeBruijn::from_dbi(dbi)),
            Lift(n, rest) => Right(Self::raise_term(*n, rest.lookup(dbi - *n))),
            Empty => panic!(),
        }
    }
}

impl<T> PrimSubst<T> {
    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#raiseS).
    pub fn raise(by: DBI) -> Rc<Self> {
        Self::weaken(Default::default(), by)
    }

    /// Lift a substitution under k binders.
    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#dropS).
    pub fn drop_by(self: Rc<Self>, drop_by: DBI) -> Rc<Self> {
        use PrimSubst::*;
        match (drop_by, &*self) {
            (0, _) => self,
            (n, IdS) => Self::raise(n),
            (n, Weak(m, rho)) => rho.clone().drop_by(n - 1).weaken(*m),
            (n, Cons(_, rho)) | (n, Succ(rho)) => rho.clone().drop_by(n - 1),
            (n, Lift(0, _rho)) => unreachable!("n = {:?}", n),
            (n, Lift(m, rho)) => rho.clone().lift_by(*m - 1).drop_by(n - 1).weaken(1),
            (_, Empty) => panic!(),
        }
    }

    /// Lift a substitution under k binders.
    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#liftS).
    pub fn lift_by(self: Rc<Self>, lift_by: DBI) -> Rc<Self> {
        use PrimSubst::*;
        match (lift_by, &*self) {
            (0, _) => self,
            (_, IdS) => Default::default(),
            (k, Lift(n, rho)) => Rc::new(Lift(*n + k, rho.clone())),
            (k, _) => Rc::new(Lift(k, self)),
        }
    }

    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#wkS).
    pub fn weaken(self: Rc<Self>, weaken_by: DBI) -> Rc<Self> {
        use PrimSubst::*;
        match (weaken_by, &*self) {
            (0, _) => self,
            (n, Weak(m, rho)) => Rc::new(Weak(n + *m, rho.clone())),
            (n, _) => Rc::new(Weak(n, self)),
        }
    }

    pub fn one(t: T) -> Rc<Self> {
        Rc::new(PrimSubst::Cons(t, Default::default()))
    }

    pub fn id() -> Rc<Self> {
        Rc::new(PrimSubst::IdS)
    }
}

impl<T: Clone> PrimSubst<T> {
    /// If Γ ⊢ ρ : Δ, Θ then splitS |Θ| ρ = (σ, δ), with
    ///    Γ ⊢ σ : Δ
    ///    Γ ⊢ δ : Θσ
    pub fn split(self: Rc<Self>, n: DBI) -> (Rc<Self>, Rc<Self>) {
        use PrimSubst::*;
        if n == 0 {
            return (self, Empty.into());
        }
        match &*self {
            Cons(u, rho) => {
                let x1 = rho.clone().split(n - 1);
                (x1.0, Rc::new(Cons(u.clone(), x1.1)))
            }
            Succ(rho) => {
                let x2 = rho.clone().split(n - 1);
                (x2.0, Succ(x2.1).into())
            }
            Lift(0, _) => {
                panic!()
            }
            Weak(m, rho) => {
                let x = rho.clone().split(n);
                (Self::weaken(x.0, *m), Self::weaken(x.1, *m))
            }
            IdS => (Self::raise(n), Self::lift_by(Rc::new(Empty), n)),
            Lift(m, rho) => {
                let x = rho.clone().lift_by(m - 1).split(n - 1);
                (Self::weaken(x.0, 1), Self::lift_by(x.1, 1))
            }
            Empty => {
                panic!()
            }
        }
    }

    pub fn union(self: Rc<Self>, other: Rc<Self>) -> Rc<Self> {
        use PrimSubst::*;
        // TODO: use helper functions for constructing new substs
        match &*other {
            IdS => self,
            Empty => self,
            Cons(t, o) => Cons(t.clone(), self.union(o.clone())).into(),
            Succ(x) => Succ(self.union(x.clone())).into(),
            Weak(v, x) => Weak(*v, self.union(x.clone())).into(),
            Lift(v, x) => Lift(*v, self.union(x.clone())).into(),
        }
    }
}

pub fn build_subst<H: BuildHasher>(map: HashMap<DBI, Term, H>, max: usize) -> Rc<Substitution> {
    Substitution::parallel(matched(map, max).into_iter())
}

/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Patterns.Match.html#matchedArgs).
fn matched<T, H: BuildHasher>(mut map: HashMap<DBI, T, H>, max: usize) -> Vec<T> {
    (0..max).map(|i| map.remove(&i).unwrap()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::core::{Case, Ctx, ValData};
    use crate::syntax::pattern::Pat;
    use crate::syntax::{ConHead, Ident, Loc};

    #[test]
    fn test_union() {
        let s1 = Substitution::one(Term::from_dbi(0));
        let s2 = Substitution::one(Term::from_dbi(1));

        assert_eq!(
            s1.union(s2),
            Substitution::one(Term::from_dbi(0)).cons(Term::from_dbi(1))
        );
    }

    #[test]
    fn test_split_subst() {
        let x = 1;
        let t = Term::mat_elim(
            x,
            vec![Case::new(
                Pat::cons(
                    ConHead::new(Ident::new("C", Loc::default()), 4),
                    vec![Pat::Var(2), Pat::Var(1)],
                ),
                Term::from_dbi(3).apply(vec![
                    Term::from_dbi(2),
                    Term::from_dbi(1),
                    Term::from_dbi(0),
                ]),
            )],
        );
        let Γ = Ctx(vec![
            (2, Term::data(ValData::new(0, vec![]))),
            (1, Term::data(ValData::new(1, vec![]))),
            (0, Term::data(ValData::new(2, vec![]))),
        ]
        .into_iter()
        .map(From::from)
        .collect());
        debug!("Γ = {}", Γ);
        debug!("{}", t);

        let Γ_new = Ctx(vec![
            (2, Term::data(ValData::new(0, vec![]))),
            (4, Term::data(ValData::new(3, vec![]))),
            (3, Term::data(ValData::new(4, vec![]))),
            (0, Term::data(ValData::new(2, vec![]))),
        ]
        .into_iter()
        .map(From::from)
        .collect());

        debug!("Γ' = {}", Γ_new);
        let σ = build_subst(
            vec![
                (0, Term::meta(0, vec![])),
                (1, Term::from_dbi(1)),
                (2, Term::meta(2, vec![])),
            ]
            .into_iter()
            .collect::<HashMap<_, _>>(),
            3,
        );
        debug!("σ = {}", σ);
        let (ρ, τ) = σ.split(x);
        debug!("ρ = {}, τ = {}", ρ, τ);
        let α = ρ.drop_by(1).lift_by(2).union(τ);
        debug!("ρ ⊎ τ = α = {}", α);
        debug!("{}", t.subst(α));
        // Γ = (a : A) (b : B) (c : C)
        //      2       1       0
        // σ = { 0 := x, 1 := y, 2 := z }
        // match b {
        //     | C i j => ...
        // }
        // Γ' = (a : A) (i : Ba) (j : Bb) (c : C)
        //       3       2        1        0
        // σ -- BROKEN
    }
}
