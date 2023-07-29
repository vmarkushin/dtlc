use crate::check::TypeCheckState;
use crate::syntax::core::dbi::DeBruijn;
use crate::syntax::core::redex::Subst;
use crate::syntax::core::{SubstWith, Term};
use crate::syntax::{dbi_nat, dbi_pred, DBI, UID};
use itertools::Either;
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::BuildHasher;
use std::rc::Rc;

pub type Substitution = PrimSubst<Term>;

/// Substitution type.
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.Syntax.Internal.html#Substitution%27).
#[derive(Clone, Debug, PartialEq, Eq)]
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

// impl<T: Display + PartialEq + Clone + DeBruijn + Subst<T, T>> Display for PrimSubst<T> {
//     fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
//         match self {
//             PrimSubst::IdS => write!(f, "id"),
//             PrimSubst::Weak(m, r) if **r == PrimSubst::IdS => write!(f, "wk{}", m),
//             PrimSubst::Empty => write!(f, "empty"),
//             rho => {
//                 let (rho1, rho2) = Rc::new(rho.clone()).split(1);
//                 let u = rho2.deref().lookup_impl(0);
//                 write!(f, "{}, {}", u, rho1)
//             }
//         }
//     }
// }

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
            (_, Empty) => Empty.into(),

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
        }
    }

    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#inplaceS).
    pub fn inplace(k: DBI, u: Term) -> Rc<Self> {
        Self::singleton(k, u).compose(PrimSubst::<Term>::raise(1).lift_by(k + 1))
    }

    /// If lookup failed, return the DBI.
    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#lookupS).
    pub fn lookup_impl(&self, i: DBI) -> Either<&Term, Term> {
        use Either::*;
        use PrimSubst::*;
        match self {
            IdS => Right(DeBruijn::from_dbi(i)),
            Weak(n, rest) => match &**rest {
                IdS => Right(Term::from_dbi(i + *n)),
                rho => Right(rho.lookup(i).subst(Self::raise(*n))),
            },
            Cons(o, rest) => match dbi_nat(i) {
                None => Left(o),
                Some(i) => rest.lookup_impl(i),
            },
            Succ(rest) => rest.lookup_impl(dbi_pred(i)),
            Lift(n, _) if i < *n => Right(DeBruijn::from_dbi(i)),
            Lift(n, rest) => Right(Self::raise_term(*n, rest.lookup(i - *n))),
            Empty => panic!(),
        }
    }
}

impl<'a> PrimSubst<Term> {
    pub fn raise_term_with(k: DBI, term: Term, tcs: &'a mut TypeCheckState) -> Term {
        Self::raise_from_with(0, k, term, tcs)
    }

    pub fn raise_from_with(n: DBI, k: DBI, term: Term, tcs: &'a mut TypeCheckState) -> Term {
        term.subst_with(Self::raise(k).lift_by(n), tcs)
    }

    pub fn lookup_with(&self, dbi: DBI, state: &'a mut TypeCheckState) -> Term {
        self.lookup_with_impl(dbi, state)
            .map_left(Clone::clone)
            .into_inner()
    }

    /// If lookup failed, return the DBI.
    pub fn lookup_with_impl(&self, i: DBI, state: &'a mut TypeCheckState) -> Either<&Term, Term> {
        use Either::*;
        use PrimSubst::*;
        match self {
            IdS => Right(DeBruijn::from_dbi(i)),
            Weak(n, rest) => match &**rest {
                IdS => Right(Term::from_dbi(i + *n)),
                rho => Right(rho.lookup_with(i, state).subst_with(Self::raise(*n), state)),
            },
            Cons(o, rest) => match dbi_nat(i) {
                None => Left(o),
                Some(i) => rest.lookup_with_impl(i, state),
            },
            Succ(rest) => rest.lookup_with_impl(dbi_pred(i), state),
            Lift(n, _) if i < *n => Right(DeBruijn::from_dbi(i)),
            Lift(n, rest) => {
                let term = rest.lookup_with(i - *n, state);
                let term1 = Self::raise_term_with(*n, term, state);
                Right(term1)
            }
            Empty => panic!(),
        }
    }
}

impl<T> PrimSubst<T> {
    pub fn strengthen(dbi: DBI) -> Rc<Self> {
        use PrimSubst::*;
        (0..dbi).fold(Self::id(), |rho, _i| Succ(rho).into())
    }

    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#raiseS).
    pub fn raise(by: DBI) -> Rc<Self> {
        Self::weaken(Default::default(), by)
    }

    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#dropS).
    pub fn drop_by(self: Rc<Self>, drop_by: DBI) -> Rc<Self> {
        use PrimSubst::*;
        match (drop_by, &*self) {
            (0, _) => self,
            (n, IdS) => Self::raise(n),
            (n, Weak(m, rho)) => rho.clone().drop_by(n).weaken(*m),
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
            (_n, Empty) => panic!(),
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
}

impl<T: Clone + DeBruijn> PrimSubst<T> {
    pub fn union(self: Rc<Self>, other: Rc<Self>) -> Rc<Self> {
        use PrimSubst::*;
        // TODO: use helper functions for constructing new substs
        match &*other {
            IdS => self,
            Empty => self,
            Cons(t, o) => self.union(o.clone()).cons(t.clone()),
            Succ(x) => Succ(self.union(x.clone())).into(),
            Weak(v, x) => self.union(x.clone()).weaken(*v),
            Lift(v, x) => self.union(x.clone()).lift_by(*v),
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

    use crate::syntax::core::{Bind, Case, Ctx, ValData};
    use crate::syntax::pattern::Pat;
    use crate::syntax::{ConHead, Ident};

    #[test]
    fn test_strengthening() {
        let term = Term::fun_app(0, "foo", [2, 1, 0, 5].map(Term::from_dbi));
        let x = 3;
        let s = Substitution::one(Term::from_dbi(4));
        let corr = Rc::new(Substitution::Lift(x, Substitution::strengthen(1)));
        let subst = corr.compose(s);
        assert_eq!(
            term.subst(subst),
            Term::fun_app(0, "foo", [1, 0, 3, 3].map(Term::from_dbi))
        );

        let term = Term::fun_app(0, "foo", [2, 1, 0].map(Term::from_dbi));
        let x = 3;
        let s = Substitution::one(Term::from_dbi(4)).lift_by(2);
        let corr = Rc::new(Substitution::Lift(x, Substitution::strengthen(1)));
        let subst = corr.compose(s);
        assert_eq!(
            term.subst(subst),
            Term::fun_app(0, "foo", [5, 1, 0].map(Term::from_dbi))
        );

        /*
        Γ = (w : W) (_ : T) (x : A) (y : B) (z : C)
        ?0 x@2
        {?0 := y'@2}
        match y@1 {
            Γ = (w : W) (_ : T) (x : A) (y' : B) (y'' : B) (z : C)
            cons @2 @1 => y'@2 x@3
        }



        Γ = (w : W) (_ : T) (x : A) (y : B) (z : C)
        [x := w]
        foo y@1 w@4
        match x@2 {
            Γ = (w : W) (_ : T) (x' : A) (x'' : A) (y : B) (z : C)
            | (cons x'@3 x''@2) => foo y@1 w@5
        }
        ==>
        Γ = (w : W) (_ : T) (y : B) (z : C)
        foo y@1 w@3
        match w@3 {
            Γ = (w' : W) (w'' : W) (_ : T) (y : B) (z : C)
            | (cons w'@4 w''@3) => foo y@1 (cons w'@4 w''@3)
        }

         */
        // \x \y \z \w -> x@3 y@2 z@1 w@0
        //
        // subst: cons @4, id
        //  v-------------------------(2)-- bar @4 @2 _  _  @0 <----<
        //  |      match @3 | cons @4 @3 => bar @5 @2 @4 @3 @0 -(1)-^
        //  |               | conz       => bar @3 @2 _  _  @0
        //  |
        //  |
        //  >-----------------------------> bar @3 @1 _  _  @4 -(3)-v
        //         match @2 | cons @3 @2 => bar @4 @1 @3 @2 @? <----<
        //                  | conz       => bar @_ @_ _  _  @_

        // subst: lift 2, cons @2, id
        //  v-------------------------(2)-- bar @4 @2 _  _  @1 <----<
        //  |      match @3 | cons @4 @3 => bar @5 @2 @4 @3 @1 -(1)-^
        //  |               | conz       => bar @3 @2 _  _  @1
        //  |
        //  |
        //  >-----------------------------> bar @4 @4 _  _  @1 -(3)-v
        //         match @2 | cons @3 @2 => bar @5 @5 @3 @2 @1 <----<
        //                  | conz       => bar @3 @3 _  _  @1

        // subst: cons @3, id
        //  v-------------------------(2)-- bar @3 @2 _  _  @0 <----<
        //  |      match @1 | cons @2 @1 => bar @4 @3 @2 @1 @0 -(1)-^
        //  |               | conz       => bar @2 @1 _  _  @0
        //  |
        //  |
        //  >-----------------------------> bar @2 @1 _  _  @3 -(3)-v
        //         match @0 | cons @1 @0 => bar @3 @2 @1 @0 @4 <----<
        //                  | conz       => bar @1 @0 _  _  @2

        // subst: cons @3, id
        //  v-------------------------(2)-- bar @3 @2 _  _  @0 <----<
        //  |      match @1 | cons @2 @1 => bar @4 @3 @2 @1 @0 -(1)-^
        //  |               | conz       => bar @2 @1 _  _  @0
        //  |
        //  |
        //  >-----------------------------> bar @2 @1 _  _  @3 -(3)-v
        //         match @0 | cons @2 @1 => bar @3 @0 @2 @1 @4 <----<
        //                  | conz       => bar @1 @0 _  _  @2
        //
        // (1) Lift the term into a new context where x is not yet eliminated and new variables
        //     are not introduced (?)
        // (2) Apply substitution
        // (3) Put into the context where y were eliminated and new variables introduced

        let term = Term::fun_app(0, "foo", [5, 2, 4, 3, 1].map(Term::from_dbi));
        let subst = Substitution::one(Term::from_dbi(2)).lift_by(2);
        let x = 3;
        let y = subst.lookup(x).dbi_view().unwrap();
        let _y_min = y;
        let _y_max = y + 1;

        println!("{}", term.clone().subst(subst.clone()));
        let (subst1, subst2) = subst.clone().split(x);
        let nsubst = subst1.drop_by(1).union(subst2);
        println!("split substitution {} => {}", subst, nsubst);

        // let corr = Substitution::strengthen(1).lift_by(y_max - y_min + 1);
        // let subst = Substitution::raise(1).cons(Term::from_dbi(3));
        // dsp!(&subst);
        // let (subst1, subst2) = subst.split(y_min);
        // dsp!(&subst1, &subst2);
        // let subst = corr.compose(subst1).union(subst2);
        // dsp!(&subst);
        // assert_eq!(
        //     dsp!(term.subst(subst)),
        //     Term::fun_app(0, "foo", [0, 2, 1, 4].map(Term::from_dbi))
        // );
    }

    #[test]
    fn test_subst() {
        // Γ = T U V
        //     ^
        // foo x y z
        //     0 1 2
        // y, Γ = T U
        // 0 -> 1

        // Γ = (w@3 : G) (z@2 : T) (y@1 : U) (x@0 : V)
        // λw. (λz. (λy. λx. foo x y z) w)
        //                       0 1 2
        // Γ = (w@2 : G) (z@1 : T) (x@0 : V)
        // λw. (λz. λx. foo x w z)
        //                  0 2 1
        // (λx. λy. _) y
        // [1 := 0]
        let term = Term::fun_app(0, "foo", [0, 1, 2].map(Term::from_dbi));
        println!("{}", term);
        let a = Term::from_dbi(1);
        let subst = Substitution::one(a).lift_by(1);
        println!("{}", subst);
        println!("{}", term.subst(subst));
    }

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
        let _ = env_logger::try_init();
        let x = 1;
        let t = Term::match_elim(
            x,
            vec![Case::new(
                Pat::cons(
                    ConHead::new(Ident::new("C"), 4),
                    vec![Pat::Var(2), Pat::Var(1)],
                ),
                Term::from_dbi(3).apply(vec![
                    Term::from_dbi(2),
                    Term::from_dbi(1),
                    Term::from_dbi(0),
                ]),
            )],
        );
        let Γ = Ctx::<Bind>(
            vec![
                (2, Term::data(ValData::new(0, vec![]))),
                (1, Term::data(ValData::new(1, vec![]))),
                (0, Term::data(ValData::new(2, vec![]))),
            ]
            .into_iter()
            .map(From::from)
            .collect(),
        );
        debug!("Γ = {}", Γ);
        debug!("{}", t);

        let Γ_new = Ctx::<Bind>(
            vec![
                (2, Term::data(ValData::new(0, vec![]))),
                (4, Term::data(ValData::new(3, vec![]))),
                (3, Term::data(ValData::new(4, vec![]))),
                (0, Term::data(ValData::new(2, vec![]))),
            ]
            .into_iter()
            .map(From::from)
            .collect(),
        );

        debug!("Γ' = {}", Γ_new);
        let σ = build_subst(
            vec![
                (0, Term::meta_with(0, vec![])),
                (1, Term::from_dbi(1)),
                (2, Term::meta_with(2, vec![])),
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
