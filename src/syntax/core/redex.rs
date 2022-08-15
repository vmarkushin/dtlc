use super::Term;
use crate::check::{Constraint, TypeCheckState};
use crate::dsp;
use crate::syntax::core::subst::{PrimSubst, Substitution};
use crate::syntax::core::term::Lambda;
use crate::syntax::core::{Case, Closure, DeBruijn, Elim, FoldVal, Func, Val, ValData, Var};
use crate::syntax::pattern::Pat;
use crate::syntax::{Bind, Ident, DBI, GI};
use itertools::Itertools;
use std::rc::Rc;

impl Term {
    /// Use `Term` instead of `Self` to emphasize that it's not `Elim`.
    pub fn apply(self, args: Vec<Term>) -> Self {
        self.apply_elim(args.into_iter().map(Elim::app).collect())
    }

    pub fn apply_elim(self, mut args: Vec<Elim>) -> Self {
        if args.is_empty() {
            return self;
        }
        match self {
            Term::Whnf(Val::Var(f, mut a)) => {
                a.append(&mut args);
                Term::Whnf(Val::Var(f, a))
            }
            Term::Whnf(Val::Meta(m, mut a)) => {
                a.append(&mut args);
                Term::meta(m, a)
            }
            Term::Whnf(Val::Lam(lam)) => Term::Redex(Func::Lam(lam), Ident::new("<λ>", 0..0), args),
            Term::Whnf(Val::Cons(c, mut a)) => {
                let mut iter = args.into_iter();
                match iter.next() {
                    None => Term::cons(c, a),
                    Some(Elim::App(arg)) => {
                        a.push(*arg);
                        Term::cons(c, a).apply_elim(iter.collect())
                    }
                    Some(Elim::Proj(_field)) => {
                        unimplemented!()
                    }
                }
            }
            Term::Redex(Func::Index(f), id, a) => def_app(f, id, a, args),
            Term::Redex(Func::Lam(lam), id, mut a) => {
                a.append(&mut args);
                Term::Redex(Func::Lam(lam), id, a)
            }
            e => panic!("Cannot eliminate `{}`.", e),
        }
    }

    fn subst_in_match_with_var(
        subst: &Rc<Substitution>,
        tcs: &mut TypeCheckState,
        x: &Box<Term>,
        y: DBI,
        cs: Vec<Case>,
    ) -> Vec<Case> {
        let x = x.dbi_view().expect("unexpected term");
        debug!("Replacing with var {} instead of {}...", y, x);
        /*
        When have such case-tree:
        match x { | cons ... => ... }
        Before entering the match, our context was Γ = t_n, t_n-1, ..., x, ..., t_0.
        After entering the match, the variable `x` gets eliminated, so all the variables
        on the left are shifted to the right.
        Γ = t_n, t_n-1, ..., t_0
        To address that, we need to exclude `x` from our substitution to not use
        it anymore inside the match. It's done by splitting the subst on `x`
        and dropping it by 1.
         */
        cs.into_iter()
            .map(|mut case| {
                /*
                When having such case:
                | cons y_m y_m-1 ... y0 => t
                Our context after entering it will look like:
                Γ = t_n, t_n-1, ..., y_m, y_m-1, ..., y_0, t_k, ..., t_0.
                Meaning, all the variables >t_k should be lifted by `y_m - y_0 + 1`

                Notice also, that `x` was changed to `y` (after substitution).
                It means, that we should lower all deBruijn indices >x in
                the case body by 1, but ignoring the newly introduced variables y_i.

                We also substitute in the pattern itself (see more in `<Pat as Subst>::subst`).
                 */

                let pat_vars = case.pattern.vars();
                let pat_term = case.pattern.clone().into_term();
                case.pattern = case.pattern.subst_with(subst.clone(), tcs);
                debug!("pattern' = {}", case.pattern);
                let new_pat_vars = case.pattern.vars();

                if let Some(s) = new_pat_vars.iter().sum1::<DBI>() {
                    let x_min = *pat_vars.last().unwrap();
                    debug_assert_eq!(x_min, x);
                    let x_max = *pat_vars.first().unwrap();

                    let y_min = *new_pat_vars.last().unwrap();
                    let y_max = *new_pat_vars.first().unwrap();
                    debug_assert_eq!(y_min, y);
                    if y_min != y_max {
                        debug_assert_eq!(
                            s,
                            (y_max * (y_max + 1) / 2) - (y_min * (y_min + 1) / 2) + y_min
                        );
                    }

                    let fresh_uid = tcs.next_uid;
                    let popped_body = case.body.clone().pop_out(tcs, x, Some(x_max));
                    debug!("Popped body: {}", &popped_body);
                    let popped_body_new = popped_body.subst_with(subst.clone(), tcs);
                    debug!("Popped body': {}", &popped_body_new);

                    let new_pat_term = case.pattern.clone().into_term();
                    case.body =
                        popped_body_new.push_in(tcs, y, Some(y_max), fresh_uid, new_pat_term);
                    debug!("Pushed in body: {}", &case.body);
                } else {
                    let popped_body = case.body.clone().pop_out(tcs, x, None);
                    debug!("Popped body: {}", &popped_body);
                    let popped_body_new = popped_body.subst_with(subst.clone(), tcs);
                    debug!("Popped body': {}", &popped_body_new);

                    case.body = popped_body_new.push_in(tcs, y, None, 0, pat_term);

                    debug!("Pushed in body: {}", &case.body);
                };
                case
            })
            .collect()
    }

    fn subst_non_var_in_cases_instead_of_var(
        subst: &Rc<Substitution>,
        tcs: &mut TypeCheckState,
        cs: Vec<Case>,
        x: &DBI,
    ) -> Vec<Case> {
        let x = *x;
        debug!("substituting instead of var {}...", x);
        let cs = cs
            .into_iter()
            .map(|mut case| {
                let pat_vars = case.pattern.vars();
                if !pat_vars.is_empty() {
                    // self.body = self.body.subst(subst.clone());
                    let x_min = *pat_vars.last().unwrap();
                    debug_assert_eq!(x_min, x);
                    let x_max = *pat_vars.first().unwrap();

                    let fresh_uid = tcs.next_uid;
                    let popped_body = case.body.clone().pop_out(tcs, x, Some(x_max));
                    debug!("Popped body: {}", &popped_body);
                    let popped_body_new = popped_body.subst_with(subst.clone(), tcs);
                    debug!("Popped body': {}", &popped_body_new);

                    case.body =
                        popped_body_new.push_in_without_pat_subst(tcs, x, Some(x_max), fresh_uid);
                    debug!("Pushed in body: {}", &case.body);
                } else {
                    let popped_body = case.body.clone().pop_out(tcs, x, None);
                    debug!("Popped body: {}", &popped_body);
                    let popped_body_new = popped_body.subst_with(subst.clone(), tcs);
                    debug!("Popped body': {}", &popped_body_new);

                    case.body = popped_body_new.push_in_without_pat_subst(tcs, x, None, 0);

                    debug!("Pushed (w/s) in body: {}", &case.body);
                };
                case
            })
            .collect();
        cs
    }

    fn subst_non_var_in_cases_instead_of_non_var(
        subst: Rc<Substitution>,
        tcs: &mut TypeCheckState,
        cs: Vec<Case>,
    ) -> Vec<Case> {
        let new_subst = subst.clone();
        debug!("new''' {} = drop({}, 1) ", new_subst, subst);
        let cs = cs
            .into_iter()
            .map(|mut case| {
                let pat_vars = case.pattern.vars();
                if !pat_vars.is_empty() {
                    let x_min = *pat_vars.last().unwrap();
                    let x_max = *pat_vars.first().unwrap();

                    let fresh_uid = tcs.next_uid;
                    let popped_body = case.body.clone().pop_out_2(tcs, x_min, x_max);
                    debug!("Popped body: {}", &popped_body);
                    let popped_body_new = popped_body.subst_with(subst.clone(), tcs);
                    debug!("Popped body': {}", &popped_body_new);

                    case.body =
                        popped_body_new.push_in_without_pat_subst_2(tcs, x_min, x_max, fresh_uid);
                    debug!("Pushed in body: {}", &case.body);
                } else {
                    case.body = case.body.subst(new_subst.clone());
                };
                case
            })
            .collect();
        cs
    }
}

/// Application on a definition.
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.html#defApp).
pub fn def_app(f: GI, id: Ident, mut a: Vec<Elim>, mut args: Vec<Elim>) -> Term {
    a.append(&mut args);
    Term::Redex(Func::Index(f), id, a)
}

/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#Subst).
pub trait Subst<T: Sized = Self, A = Term>: Sized {
    /// Apply a substitution to an open term.
    fn subst(self, subst: Rc<PrimSubst<A>>) -> T;
}

pub trait SubstWith<'a, T: Sized = Self, A = Term, S = &'a mut TypeCheckState>: Sized {
    /// Apply a substitution to an open term.
    fn subst_with(self, subst: Rc<PrimSubst<A>>, state: S) -> T;
}

impl Subst for Term {
    fn subst(self, subst: Rc<Substitution>) -> Term {
        let mut tcs = TypeCheckState::default();
        self.subst_with(subst, &mut tcs)
    }
}

impl SubstWith<'_> for Term {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &'_ mut TypeCheckState) -> Term {
        match self {
            Term::Whnf(n) => n.subst_with(subst, tcs),
            Term::Redex(Func::Index(f), id, args) => {
                def_app(f, id, vec![], args.subst_with(subst, tcs))
            }
            Term::Redex(Func::Lam(lam), id, args) => Term::Redex(
                Func::Lam(lam.subst_with(subst.clone(), tcs)),
                id,
                args.subst_with(subst, tcs),
            ),
            Term::Match(x, cs) => {
                let x_inst = x.clone().subst_with(subst.clone(), tcs);
                debug!(
                    "subst in `match {} ...` with {} => `match {} ...`",
                    x, subst, x_inst
                );
                match &x_inst {
                    Term::Whnf(Val::Var(Var::Bound(y), es)) if es.is_empty() => {
                        let cs = Self::subst_in_match_with_var(&subst, tcs, &x, *y, cs);
                        Term::Match(box x_inst, cs)
                    }
                    _ => {
                        let cs = match &*x {
                            Term::Whnf(Val::Var(Var::Bound(x), es)) if es.is_empty() => {
                                Self::subst_non_var_in_cases_instead_of_var(&subst, tcs, cs, x)
                            }
                            _ => Self::subst_non_var_in_cases_instead_of_non_var(subst, tcs, cs),
                        };

                        Term::Match(box x_inst, cs)
                    }
                }
            }
        }
    }
}

impl SubstWith<'_> for Elim {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Elim {
        match self {
            Elim::App(term) => Elim::app(term.subst_with(subst, tcs)),
            e => e,
        }
    }
}

impl SubstWith<'_> for Lambda {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Self {
        match self {
            Lambda(arg, closure) => Lambda(
                arg.unboxed().subst_with(subst.clone(), tcs).boxed(),
                closure.subst_with(subst, tcs),
            ),
        }
    }
}

impl SubstWith<'_, Term> for Val {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Term {
        match self {
            Val::Pi(arg, closure) => Term::pi2(
                arg.unboxed().subst_with(subst.clone(), tcs).boxed(),
                closure.subst_with(subst, tcs),
            ),
            Val::Lam(lam) => Term::Whnf(Val::Lam(lam.subst_with(subst, tcs))),
            Val::Cons(name, args) => {
                let xs = args
                    .into_iter()
                    .map(|t| t.subst_with(subst.clone(), tcs))
                    .collect::<Vec<_>>();
                Term::cons(name, xs)
            }
            Val::Universe(n) => Term::universe(n),
            Val::Data(info) => Term::data(info.subst_with(subst, tcs)),
            Val::Meta(m, a) => Term::meta(m, a.subst_with(subst, tcs)),
            Val::Var(Var::Bound(f), args) => subst
                .lookup_with(f, tcs)
                .apply_elim(args.subst_with(subst, tcs)),
            Val::Var(Var::Free(n), args) => {
                Term::Whnf(Val::Var(Var::Free(n), vec![])).apply_elim(args.subst_with(subst, tcs))
            }
        }
    }
}

impl SubstWith<'_> for Closure {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Self {
        match self {
            Closure::Plain(body) => Self::plain(body.subst_with(subst.lift_by(1), tcs)),
        }
    }
}

impl<R, T: Subst<R>> Subst<Vec<R>> for Vec<T> {
    fn subst(self, subst: Rc<Substitution>) -> Vec<R> {
        self.into_iter().map(|e| e.subst(subst.clone())).collect()
    }
}

impl<R, T: Subst<R>, const N: usize> Subst<[R; N]> for [T; N] {
    fn subst(self, subst: Rc<Substitution>) -> [R; N] {
        self.map(|e| e.subst(subst.clone()))
    }
}

impl<A, B, X: Subst<A>, Y: Subst<B>> Subst<(A, B)> for (X, Y) {
    fn subst(self, subst: Rc<Substitution>) -> (A, B) {
        let (x, y) = self;
        (x.subst(subst.clone()), y.subst(subst))
    }
}

impl<R, T: Subst<R>> Subst<Bind<R>> for Bind<T> {
    fn subst(self, subst: Rc<Substitution>) -> Bind<R> {
        self.map_term(|t| t.subst(subst))
    }
}

macro_rules! impl_subst_with_for_vec {
    ($t: ty) => {
        impl<'a> SubstWith<'a, Self> for Vec<$t> {
            fn subst_with(self, subst: Rc<Substitution>, tcs: &'a mut TypeCheckState) -> Self {
                self.into_iter()
                    .map(|e| e.subst_with(subst.clone(), tcs))
                    .collect()
            }
        }
    };
}

impl_subst_with_for_vec!(Term);
impl_subst_with_for_vec!(Elim);
impl_subst_with_for_vec!(Constraint);
impl_subst_with_for_vec!(Pat<DBI, Term>);

/*
impl<'a, R, T: SubstWith<'a, R>, const N: usize> SubstWith<'a, [R; N]> for [T; N] {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &'a mut TypeCheckState) -> [R; N] {
        self.map(|e| e.subst_with(subst.clone(), tcs))
    }
}
 */

impl<'a, A, B, X: Subst<A>, Y: SubstWith<'a, B>> SubstWith<'a, (A, B)> for (X, Y) {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &'a mut TypeCheckState) -> (A, B) {
        let (x, y) = self;
        (x.subst(subst.clone()), y.subst_with(subst, tcs))
    }
}

impl<'a, R, T: SubstWith<'a, R>> SubstWith<'a, Bind<R>> for Bind<T> {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &'a mut TypeCheckState) -> Bind<R> {
        self.map_term(|t| t.subst_with(subst, tcs))
    }
}

impl SubstWith<'_> for ValData {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Self {
        ValData::new(self.def, self.args.subst_with(subst, tcs))
    }
}

impl<'a> SubstWith<'a, Pat<DBI, Term>> for Pat<DBI, Term> {
    // impl<'a, R, T: SubstWith<'a, R>> SubstWith<'a, Pat<DBI, R>> for Pat<DBI, T> {
    fn subst_with(self, subst: Rc<PrimSubst<Term>>, tcs: &'a mut TypeCheckState) -> Pat<DBI, Term> {
        // fn subst_with(self, subst: Rc<PrimSubst<Term>>, tcs: &'a mut TypeCheckState) -> Pat<DBI, R> {
        match self {
            Pat::Absurd => Pat::Absurd,
            Pat::Var(v) => {
                let t = subst.lookup_with(v, tcs);
                if let Some(dbi) = t.dbi_view() {
                    Pat::Var(dbi)
                } else {
                    Pat::Var(v)
                }
            }
            // Pat::Var(v) => Pat::Var(v),
            Pat::Cons(f, c, pats) => {
                let mut pats_new = Vec::with_capacity(pats.len());
                let mut i = None::<usize>;
                for (pi, p) in pats.into_iter().rev().enumerate() {
                    let np = match p {
                        Pat::Var(v) => {
                            if pi == 0 {
                                let t = subst.lookup_with(v, tcs);
                                match t.dbi_view() {
                                    Some(nv) => {
                                        i = Some(nv);
                                        Pat::Var(nv)
                                    }
                                    _ => Pat::Var(v),
                                }
                            } else {
                                if let Some(j) = i {
                                    i = Some(j + 1);
                                    Pat::Var(j + 1)
                                } else {
                                    Pat::Var(v)
                                }
                            }
                        }
                        Pat::Absurd => panic!(),
                        Pat::Wildcard => panic!(),
                        Pat::Cons(..) => {
                            panic!("substitution in case trees with nested conses is not allowed")
                        }
                        Pat::Forced(t) => Pat::Forced(t.subst_with(subst.clone(), tcs)),
                    };
                    pats_new.insert(0, np);
                }
                Pat::Cons(f, c, pats_new)
            }
            Pat::Forced(t) => Pat::Forced(t.subst_with(subst, tcs)),
            Pat::Wildcard => Pat::Wildcard,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::syntax::ConHead;
    use std::iter;

    #[test]
    fn test_pop_out_term_from_case() {
        use crate::syntax::core::Pat;
        /*
        I.
        subst: cons @2
             d  c  b
        foo @2 @3 @4
            5 4 3 2 1 0
        Γ = a b c d e f
              f
        match 0 {     4 3 2 1 0
                  Γ = a b c d e
            | nil => foo @1 @2 @3
                          d  c  b
        }
        ==>
        Γ = a b c d e
             d  c  b
        foo @1 @2 @3
        match @2 {
                  Γ = a b d e
            | nil => foo @1 nil @2
        }

        II.
        subst: cons @0, cons @0
             d  c  b
        foo @2 @3 @4
            5 4 3 2 1 0
        Γ = a b c d e f
              e
        match 1 {     4 3 2 1 0
                  Γ = a b c d f
            | nil => foo @1 @2 @3
                          d  c  b
        }
        ==>
        Γ = a b c d
             d  c  b
        foo @0 @1 @2
        match @0 {
                  Γ = a b c
            | nil => foo nil @0 @1
        }


        III.
        Γ = a b c d e f
        subst: cons @2
        foo _  _  @2 @3
                   d  c
              f
        match 0 {
                       Γ = a b c d e f0 f1
            | cons 1 0 => foo @0 @1 @3 @4
                              f1 f0  d  c
        }
        ==>
        Γ = a b c d e
        foo _  _  @1 @2
                   d  c
               c
        match @2 {
                       Γ = a b c3 c2 d e
            | cons 3 2 => foo @2 @3 @1 (cons 3 2)
                                     d
        }
         */
        /*
        foo @0 @1 ?7 ?8 @3 @4 ?6
        bar @0 @1 @3 @4 @5
        match @2 {
            | cons 3 2 => foo @0 @1 @2 @3 @4 @5 ?6
            | nil      => bar @0 @1 @2 @3 @4
        }
         */

        let x = 2;
        let nil_pat = Pat::cons(ConHead::new("nil", 0), vec![]);
        let _nil_cons = nil_pat.into_term();
        let term = Term::fun_app(0, "foo", [0, 1, 2, 3, 4, 5].map(Term::from_dbi));
        let x_max = 3;

        let mut tcs = TypeCheckState::default();
        let fresh_uid = tcs.next_uid;
        assert_eq!(
            term.pop_out(&mut tcs, x, Some(x_max)),
            Term::fun_app(
                0,
                "foo",
                vec![
                    Term::from_dbi(0),
                    Term::from_dbi(1),
                    Term::free_var(fresh_uid + 1),
                    Term::free_var(fresh_uid + 0),
                    Term::from_dbi(3),
                    Term::from_dbi(4),
                ]
            )
        );

        let term = Term::fun_app(0, "bar", [0, 1, 2, 3, 4].map(Term::from_dbi));

        let mut tcs = TypeCheckState::default();
        assert_eq!(
            term.pop_out(&mut tcs, x, None),
            Term::fun_app(
                0,
                "bar",
                vec![
                    Term::from_dbi(0),
                    Term::from_dbi(1),
                    Term::from_dbi(3),
                    Term::from_dbi(4),
                    Term::from_dbi(5),
                ]
            )
        );
    }

    #[test]
    fn test_push_in_term_from_case() {
        use crate::syntax::core::Pat;
        /*
        I.
        subst: cons @2
             d  c  b
        foo @2 @3 @4
            5 4 3 2 1 0
        Γ = a b c d e f
              f
        match 0 {     4 3 2 1 0
                  Γ = a b c d e
            | nil => foo @1 @2 @3
                          d  c  b
        }
        ==>
        Γ = a b c d e
             d  c  b
        foo @1 @2 @3
        match @2 {
                  Γ = a b d e
            | nil => foo @1 nil @2
        }

        II.
        subst: cons @0, cons @0
             d  c  b
        foo @2 @3 @4
            5 4 3 2 1 0
        Γ = a b c d e f
              e
        match 1 {     4 3 2 1 0
                  Γ = a b c d f
            | nil => foo @1 @2 @3
                          d  c  b
        }
        ==>
        Γ = a b c d
             d  c  b
        foo @0 @1 @2
        match @0 {
                  Γ = a b c
            | nil => foo nil @0 @1
        }


        III.
        Γ = a b c d e f
        subst: cons @2
        foo _  _  @2 @3
                   d  c
              f
        match 0 {
                       Γ = a b c d e f0 f1
            | cons 1 0 => foo @0 @1 @3 @4
                              f1 f0  d  c
        }
        ==>
        Γ = a b c d e
        foo _  _  @1 @2
                   d  c
               c
        match @2 {
                       Γ = a b c3 c2 d e
            | cons 3 2 => foo @2 @3 @1 (cons 3 2)
                                     d
        }
         */

        let x = 2;
        let nil_con = ConHead::new("nil", 0);
        let nil_pat = Pat::cons(nil_con.clone(), vec![]);
        let nil_term = nil_pat.into_term();
        let term = Term::fun_app(
            0,
            "foo",
            vec![
                Term::from_dbi(0),
                Term::from_dbi(1),
                Term::free_var(1),
                Term::free_var(0),
                Term::from_dbi(3),
                Term::from_dbi(4),
            ],
        );
        let x_min = x;
        let x_max = 3;

        let max_mi = 0;
        let cons_con = ConHead::new("cons", 0);
        let cons_pat = Pat::cons(
            cons_con.clone(),
            (x_min..=x_max).rev().map(Pat::from_dbi).collect::<Vec<_>>(),
        );
        let cons_term = cons_pat.into_term();
        let mut tcs = TypeCheckState::default();
        assert_eq!(
            term.push_in(&mut tcs, x, Some(x_max), max_mi + 0, cons_term.clone()),
            Term::fun_app(0, "foo", [0, 1, 2, 3, 4, 5].map(Term::from_dbi))
        );

        // foo ?0 ?1 @1 @3 @4 @2
        // match @2 {
        //     | cons 3 2 => foo @2 @3 @1 @4 @5 (cons @3 @2)
        let term = Term::fun_app(
            0,
            "foo",
            vec![
                Term::free_var(1),
                Term::free_var(0),
                Term::from_dbi(1),
                Term::from_dbi(3),
                Term::from_dbi(4),
                Term::from_dbi(2),
            ],
        );
        let x_min = x;
        let x_max = 3;

        let max_mi = 0;
        let cons_pat = Pat::cons(
            cons_con.clone(),
            (x_min..=x_max).rev().map(Pat::from_dbi).collect::<Vec<_>>(),
        );
        let cons_term = cons_pat.into_term();
        let mut tcs = TypeCheckState::default();
        assert_eq!(
            term.push_in(&mut tcs, x, Some(x_max), max_mi, cons_term.clone()),
            Term::fun_app(
                0,
                "foo",
                [2, 3, 1, 4, 5]
                    .map(Term::from_dbi)
                    .into_iter()
                    .chain(iter::once(cons_term.clone()))
            )
        );

        let term = Term::fun_app(
            0,
            "bar",
            vec![
                Term::from_dbi(0),
                Term::from_dbi(1),
                Term::from_dbi(3),
                Term::from_dbi(4),
                Term::from_dbi(5),
            ],
        );

        let mut tcs = TypeCheckState::default();
        assert_eq!(
            term.push_in(&mut tcs, x, None, 0, nil_term.clone()),
            Term::fun_app(0, "bar", [0, 1, 2, 3, 4].map(Term::from_dbi))
        );

        let term = Term::fun_app(
            0,
            "bar",
            vec![Term::from_dbi(1), Term::from_dbi(2), Term::from_dbi(3)],
        );

        let mut tcs = TypeCheckState::default();
        assert_eq!(
            term.push_in(&mut tcs, x, None, 0, nil_term.clone()),
            Term::fun_app(
                0,
                "bar",
                vec![Term::from_dbi(1), nil_term, Term::from_dbi(2)]
            )
        );
    }
}
