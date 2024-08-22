use super::Term;
use crate::check::{Constraint, TypeCheckState};
use crate::syntax::core::free_subst::SubstituteFreeVars;
use crate::syntax::core::subst::{PrimSubst, Substitution};
use crate::syntax::core::term::{Id, Lambda, Name};
use crate::syntax::core::{Boxed, Case, Closure, DeBruijn, Elim, Func, ValData, Var};
use crate::syntax::pattern::Pat;
use crate::syntax::{Bind, Ident, DBI, GI, UID};
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::Display;
use std::iter;
use std::rc::Rc;
use std::sync::atomic::Ordering;

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
            Term::Var(f, mut a) => {
                a.append(&mut args);
                Term::Var(f, a)
            }
            Term::Lam(lam) => Term::Redex(Func::Lam(lam), Ident::new("<λ>"), args),
            Term::Cons(c, mut a) => {
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

    pub(crate) fn subst_in_match_with_var<S, C: SubstCtx>(
        subst: &Rc<PrimSubst<S>>,
        tcs: &mut C,
        x: &Term,
        y: DBI,
        cs: Vec<Case>,
    ) -> Vec<Case>
    where
        Pat<DBI, Term>: SubstWith<S, C>,
        Term: SubstWith<S, C>,
    {
        let x = x.dbi_view().expect("unexpected term");
        debug!("Replacing with var {} instead of {}...", y, x);
        /*
        Given a case tree of the form:
        match x { | cons ... => ... }
        Before entering the match, our context is Γ = t_n, t_n-1, ..., x, ..., t_0.
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
                Our context after entering the branch will look like this:
                Γ = t_n, t_n-1, ..., y_m, y_m-1, ..., y_0, t_k, ..., t_0.
                Meaning, all the variables >t_k should be lifted by `y_m - y_0 + 1`

                Notice also, that `x` has changed to `y` (after substitution).
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
                    // pattern variables should increase linearly
                    if y_min != y_max {
                        debug_assert_eq!(
                            s,
                            (y_max * (y_max + 1) / 2) - (y_min * (y_min + 1) / 2) + y_min
                        );
                    }

                    /*
                    Substitution in case is done by 'popping' term on the right hand side, i.e.
                    putting it in the outer context (without the eliminated `x` and newly bound
                    variables (which are replaced by fresh free variables). This is done due to
                    some problems that appear when trying to do it naively with DeBruijn indices.

                    After substitution, the term is 'pushed' back in the case (i.e. all the free
                    variables are replaced with the corresponding pattern variables and variables
                    are shifted).
                     */
                    let fresh_uid = tcs.next_fresh_uid();
                    let popped_body = case.body.clone().pop_out::<C>(tcs, x, Some(x_max));
                    trace!("Popped body: {}", &popped_body);
                    let popped_body_new = popped_body.subst_with(subst.clone(), tcs);
                    trace!("Popped body': {}", &popped_body_new);

                    let new_pat_term = case.pattern.clone().into_term();
                    case.body =
                        popped_body_new.push_in(tcs, y, Some(y_max), fresh_uid, new_pat_term);
                    trace!("Pushed in body: {}", &case.body);
                } else {
                    let popped_body = case.body.clone().pop_out(tcs, x, None);
                    trace!("Popped body: {}", &popped_body);
                    let popped_body_new = popped_body.subst_with(subst.clone(), tcs);
                    trace!("Popped body': {}", &popped_body_new);

                    case.body = popped_body_new.push_in(tcs, y, None, 0, pat_term);

                    trace!("Pushed in body: {}", &case.body);
                };
                case
            })
            .collect()
    }

    pub(crate) fn subst_non_var_in_cases_instead_of_var<S, C>(
        subst: &Rc<PrimSubst<S>>,
        tcs: &mut C,
        cs: Vec<Case>,
        x: &DBI,
    ) -> Vec<Case>
    where
        C: SubstCtx,
        Pat<DBI, Term>: SubstWith<S, C>,
        Term: SubstWith<S, C>,
        Term: SubstWith<Term, C>,
    {
        let x = *x;
        debug!("substituting instead of var {}...", x);
        cs.into_iter()
            .map(|mut case| {
                let pat_vars = case.pattern.vars();
                if !pat_vars.is_empty() {
                    let x_min = *pat_vars.last().unwrap();
                    debug_assert_eq!(x_min, x);
                    let x_max = *pat_vars.first().unwrap();

                    let fresh_uid = tcs.next_fresh_uid();
                    let popped_body = case.body.clone().pop_out(tcs, x, Some(x_max));
                    trace!("Popped body: {}", &popped_body);
                    let popped_body_new = popped_body.subst_with(subst.clone(), tcs);
                    trace!("Popped body': {}", &popped_body_new);

                    case.body =
                        popped_body_new.push_in_without_pat_subst(tcs, x, Some(x_max), fresh_uid);
                    trace!("Pushed in body: {}", &case.body);
                } else {
                    let popped_body = case.body.clone().pop_out(tcs, x, None);
                    trace!("Popped body: {}", &popped_body);
                    let popped_body_new = popped_body.subst_with(subst.clone(), tcs);
                    trace!("Popped body': {}", &popped_body_new);

                    case.body = popped_body_new.push_in_without_pat_subst(tcs, x, None, 0);

                    trace!("Pushed (w/s) in body: {}", &case.body);
                };
                case
            })
            .collect()
    }

    pub fn subst_non_var_in_cases_instead_of_free_var<C>(
        tcs: &mut C,
        cs: Vec<Case>,
        x: &UID,
    ) -> Vec<Case>
    where
        C: SubstCtx,
        Term: SubstWith<Term, C>,
    {
        let x = *x;
        cs.into_iter()
            .map(|mut case| {
                let term = case.pattern.clone().into_term();
                debug!(target: "reduce", "substituting {term} instead of free var #{} in body {}...", x , case.body);
                let subst = iter::once((x, term)).collect::<HashMap<_, _>>();
                case.body.subst_free_vars_with(&subst, tcs, 0);
                case
            })
            .collect()
    }

    pub(crate) fn subst_non_var_in_cases_instead_of_non_var<S, C: SubstCtx>(
        subst: Rc<PrimSubst<S>>,
        tcs: &mut C,
        cs: Vec<Case>,
    ) -> Vec<Case>
    where
        Term: SubstWith<S, C>,
    {
        let new_subst = subst.clone();
        // debug!("new''' {} = drop({}, 1) ", new_subst, subst);
        cs.into_iter()
            .map(|mut case| {
                let pat_vars = case.pattern.vars();
                if !pat_vars.is_empty() {
                    let x_min = *pat_vars.last().unwrap();
                    let x_max = *pat_vars.first().unwrap();

                    let fresh_uid = tcs.next_fresh_uid();
                    let popped_body = case.body.clone().pop_out_non_var(tcs, x_min, x_max);
                    trace!("Popped body: {}", &popped_body);
                    let popped_body_new = popped_body.subst_with(subst.clone(), tcs);
                    trace!("Popped body': {}", &popped_body_new);

                    case.body = popped_body_new
                        .push_in_without_pat_subst_non_var(tcs, x_min, x_max, fresh_uid);
                    trace!("Pushed in body: {}", &case.body);
                } else {
                    case.body = case.body.subst_with(new_subst.clone(), tcs);
                };
                case
            })
            .collect()
    }
}

/// Application on a definition.
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.html#defApp).
pub fn def_app(f: GI, id: Ident, mut a: Vec<Elim>, mut args: Vec<Elim>) -> Term {
    a.append(&mut args);
    Term::Redex(Func::Index(f), id, a)
}

pub trait SubstCtx {
    fn fresh_uid(&mut self) -> UID;

    fn next_fresh_uid(&mut self) -> UID;

    fn fresh_free_var(&mut self) -> Term {
        Term::Var(Var::free(self.fresh_uid()), vec![])
    }
}

/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#Subst).
pub trait Subst<A = Term, T: Sized = Self>: Sized {
    /// Apply a substitution to an open term.
    fn subst(self, subst: Rc<PrimSubst<A>>) -> T;
}

pub trait SubstWith<A = Term, C = TypeCheckState, T: Sized = Self>: Sized {
    /// Apply a substitution to an open term.
    fn subst_with(self, subst: Rc<PrimSubst<A>>, state: &mut C) -> T;
}

impl<S, T, R> Subst<S, R> for T
where
    T: SubstWith<S, TypeCheckState, R>,
{
    fn subst(self, subst: Rc<PrimSubst<S>>) -> R {
        self.subst_with(subst, &mut TypeCheckState::default())
    }
}

impl<C: SubstCtx> SubstWith<Term, C, Term> for Var {
    fn subst_with(self, subst: Rc<PrimSubst<Term>>, state: &mut C) -> Term {
        match self {
            v if let Some(f) = v.dbi_view() => {
                subst.lookup_with::<C>(f, state)
            }
            v => Term::Var(v, vec![]),
        }
    }
}

impl<S, C> SubstWith<S, C> for Term
where
    Var: SubstWith<S, C, Self>,
    Pat<DBI, Term>: SubstWith<S, C>,
    S: Display,
    C: SubstCtx,
{
    fn subst_with(self, subst: Rc<PrimSubst<S>>, tcs: &mut C) -> Term {
        match self {
            Term::Pi(arg, closure) => Term::pi2(
                arg.unboxed().subst_with(subst.clone(), tcs).boxed(),
                closure.subst_with(subst, tcs),
            ),
            Term::Lam(lam) => Term::Lam(lam.subst_with(subst, tcs)),
            Term::Cons(name, args) => {
                let xs = args
                    .into_iter()
                    .map(|t| t.subst_with(subst.clone(), tcs))
                    .collect::<Vec<_>>();
                Term::cons(name, xs)
            }
            Term::Universe(n) => Term::universe(n),
            Term::Data(info) => Term::data(info.subst_with(subst, tcs)),
            Term::Var(var, args) => var.subst_with(subst.clone(), tcs).apply_elim(args.subst_with(subst, tcs)),
            Term::Id(id) => id.subst_with(subst, tcs),
            Term::Refl(t) => Term::Refl(t.subst_with(subst, tcs).boxed()),
            Term::Redex(Func::Index(f), id, args) => {
                def_app(f, id, vec![], args.subst_with(subst, tcs))
            }
            Term::Redex(Func::Lam(lam), id, args) => Term::Redex(
                Func::Lam(lam.subst_with(subst.clone(), tcs)),
                id,
                args.subst_with(subst, tcs),
            ),
            Term::Match(x, x_ty, cs) => {
                // For how substitution in `match` generally work see inner comments
                // of `Self::subst_in_match_with_var` function.
                let x_ty = x_ty.clone().subst_with(subst.clone(), tcs).boxed();
                let x_inst = x.clone().subst_with(subst.clone(), tcs);
                debug!(
                    "subst in `match {} ...` with {} => `match {} ...`",
                    x, subst, x_inst
                );
                let maybe_x_inst_var = x_inst.dbi_view();
                match maybe_x_inst_var {
                    Some(y) => {
                        let cs = Self::subst_in_match_with_var::<S, C>(&subst, tcs, &x, y, cs);
                        Term::Match(x_inst.boxed(), x_ty.clone(), cs)
                    }
                    _ => {
                        let cs = match &*x {
                            t if let Some(x) = t.dbi_view() => {
                                if t.is_twin_var() {
                                    warn!("Twin var in match: {}", x);
                                }
                                Self::subst_non_var_in_cases_instead_of_var(&subst, tcs, cs, &x)
                            }
                            t if let Some(x) = t.free_var_view() => {
                                if t.is_twin_var() {
                                    warn!("Twin (free) var in match: {}", x);
                                }
                                Self::subst_non_var_in_cases_instead_of_free_var(tcs, cs, &x)
                            }
                            _ => Self::subst_non_var_in_cases_instead_of_non_var(subst, tcs, cs),
                        };

                        Term::Match(x_inst.boxed(), x_ty.clone(), cs)
                    }
                }
            }
            Term::Ap(_tele, _ps, _t) => {
                // let ps = ps.subst_with(subst.clone(), tcs);
                // let t = t.subst_with(subst, tcs);
                // Term::Ap(tele, ps, box t)
                todo!("subst in `ap`")
            }
        }
    }
}

impl<S, C> SubstWith<S, C> for Elim
where
    Term: SubstWith<S, C>,
{
    fn subst_with(self, subst: Rc<PrimSubst<S>>, tcs: &mut C) -> Elim {
        match self {
            Elim::App(term) => Elim::app(term.subst_with(subst, tcs)),
            e => e,
        }
    }
}

impl<S, C> SubstWith<S, C> for Lambda
where
    Term: SubstWith<S, C>,
{
    fn subst_with(self, subst: Rc<PrimSubst<S>>, tcs: &mut C) -> Self {
        match self {
            Lambda(arg, closure) => Lambda(
                arg.unboxed().subst_with(subst.clone(), tcs).boxed(),
                closure.subst_with(subst, tcs),
            ),
        }
    }
}

impl<S, C> SubstWith<S, C, Term> for Id
where
    Term: SubstWith<S, C>,
{
    fn subst_with(self, subst: Rc<PrimSubst<S>>, tcs: &mut C) -> Term {
        Term::Id(Id {
            tele: self.tele.subst_with(subst.clone(), tcs),
            ty: self.ty.subst_with(subst.clone(), tcs).boxed(),
            paths: self.paths.subst_with(subst.clone(), tcs),
            a1: self.a1.subst_with(subst.clone(), tcs).boxed(),
            a2: self.a2.subst_with(subst, tcs).boxed(),
        })
    }
}


impl<S, C> SubstWith<S, C> for Closure
where
    Term: SubstWith<S, C>,
{
    fn subst_with(self, subst: Rc<PrimSubst<S>>, tcs: &mut C) -> Self {
        match self {
            Closure::Plain(body) => Self::plain(body.subst_with(subst.lift_by(1), tcs)),
        }
    }
}

impl<A, S, C, T> SubstWith<S, C, Vec<A>> for Vec<T>
where
    T: SubstWith<S, C, A>,
{
    fn subst_with(self, subst: Rc<PrimSubst<S>>, tcs: &mut C) -> Vec<A> {
        self.into_iter().map(|e| e.subst_with(subst.clone(), tcs)).collect()
    }
}

impl<A, B, S, C, X, Y> SubstWith<S, C, (A, B)> for (X, Y)
where
    X: SubstWith<S, C, A>,
    Y: SubstWith<S, C, B>,
{
    fn subst_with(self, subst: Rc<PrimSubst<S>>, tcs: &mut C) -> (A, B) {
        let (x, y) = self;
        (x.subst_with(subst.clone(), tcs), y.subst_with(subst, tcs))
    }
}

impl<R, S, C, T> SubstWith<S, C, Bind<R>> for Bind<T>
where
    T: SubstWith<S, C, R>,
{
    fn subst_with(self, subst: Rc<PrimSubst<S>>, tcs: &mut C) -> Bind<R> {
        self.map_term(|t| t.subst_with(subst, tcs))
    }
}

impl<S, C> SubstWith<S, C> for ValData
where
    Term: SubstWith<S, C>,
{
    fn subst_with(self, subst: Rc<PrimSubst<S>>, tcs: &mut C) -> Self {
        ValData::new(self.def, self.args.subst_with(subst, tcs))
    }
}

impl<C: SubstCtx> SubstWith<Term, C> for Pat<DBI, Term>
{
    fn subst_with(self, subst: Rc<PrimSubst<Term>>, tcs: &mut C) -> Self {
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
                            } else if let Some(j) = i {
                                i = Some(j + 1);
                                Pat::Var(j + 1)
                            } else {
                                Pat::Var(v)
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
        let fresh_uid = tcs.next_fresh_uid();
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
