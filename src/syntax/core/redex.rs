use super::Term;
use crate::check::{Constraint, TypeCheckState};
use crate::dsp;
use crate::syntax::core::subst::{PrimSubst, Substitution};
use crate::syntax::core::term::Lambda;
use crate::syntax::core::{Closure, DeBruijn, Elim, FoldVal, Func, Val, ValData, Var};
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
        tcs.enter_def(0, 0);
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
                    /*
                    before subst:
                    with subst: cons(@3, cons(@4, id))
                              x  y  z             z        x  y
                    Γ = @5 @4 @3 @2 @1 @0  =>  @5 @4 @3 @2 @1 @0
                    -- e.g. bar @3 @2 @1 => bar @1 @0 @4
                    -- e.g. baz @1 => baz @4
                    match @0 {                            x  y  z
                     | nil => (bar @2 @1 @0) -- Γ = @4 @3 @2 @1 @0
                     | (pair @1 @0) => (foo @2 @1 @0) --  Γ = @4 @3 @2 @1 @0, bar @4 @3 @2
                    }                                         x  y  z

                    after subst:
                        z        x  y
                    Γ = @4 @3 @2 @1 @0
                    -- eg. bar @1 @0 @4
                    match @3 {                      z     x  y
                     | nil => (bar @1 @0 @3) -- Γ = @3 @2 @1 @0
                     | (pair @1 @0) => (foo @5 @1 @0) -- Γ = @5 @4 @3 @2 @1 @0, e.g. bar @5 @3 @2
                                                             z     x  y
                    }

                    with subst: cons(@3, id)
                              x  y     z             z  x  y
                    Γ = @5 @4 @3 @2 @1 @0  =>  @5 @4 @3 @2 @1 @0
                    e.g. bar @3 @2 @0 => bar @2 @1 @3
                         foo @2 _ _ @0
                    match @1 {     x  y  z                   x  y  z
                     | nil => (bar @2 @1 @0)    Γ = @5 @4 @3 @2 @1 @0
                     | (pair 2 1) => (foo @3 @2 @1 @0)    Γ = @5 @4 @3 @2 @1 @0
                    }                     y        z             x  y        z

                              z  x  y
                    Γ = @5 @4 @3 @2 @1 @0
                    match @0 {     x  y  z                 z  x  y
                     | nil => (bar @1 @0 @2)  Γ = @5 @4 @3 @2 @1 @0
                     | (pair 2 1) => (foo @0 @2 @1 @4)   Γ = @5 @4 @3 @2 @1 @0
                    }                     y        z            z  x        y
                     */
                    Term::Whnf(Val::Var(Var::Bound(y), _es)) => {
                        let x = x.dbi_view().expect("unexpected term");
                        let y = *y;
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
                        let (subst1, subst2) = subst.clone().split(x);
                        debug!(
                            "split substitution (by {}): {} ⊎ {} = {}",
                            x, subst1, subst2, subst,
                        );
                        // let _subst1 = subst1.clone().drop_by(1);
                        let _ = subst2;
                        let cs = cs
                            .into_iter()
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

                                /*
                                with: cons @3
                                bar @3 @2 @0
                                foo _  _  @0
                                match @1 {
                                 | nil => (bar @2 @1 @0)
                                 | (pair 2 1) => (foo @2 @1 @0)
                                }

                                bar @2 @1 @3
                                foo _  _  @3
                                match @0 {
                                 | nil => (bar @1 @0 @2)
                                 | (pair 1 0) => (foo @1 @0 @4)
                                }
                                 */

                                let pat_vars = case.pattern.vars();
                                let pat_term = case.pattern.clone().into_term();
                                case.pattern = case.pattern.subst_with(subst.clone(), tcs);
                                debug!("pattern' = {}", case.pattern);
                                let new_pat_vars = case.pattern.vars();

                                // debug!("Substituting in case {} with {}", case, subst);
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
                                            (y_max * (y_max + 1) / 2) - (y_min * (y_min + 1) / 2)
                                                + y_min
                                        );
                                    }

                                    let fresh_uid = tcs.next_uid;
                                    let popped_body =
                                        case.body.clone().pop_out(tcs, x, Some(x_max));
                                    debug!("Popped body: {}", &popped_body);
                                    let popped_body_new =
                                        popped_body.subst_with(subst.clone(), tcs);
                                    debug!("Popped body': {}", &popped_body_new);

                                    let new_pat_term = case.pattern.clone().into_term();
                                    case.body = popped_body_new.push_in(
                                        tcs,
                                        y,
                                        Some(y_max),
                                        fresh_uid,
                                        new_pat_term,
                                    );
                                    debug!("Pushed in body: {}", &case.body);
                                } else {
                                    let popped_body = case.body.clone().pop_out(tcs, x, None);
                                    debug!("Popped body: {}", &popped_body);
                                    let popped_body_new =
                                        popped_body.subst_with(subst.clone(), tcs);
                                    debug!("Popped body': {}", &popped_body_new);

                                    case.body = popped_body_new.push_in(tcs, y, None, 0, pat_term);

                                    debug!("Pushed in body: {}", &case.body);
                                };
                                case
                            })
                            .collect();
                        Term::Match(box x_inst, cs)
                    }
                    /*
                    Term::Whnf(val) if val.is_cons() => {
                        /*
                        Given:
                        Γ = (a : A) (b : B) (c : C)
                             2       1       0         -- DeBruijn indices
                        σ = { 0 := x, 1 := y, 2 := z }
                        self = match b {
                            | C i j => t
                        }

                        1) On match:
                           Γ' = (a : A) (i : Ba) (j : Bb) (c : C)
                                 3       2        1        0
                           ρ ⊎ τ = σ
                           σ' = ρ.drop(1).lift(n) ⊎ τ
                           where `n` is number of newly bound variables in the pattern (2 in this case)
                           result: tσ'

                        2) On stuck match:
                           Perform ordinary substitution in each sub-term
                        */
                        match try_match(val, &cs) {
                            Some((i, sigma)) => {
                                debug!("matched {} with σ = {}", i, sigma);

                                let new_subst = match &*x {
                                    Term::Whnf(Val::Var(x, es)) if es.is_empty() => {
                                        let (subst1, subst2) = subst.clone().split(*x);
                                        debug!("{} = {} ⊎ {}", subst, subst1, subst2);
                                        let new_sigma = sigma.drop_by(1);
                                        debug!("σ' = {}", new_sigma);
                                        let rc = subst1.drop_by(1).union(new_sigma);
                                        let new_subst = rc.clone().union(subst2.clone());
                                        debug!("new {} = {} ⊎ {} ", new_subst, rc, subst2);
                                        new_subst
                                    }
                                    _ => {
                                        let subst = subst.drop_by(1);
                                        // let new_subst = subst.clone().union(sigma.clone());
                                        let new_subst = sigma.clone().union(subst.clone());
                                        debug!("new' {} = {} ⊎ {} ", new_subst, sigma, subst);
                                        new_subst
                                    }
                                };
                                let matched_case = cs.remove(i);
                                matched_case.body.subst(new_subst)
                            }
                            None => {
                                let cs = cs.into_iter().map(|c| c.subst(subst.clone())).collect();
                                Term::Match(box x_inst, cs)
                            }
                        }
                    }
                     */
                    _ => {
                        let cs = match &*x {
                            // if we substituted instead of var...
                            Term::Whnf(Val::Var(Var::Bound(x), es)) if es.is_empty() => {
                                let x = *x;
                                debug!("substituting instead of var {}...", x);
                                let (subst1, subst2) = subst.clone().split(x);
                                debug!("split substitution: {} ⊎ {} = {}", subst1, subst2, subst);
                                // let rc = subst1.clone().drop_by(1);
                                // let new_subst = rc.clone().union(subst2.clone());
                                // debug!(
                                //     "unify substitution: {} = {} ⊎ {} = drop({}, 1) ⊎ {}",
                                //     new_subst, rc, subst2, subst1, subst2
                                // );

                                /*

                                cons a
                                match t {
                                 | zero => (suc @0)
                                 | (suc 2) => 4 3 2 1 0
                                }

                                match t {
                                 | zero => (suc @0)
                                 | (suc 1) => 3 2 1 0 a
                                }
                                 */
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
                                            let popped_body =
                                                case.body.clone().pop_out(tcs, x, Some(x_max));
                                            debug!("Popped body: {}", &popped_body);
                                            let popped_body_new =
                                                popped_body.subst_with(subst.clone(), tcs);
                                            debug!("Popped body': {}", &popped_body_new);

                                            /*
                                            Cons(@1, Cons((pair @3 @4), ε))

                                            bar @1 @0 @1
                                            foo ?1 ?0 @1
                                            match @1 {
                                             | nil => (bar @2 @1 @0)
                                             | (pair 2 1) => (foo @2 @1 @0)
                                            }

                                            match (pair @3 @4) {
                                             | nil => (bar @1 @0 @1)
                                             | (pair 2 1) => (foo @2 @1 @3)
                                            }
                                            */
                                            case.body = popped_body_new.push_in_without_pat_subst(
                                                tcs,
                                                x,
                                                Some(x_max),
                                                fresh_uid,
                                            );
                                            debug!("Pushed in body: {}", &case.body);
                                        } else {
                                            let popped_body =
                                                case.body.clone().pop_out(tcs, x, None);
                                            debug!("Popped body: {}", &popped_body);
                                            let popped_body_new =
                                                popped_body.subst_with(subst.clone(), tcs);
                                            debug!("Popped body': {}", &popped_body_new);

                                            case.body = popped_body_new
                                                .push_in_without_pat_subst(tcs, x, None, 0);

                                            debug!("Pushed (w/s) in body: {}", &case.body);
                                        };
                                        case
                                    })
                                    .collect();
                                cs
                            }
                            _ => {
                                let new_subst = subst.clone();
                                debug!("new''' {} = drop({}, 1) ", new_subst, subst);
                                let cs = cs
                                    .into_iter()
                                    .map(|mut case| {
                                        let pat_vars = case.pattern.vars();
                                        if !pat_vars.is_empty() {
                                            // self.body = self.body.subst(subst.clone());
                                            let x_min = *pat_vars.last().unwrap();
                                            // debug_assert_eq!(x_min, x);
                                            let x_max = *pat_vars.first().unwrap();

                                            let fresh_uid = tcs.next_uid;
                                            let popped_body =
                                                case.body.clone().pop_out_2(tcs, x_min, x_max);
                                            debug!("Popped body: {}", &popped_body);
                                            let popped_body_new =
                                                popped_body.subst_with(subst.clone(), tcs);
                                            debug!("Popped body': {}", &popped_body_new);

                                            case.body = popped_body_new
                                                .push_in_without_pat_subst_2(
                                                    tcs, x_min, x_max, fresh_uid,
                                                );
                                            debug!("Pushed in body: {}", &case.body);
                                        } else {
                                            case.body = case.body.subst(new_subst.clone());
                                            // let popped_body =
                                            //     case.body.clone().pop_out(tcs, x, None);
                                            // debug!("Popped body: {}", &popped_body);
                                            // let popped_body_new =
                                            //     popped_body.subst_with(subst.clone(), tcs);
                                            // debug!("Popped body': {}", &popped_body_new);
                                            //
                                            // case.body = popped_body_new
                                            //     .push_in_without_pat_subst(tcs, x, None, 0);
                                            //
                                            // debug!("Pushed (w/s) in body: {}", &case.body);
                                        };
                                        case
                                    })
                                    .collect();
                                cs
                            }
                        };

                        Term::Match(box x_inst, cs)
                    }
                }
            }
        }
    }
}
/*
pub fn shift_pattern_vars(
    term: Term,
    x_min: usize,
    x_max: usize,
    y_min: usize,
    y_max: usize,
    diff: isize,
    len: usize,
) -> Term {
    let subst = if diff >= 0 {
        let diff = diff as usize;
        let pat_subst = Substitution::parallel(
            (y_min..=y_max)
                .map(Term::from_dbi)
                .collect::<Vec<_>>()
                .into_iter(),
        );
        let lifted_vars_subst = Substitution::parallel(
            (y_max..y_max + diff)
                .map(|i| Term::from_dbi(i - diff - 1))
                .collect::<Vec<_>>()
                .into_iter(),
        );
        let unchanged_vars = Substitution::parallel(
            (0..x_min)
                .map(Term::from_dbi)
                .collect::<Vec<_>>()
                .into_iter(),
        );
        Substitution::raise(len + diff + x_min)
            .union(lifted_vars_subst.union(pat_subst.union(unchanged_vars)))
    } else {
        let diff = -diff as usize;
        let y_min = x_min - diff;
        let y_max = x_max - diff;
        let len = x_max - x_min + 1;
        let unchanged_vars = Substitution::parallel(
            (0..y_min)
                .map(Term::from_dbi)
                .collect::<Vec<_>>()
                .into_iter(),
        );
        let pat_subst = Substitution::parallel(
            (y_min..=y_max)
                .map(Term::from_dbi)
                .collect::<Vec<_>>()
                .into_iter(),
        );
        let lifted_vars_subst = Substitution::parallel(
            (y_max..=x_min)
                .map(|i| Term::from_dbi(i + len - 1))
                .collect::<Vec<_>>()
                .into_iter(),
        );
        Substitution::raise(len + diff + y_min)
            .union(pat_subst.union(lifted_vars_subst.union(unchanged_vars)))
    };
    term.subst(subst)
}

 */
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
        // let args = self
        //     .args
        //     .into_iter()
        //     .map(|t| t.subst_with(subst.clone(), tcs))
        //     .collect();
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
/*
fn subst_in_subst(
    mut subst: Rc<Substitution>,
    term: &Term,
    dbi: DBI,
    to_term: &Term,
) -> Rc<Substitution> {
    let vars = term
        .try_fold_val::<!, _>(Vec::new(), |mut xs, val| {
            match val {
                Val::Var(x, _) => xs.push(*x),
                _ => {}
            };
            Ok(xs)
        })
        .unwrap();
    let mut split_vars = Vec::new();
    for v in vars {
        if let Some(nv) = subst.lookup(v).dbi_view() {
            if nv == dbi {
                split_vars.push(v);
            }
        }
    }
    split_vars.sort();
    for v in split_vars {
        dbg!(v);
        let (s1, s2) = subst.clone().split(v);
        dsp!(&s2);
        let s1 = Substitution::one(to_term.clone()).union(dsp!(s1).drop_by(1));
        subst = s1.union(s2);
        dsp!(&subst);
    }
    // dsp!(&subst);
    subst
}

#[test]
fn test_subst_in_subst() {
    let subst = Substitution::one(Term::from_dbi(2));
    let t = Term::fun_app(0, "foo", [0, 1, 3, 4].map(Term::from_dbi));

    let new_subst = subst_in_subst(subst.clone(), &t, 2, &Term::from_dbi(10));
    assert_eq!(
        dsp!(t.subst(new_subst)),
        Term::fun_app(0, "foo", [10, 1, 10, 4].map(Term::from_dbi))
    );
}

 */
/*
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
pub fn subst_in_case(
    term: Term,
    pat_term: Term,
    x_min: usize,
    x_max: usize,
    y_min: usize,
    y_max: usize,
    diff: isize,
    len: usize,
    subst: Rc<Substitution>,
) -> Term {
    let subst = if diff >= 0 {
        // x <= y
        let diff = diff as usize;
        let pat_subst = Substitution::parallel(
            (y_min..=y_max)
                .map(Term::from_dbi)
                .collect::<Vec<_>>()
                .into_iter(),
        );
        let (s1, s2) = subst.split(x_min);
        println!("s1 = {}", &s1);
        println!("s2 = {}", &s2);
        let s1 = s1.lift_by(len);
        let s2 = s2.drop_by(1);
        println!("s1' = {}", &s1);
        println!("s2' = {}", &s2);
        let final_subst = s1.union(pat_subst.union(s2));
        dsp!("fs = {}", &final_subst);
        final_subst
    } else {
        todo!()
    };
    term.subst(subst)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::syntax::ConHead;
    use std::iter;

    #[test]
    fn test_subst_in_case() {
        // subst: cons @2
        // foo @0 @1 @3 @4
        // foo @2 @3 @1 (cons 3 2)
        let subst = Substitution::one(Term::from_dbi(2));
        let t = Term::fun_app(0, "foo", [0, 1, 3, 4].map(Term::from_dbi));
        let x_min = 0;
        let x_max = 1;
        let len = x_max - x_min + 1;
        let y_min = subst.lookup(x_min).dbi_view().unwrap();
        let diff = (y_min as isize) - (x_min as isize);
        let y_max = ((y_min as isize) + diff) as usize;
        let con_head = ConHead::new("cons", 0);
        let pat = |v1, v0| Pat::cons(con_head.clone(), vec![Pat::Var(v1), Pat::Var(v0)]);
        let pat_term = pat(x_min, x_max).into_term();
        assert_eq!(
            subst_in_case(t, pat_term, x_min, y_max, y_min, y_max, diff, len, subst),
            Term::fun_app(
                0,
                "foo",
                [2, 3, 1]
                    .map(Term::from_dbi)
                    .into_iter()
                    .chain(iter::once(Term::cons(
                        con_head.clone(),
                        [3, 2].map(Term::from_dbi).to_vec()
                    ))),
            )
        );
    }

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
        let term = Term::fun_app(
            0,
            "foo",
            [0, 1, 2, 3, 4, 5]
                .map(Term::from_dbi)
                .into_iter()
                .chain(iter::once(Term::meta(6, Vec::new()))),
        );
        let _x_min = x;
        let x_max = 3;

        let fresh_mi = term.fresh_mi();
        let mut tcs = TypeCheckState::default();
        assert_eq!(
            term.pop_out(&mut tcs, x, Some(x_max)),
            Term::fun_app(
                0,
                "foo",
                vec![
                    Term::from_dbi(0),
                    Term::from_dbi(1),
                    Term::meta(fresh_mi + 0, vec![]),
                    Term::meta(fresh_mi + 1, vec![]),
                    Term::from_dbi(3),
                    Term::from_dbi(4),
                    Term::meta(6, vec![]),
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
                Term::meta(7, vec![]),
                Term::meta(8, vec![]),
                Term::from_dbi(3),
                Term::from_dbi(4),
                Term::meta(6, vec![]),
            ],
        );
        let x_min = x;
        let x_max = 3;

        let max_mi = 6;
        let cons_con = ConHead::new("cons", 0);
        let cons_pat = Pat::cons(
            cons_con.clone(),
            (x_min..=x_max).rev().map(Pat::from_dbi).collect::<Vec<_>>(),
        );
        let cons_term = cons_pat.into_term();
        let mut tcs = TypeCheckState::default();
        assert_eq!(
            term.push_in(&mut tcs, x, Some(x_max), max_mi + 1, cons_term.clone()),
            Term::fun_app(
                0,
                "foo",
                [0, 1, 2, 3, 4, 5]
                    .map(Term::from_dbi)
                    .into_iter()
                    .chain(iter::once(Term::meta(6, Vec::new())))
            )
        );

        // foo ?0 ?1 @1 @3 @4 @2
        // match @2 {
        //     | cons 3 2 => foo @2 @3 @1 @4 @5 (cons @3 @2)
        let term = Term::fun_app(
            0,
            "foo",
            vec![
                Term::meta(0, vec![]),
                Term::meta(1, vec![]),
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

    /*
    #[test]
    fn test_shift_pat_bindings() {
        /*
        pair 1 0 => foo @6 @5 @4 @3 @2 @1 @0
        pair 2 1 => foo @6 @5 @4 @3 @0 @2 @1
        pair 3 2 => foo @6 @5 @4 @1 @0 @3 @2
        pair 4 3 => foo @6 @5 @2 @1 @0 @4 @3
        pair 4 5 => foo @6 @3 @2 @1 @0 @5 @4
        pair 5 6 => foo @4 @3 @2 @1 @0 @6 @5
        pair 6 7 => foo @4 @3 @2 @1 @0 @7 @6
         */
        let x_min = 2;
        let x_max = 3;
        let diff = 4;
        let y_min = x_min + diff;
        let y_max = x_max + diff;
        let len = x_max - x_min + 1;
        let term = Term::fun_app(0, "foo", [6, 5, 4, 1, 0, 3, 2].map(Term::from_dbi));
        assert_eq!(
            shift_pattern_vars(term, x_min, x_max, y_min, y_max, diff as isize, len),
            Term::fun_app(0, "foo", [4, 3, 2, 1, 0, 7, 6].map(Term::from_dbi))
        );

        let x_min = 6usize;
        let x_max = 7usize;
        let diff: isize = -6;
        let y_min = (x_min as isize + diff) as usize;
        let y_max = (x_max as isize + diff) as usize;
        let len = x_max - x_min + 1;
        let term = Term::fun_app(0, "foo", [8, 5, 4, 3, 2, 1, 0, 7, 6].map(Term::from_dbi));
        assert_eq!(
            shift_pattern_vars(term, x_min, x_max, y_min, y_max, diff, len),
            Term::fun_app(0, "foo", [8, 7, 6, 5, 4, 3, 2, 1, 0].map(Term::from_dbi))
        );

        let x_min = 5usize;
        let x_max = 6usize;
        let diff: isize = -4;
        let y_min = (x_min as isize + diff) as usize;
        let y_max = (x_max as isize + diff) as usize;
        let len = x_max - x_min + 1;
        let term = Term::fun_app(0, "foo", [8, 7, 4, 3, 2, 1, 0, 6, 5].map(Term::from_dbi));
        assert_eq!(
            shift_pattern_vars(term, x_min, x_max, y_min, y_max, diff, len),
            Term::fun_app(0, "foo", [8, 7, 6, 5, 4, 3, 0, 2, 1].map(Term::from_dbi))
        );
    }
     */
}
