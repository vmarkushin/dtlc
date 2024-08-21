use crate::check::TypeCheckState;
use crate::syntax::core::{Bind, Closure, Elim, Func, Name, SubstCtx, SubstWith, Substitution, Term, Var};
use crate::syntax::{DBI, UID};
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::DerefMut;

pub trait SubstituteFreeVars<U = UID, T = Term, C = TypeCheckState, R = Term> {
    fn subst_free_vars_with(&mut self, subst: &HashMap<U, T>, state: &mut C, depth: usize);

    // Used for variables
    fn subst_free_vars_with_to(&self, subst: &HashMap<U, T>, state: &mut C, depth: usize) -> Option<R> { None }
}

impl<C, T, UID, Term> SubstituteFreeVars<UID, Term, C>
for Box<T>
where
    T: SubstituteFreeVars<UID, Term, C>,
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<UID, Term>,
        state: &mut C,
        depth: usize,
    ) {
        self.as_mut().subst_free_vars_with(subst, state, depth);
    }
}

impl<C, T, U, Term> SubstituteFreeVars<U, Term, C> for Bind<T>
where
    U: Eq + PartialEq + Hash + From<UID> + Into<UID> + Copy,
    T: SubstituteFreeVars<U, Term, C>,
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<U, Term>,
        state: &mut C,
        depth: usize,
    ) {
        self.ty.subst_free_vars_with(subst, state, depth);
        if subst.contains_key(&U::from(self.name)) {
            self.name = 0;
        }
    }
}

impl<U, C> SubstituteFreeVars<U, Term, C> for Elim
where
    C: SubstCtx,
    U: Eq + PartialEq + Hash + From<UID> + Into<UID> + Copy,
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<U, Term>,
        state: &mut C,
        depth: usize,
    ) {
        match self {
            Elim::App(a) => {
                (&mut *a).subst_free_vars_with(subst, state, depth);
            }
            Elim::Proj(_) => {}
        }
    }
}

impl<U, C> SubstituteFreeVars<U, Term, C> for Closure
where
    C: SubstCtx,
    U: Eq + PartialEq + Hash + From<UID> + Into<UID> + Copy,
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<U, Term>,
        state: &mut C,
        depth: usize,
    ) {
        let Closure::Plain(p) = self;
        p.subst_free_vars_with(subst, state, depth + 1);
    }
}

impl<C> SubstituteFreeVars<BindSubst, DBI, C> for Var
{
    fn subst_free_vars_with(&mut self, _subst: &HashMap<BindSubst, DBI>, _state: &mut C, _depth: usize) {}
    fn subst_free_vars_with_to(&self, subst: &HashMap<BindSubst, DBI>, _state: &mut C, depth: usize) -> Option<Term> {
        match self {
            Var::Single(Name::Free(uid))  if *uid != 0 => {
                if let Some(dbi) = subst.get(&BindSubst(*uid)).cloned() {
                    let new_dbi = dbi + depth;
                    return Some(Term::bound_var(new_dbi));
                }
            }
            Var::Twin(Name::Free(uid), twin)  if *uid != 0 => {
                if let Some(dbi) = subst.get(&BindSubst(*uid)).cloned() {
                    let new_dbi = dbi + depth;
                    return Some(Term::Var(Var::twin_bound(new_dbi, *twin), vec![]));
                }
            }
            _ => (),
        };
        None
    }
}

impl<U, C> SubstituteFreeVars<U, Term, C> for Var
where
    C: SubstCtx,
    U: Eq + PartialEq + Hash + Into<UID> + From<UID> + Copy,

{
    fn subst_free_vars_with(&mut self, subst: &HashMap<U, Term>, state: &mut C, depth: usize) {}
    fn subst_free_vars_with_to(&self, subst: &HashMap<U, Term>, state: &mut C, depth: usize) -> Option<Term> {
        match self {
            Var::Single(Name::Free(uid)) | Var::Twin(Name::Free(uid), _) if *uid != 0 => {
                if let Some(term) = subst.get(&U::from(*uid)).cloned() {
                    // let new_dbi = *ix + depth;
                    // *var = Var::bound(new_dbi);
                    return Some(term.subst_with(Substitution::id().lift_by(depth), state));
                }
            }
            //  => {
            //     if let Some(term) = subst.get(uid).cloned() {
            //         // let new_dbi = *term + depth;
            //         // trace!("bound {} := {}", uid, new_dbi);
            //         // *var = Var::Twin(Name::Bound(new_dbi), *twin);
            //         *self = term;
            //     }
            // }
            _ => (),
        };
        None
    }
}

impl<U, C> SubstituteFreeVars<U, Term, C> for Term
where
    C: SubstCtx,
    U: Eq + PartialEq + Hash + Into<UID> + From<UID> + Copy,
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<U, Term>,
        state: &mut C,
        depth: usize,
    ) {
        match self {
            Term::Var(Var::Meta(_), args) => {
                args.subst_free_vars_with(subst, state, depth);
            }
            Term::Var(var, args) => {
                args.subst_free_vars_with(subst, state, depth);
                var.subst_free_vars_with(subst, state, depth);
            }
            Term::Redex(Func::Lam(lam), _, args) => {
                lam.0.subst_free_vars_with(subst, state, depth);
                lam.1.subst_free_vars_with(subst, state, depth);
                args.subst_free_vars_with(subst, state, depth);
            }
            Term::Redex(Func::Index(_), _, args) => {
                args.subst_free_vars_with(subst, state, depth);
            }
            Term::Match(t, tt, cases) => {
                t.subst_free_vars_with(subst, state, depth);
                tt.subst_free_vars_with(subst, state, depth);
                for case in cases {
                    // trace!(target: "unify", "bound free vars in case {case} with {vars:?}, depth: {depth}");
                    let len = case.pattern.vars().len();
                    if len == 0 {
                        case.body.subst_free_vars_with(subst, state, depth);
                        // trace!(target: "unify", "bound free vars in case: {}", case.body);
                    } else {
                        // let min = *case.pattern.vars().last().unwrap();
                        let vars_new = subst
                            .clone()
                            .into_iter()
                            .map(|(k, v)| (k, v.subst_with(Substitution::id().lift_by(len), state)))
                            // .map(|(k, v)| (k, v + len))
                            .collect();
                        case.body.subst_free_vars_with(&vars_new, state, depth);
                    }
                }
            }
            Term::Universe(_) => {}
            Term::Data(data) => {
                data.args.subst_free_vars_with(subst, state, depth);
            }
            Term::Pi(x, ret) => {
                x.subst_free_vars_with(subst, state, depth);
                ret.subst_free_vars_with(subst, state, depth);
            }
            Term::Lam(lam) => {
                lam.0.subst_free_vars_with(subst, state, depth);
                lam.1.subst_free_vars_with(subst, state, depth);
            }
            Term::Cons(_, args) => {
                args.subst_free_vars_with(subst, state, depth);
            }
            Term::Id(_id) => {
                todo!("bound_free_vars for id")
            }
            Term::Refl(t) => {
                t.subst_free_vars_with(subst, state, depth);
            }
            Term::Ap(_tele, _ps, _t) => {
                // tele.subst_free_vars_with(subst, state, depth);
                // ps.subst_free_vars_with(subst, state, depth);
                // t.subst_free_vars_with(subst, state, depth);
                todo!("bound_free_vars for ap")
            }
        }
    }
}

impl<C, U, T, R> SubstituteFreeVars<U, R, C> for Vec<T>
where
    U: Eq + PartialEq + Hash + Into<UID> + From<UID> + Copy,
    T: SubstituteFreeVars<U, R, C>,
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<U, R>,
        state: &mut C,
        depth: usize,
    ) {
        self.into_iter()
            .map(|e| e.subst_free_vars_with(subst, state, depth))
            .collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BindSubst(DBI);

