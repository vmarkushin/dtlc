use crate::check::TypeCheckState;
use crate::syntax::core::{Bind, Closure, Elim, Func, Name, SubstWith, Substitution, Term, Var};
use crate::syntax::UID;
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::DerefMut;

pub trait SubstituteFreeVars<'a, U = UID, T = Term, S = &'a mut TypeCheckState> {
    fn subst_free_vars_with(&mut self, subst: &HashMap<U, T>, state: S, depth: usize);
}

impl<'a, T: SubstituteFreeVars<'a, UID, Term>, UID, Term> SubstituteFreeVars<'a, UID, Term>
    for Box<T>
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<UID, Term>,
        state: &'a mut TypeCheckState,
        depth: usize,
    ) {
        self.as_mut().subst_free_vars_with(subst, state, depth);
    }
}

impl<'a, T, U, Term> SubstituteFreeVars<'a, U, Term> for Bind<T>
where
    U: Eq + PartialEq + Hash + From<UID> + Into<UID> + Copy,
    T: SubstituteFreeVars<'a, U, Term>,
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<U, Term>,
        state: &'a mut TypeCheckState,
        depth: usize,
    ) {
        self.ty.subst_free_vars_with(subst, state, depth);
        if subst.contains_key(&U::from(self.name)) {
            self.name = 0;
        }
    }
}

impl<U> SubstituteFreeVars<'_, U, Term> for Elim
where
    U: Eq + PartialEq + Hash + From<UID> + Into<UID> + Copy,
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<U, Term>,
        state: &'_ mut TypeCheckState,
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

impl<U> SubstituteFreeVars<'_, U, Term> for Closure
where
    U: Eq + PartialEq + Hash + From<UID> + Into<UID> + Copy,
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<U, Term>,
        state: &'_ mut TypeCheckState,
        depth: usize,
    ) {
        let Closure::Plain(p) = self;
        // p.subst_free_vars_with(subst, state, depth + 1);
        p.subst_free_vars_with(subst, state, depth + 1);
    }
}

impl<U> SubstituteFreeVars<'_, U, Term> for Term
where
    U: Eq + PartialEq + Hash + Into<UID> + From<UID> + Copy,
{
    fn subst_free_vars_with(
        &mut self,
        subst: &HashMap<U, Term>,
        state: &'_ mut TypeCheckState,
        depth: usize,
    ) {
        match self {
            Term::Var(Var::Meta(_), args) => {
                args.subst_free_vars_with(subst, state, depth);
            }
            Term::Var(var, args) => {
                args.subst_free_vars_with(subst, state, depth);
                match var {
                    Var::Single(Name::Free(uid)) | Var::Twin(Name::Free(uid), _) if *uid != 0 => {
                        if let Some(term) = subst.get(&U::from(*uid)).cloned() {
                            // let new_dbi = *ix + depth;
                            // *var = Var::bound(new_dbi);
                            *self = term.subst_with(Substitution::id().lift_by(depth), state)
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
                    _ => return,
                };
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

macro_rules! impl_subst_free_vars_with_for_vec {
    ($t: ty) => {
        /*
            fn subst_free_vars_with(
            &mut self,
            subst: &HashMap<U, Term>,
            state: &'_ mut TypeCheckState,
            depth: usize,
        )
             */
        impl<'a, U> SubstituteFreeVars<'a, U> for Vec<$t>
        where
            U: Eq + PartialEq + Hash + Into<UID> + From<UID> + Copy,
        {
            fn subst_free_vars_with(
                &mut self,
                subst: &HashMap<U, Term>,
                state: &'a mut TypeCheckState,
                depth: usize,
            ) {
                self.into_iter()
                    .map(|e| e.subst_free_vars_with(subst, state, depth))
                    .collect()
            }
        }
    };
}

impl_subst_free_vars_with_for_vec!(Term);
impl_subst_free_vars_with_for_vec!(Elim);
// impl_subst_free_vars_with_for_vec!(Constraint);
// impl_subst_free_vars_with_for_vec!(Pat<DBI, Term>);
