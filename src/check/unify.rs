use crate::check::meta::MetaSol;
use crate::check::state::TypeCheckState;
use crate::check::{Error, Result};
use crate::syntax::core::{
    Closure, Elim, FoldVal, Func, Lambda, Subst, Substitution, Term, Val, ValData,
};
use crate::syntax::{GI, MI};
use std::cmp::Ordering;

impl TypeCheckState {
    pub fn subtype(&mut self, sub: &Val, sup: &Val) -> Result<()> {
        if !self.trace_tc {
            return self.subtype_impl(sub, sup);
        }
        let depth_ws = self.tc_depth_ws();
        self.tc_deeper();
        debug!("{}Checking {} <: {}", depth_ws, sub, sup);
        self.subtype_impl(sub, sup).map_err(|e| {
            debug!("{}Subtyping {} <: {}", depth_ws, sub, sup);
            e
        })?;
        if self.current_checking_def.is_some() {
            debug!("{}{} <: {} --> {}", depth_ws, sub, sup, self.meta_ctx());
        } else {
            debug!("{}{} <: {}", depth_ws, sub, sup);
        }
        self.tc_shallower();
        Ok(())
    }

    fn subtype_impl(&mut self, sub: &Val, sup: &Val) -> Result<()> {
        use Val::*;
        match (sub, sup) {
            (Universe(sub_l), Universe(sup_l)) if sub_l <= sup_l => Ok(()),
            (Pi(a, c0), Pi(b, c1)) if a.licit == b.licit => {
                Unify::unify(self, &a.ty, &b.ty)?;
                self.compare_closure(c0, c1, |tcs, a, b| match (a, b) {
                    // Covariance
                    (Term::Whnf(left), Term::Whnf(right)) => tcs.subtype(left, right),
                    (a, b) => Unify::unify(tcs, a, b),
                })
            }
            (e, t) => Unify::unify(self, e, t),
        }
    }
}

pub trait Unify {
    /// Conversion check, maybe can solve metas.
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()>;
}

impl<T: Unify> Unify for [T] {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        for (a, b) in left.iter().zip(right.iter()) {
            Unify::unify(tcs, a, b)?;
        }
        Ok(())
    }
}

impl<T: Unify> Unify for Box<T> {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        Unify::unify(tcs, &**left, &**right)
    }
}

impl Unify for Term {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        use Term::*;
        match (left, right) {
            (Whnf(left), Whnf(right)) => Unify::unify(tcs, left, right),
            (Redex(Func::Index(i), _, a), Redex(Func::Index(j), _, b)) if a.len() == b.len() => {
                Unify::unify(tcs, i, j)?;
                Unify::unify(tcs, a.as_slice(), b.as_slice())
            }
            (Redex(Func::Lam(_i), _, a), Redex(Func::Lam(_j), _, b)) if a.len() == b.len() => {
                todo!("lambda reduction unification")
            }
            (a, b) => Err(Error::DifferentTerm(box a.clone(), box b.clone())),
        }
    }
}

impl Unify for GI {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        if left != right {
            let left_name = tcs.def(*left).def_name().clone();
            let right_name = tcs.def(*right).def_name().clone();
            Err(Error::DifferentName(left_name, right_name))
        } else {
            Ok(())
        }
    }
}

impl Unify for Elim {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        use Elim::*;
        match (left, right) {
            (Proj(a), Proj(b)) if a == b => Ok(()),
            (App(a), App(b)) => Unify::unify(tcs, a, b),
            (a, b) => Err(Error::DifferentElim(box a.clone(), box b.clone())),
        }
    }
}

impl TypeCheckState {
    fn compare_closure(
        &mut self,
        left: &Closure,
        right: &Closure,
        term_cmp: impl FnOnce(&mut TypeCheckState, &Term, &Term) -> Result<()>,
    ) -> Result<()> {
        use Closure::*;
        self.unify_depth += 1;
        let res = match (left, right) {
            (Plain(a), Plain(b)) => term_cmp(self, &**a, &**b),
        };
        self.unify_depth -= 1;
        res?;
        Ok(())
    }
}

impl Unify for Closure {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        tcs.compare_closure(left, right, Unify::unify)
    }
}

impl Unify for ValData {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        Unify::unify(tcs, &left.def, &right.def)?;
        Unify::unify(tcs, left.args.as_slice(), right.args.as_slice())
    }
}

impl Unify for Val {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        tcs.unify_val(left, right)
    }
}

fn check_solution(meta: MI, rhs: &Val) -> Result<()> {
    rhs.try_fold_val((), |(), v| match v {
        Val::Meta(mi, ..) if mi == &meta => Err(Error::MetaRecursion(*mi)),
        _ => Ok(()),
    })
}

impl TypeCheckState {
    fn unify_meta_with(&mut self, term: &Val, mi: MI) -> Result<()> {
        let depth = self.unify_depth;
        match self.meta_ctx().solution(mi) {
            MetaSol::Unsolved => {
                check_solution(mi, term)?;
                if self.trace_tc {
                    debug!("{}?{} := {}", self.tc_depth_ws(), mi, term);
                }
                let solution = Term::Whnf(term.clone());
                self.mut_meta_ctx().solve_meta(mi, depth, solution);
                Ok(())
            }
            MetaSol::Solved(ix, sol) => match ix.cmp(&depth) {
                Ordering::Equal => {
                    let sol = *sol.clone();
                    let sol = self.simplify(sol)?;
                    Unify::unify(self, &sol, term)
                }
                Ordering::Less => {
                    let sol = sol.clone().subst(Substitution::raise(depth - *ix));
                    let sol = self.simplify(sol)?;
                    Unify::unify(self, &sol, term)
                }
                Ordering::Greater => {
                    let sol_ix = *ix;
                    let term = term.clone().subst(Substitution::raise(sol_ix - depth));
                    let sol = *sol.clone();
                    self.unify_depth = sol_ix;
                    let res = Unify::unify(self, &sol, &term);
                    self.unify_depth = depth;
                    res?;
                    Ok(())
                }
            },
        }
    }

    #[allow(clippy::many_single_char_names)]
    fn unify_val(&mut self, left: &Val, right: &Val) -> Result<()> {
        use Val::*;
        match (left, right) {
            (Universe(sub_l), Universe(sup_l)) if sub_l == sup_l => Ok(()),
            (Data(left), Data(right)) => Unify::unify(self, left, right),
            (Pi(a, c0), Pi(b, c1)) if a.licit == b.licit => {
                Unify::unify(self, &a.ty, &b.ty)?;
                Unify::unify(self, c0, c1)
            }
            (Lam(Lambda(a, c0)), Lam(Lambda(b, c1))) if a.licit == b.licit => {
                Unify::unify(self, &a.ty, &b.ty)?;
                Unify::unify(self, c0, c1)
            }
            (Cons(c0, a), Cons(c1, b)) if c0.cons_ix == c1.cons_ix => {
                Unify::unify(self, a.as_slice(), b.as_slice())
            }
            (Meta(i, a), Meta(j, b)) => {
                if i == j {
                    Unify::unify(self, a.as_slice(), b.as_slice())
                } else if a.is_empty() {
                    self.unify_meta_with(right, *i)
                } else if b.is_empty() {
                    self.unify_meta_with(left, *j)
                } else {
                    unimplemented!()
                }
            }
            (Meta(i, a), b) | (b, Meta(i, a)) if a.is_empty() => self.unify_meta_with(b, *i),
            (Var(i, a), Var(j, b)) if i == j => Unify::unify(self, a.as_slice(), b.as_slice()),
            (a, b) => Err(Error::DifferentTerm(
                box Term::Whnf(a.clone()),
                box Term::Whnf(b.clone()),
            )),
        }
    }
}
