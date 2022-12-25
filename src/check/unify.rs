use crate::check::meta::MetaSol;
use crate::check::state::TypeCheckState;
use crate::check::{Error, Result};
use crate::ensure;
use crate::syntax::core::{Bind, Tele};
use crate::syntax::core::{
    Case, Closure, Elim, FoldVal, Func, Lambda, Pat, SubstWith, Substitution, Term, ValData,
};
use crate::syntax::{DBI, GI, MI};
use std::cmp::Ordering;

impl TypeCheckState {
    pub fn subtype(&mut self, sub: &Term, sup: &Term) -> Result<()> {
        if !self.trace_tc {
            return self.subtype_impl(sub, sup);
        }
        let depth_ws = self.tc_depth_ws();
        self.tc_deeper();
        debug!("{}Checking subtyping {} <= {}", depth_ws, sub, sup);
        self.subtype_impl(sub, sup).map_err(|e| {
            debug!("{}Error checking subtyping {} <= {}", depth_ws, sub, sup);
            e
        })?;
        if self.current_checking_def.is_some() {
            debug!("{}{} <= {} --> {}", depth_ws, sub, sup, self.meta_ctx());
        } else {
            debug!("{}{} <= {}", depth_ws, sub, sup);
        }
        self.tc_shallower();
        Ok(())
    }

    fn subtype_impl(&mut self, sub: &Term, sup: &Term) -> Result<()> {
        use Term::*;
        match (sub, sup) {
            (Universe(sub_l), Universe(sup_l)) if sub_l <= sup_l => Ok(()),
            (Pi(a, c0), Pi(b, c1)) if a.licit == b.licit => {
                Unify::unify(self, &a.ty, &b.ty)?;
                self.compare_closure(c0, c1, |tcs, a, b| match (a, b) {
                    // Covariance
                    (left, right) if left.is_whnf() && right.is_whnf() => tcs.subtype(left, right),
                    (a, b) => Unify::unify(tcs, a, b),
                })
            }
            (Id(id_a), Id(id_b)) => {
                debug!("Checking id subtyping {} <= {}", id_a, id_b);
                ensure!(
                    id_a.tele.len() == id_b.tele.len(),
                    Error::IdTelePathsLenMismatch
                );
                ensure!(
                    id_a.paths.len() == id_b.paths.len(),
                    Error::IdTelePathsLenMismatch
                );
                ensure!(
                    id_a.tele.len() == id_a.paths.len(),
                    Error::IdTelePathsLenMismatch
                );

                for (i, (a, b)) in id_a.tele.iter().zip(id_b.tele.iter()).enumerate() {
                    let res = Unify::unify(self, &a.ty, &b.ty);
                    if res.is_err() {
                        self.unify_depth_dec(i);
                        res?;
                    }
                    self.unify_depth_inc(1);
                }
                let res = try {
                    Unify::unify(self, &id_a.ty, &id_b.ty)?;
                    Unify::unify(self, &id_a.a1, &id_a.a2)?;
                    Unify::unify(self, &id_b.a1, &id_b.a2)?;
                    Unify::unify(self, &id_a.a1, &id_b.a1)?;
                };
                self.unify_depth_dec(id_a.tele.len());
                res
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

impl Unify for Pat {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        match (left, right) {
            (Pat::Var(x), Pat::Var(y)) if x == y => Ok(()),
            (Pat::Cons(forced1, a_head, a_args), Pat::Cons(forced2, b_head, b_args))
                if forced1 == forced2 && a_head.cons_gi == b_head.cons_gi =>
            {
                Unify::unify(tcs, a_args.as_slice(), b_args.as_slice())
            }
            (Pat::Forced(x), Pat::Forced(y)) => Unify::unify(tcs, x, y),
            (Pat::Absurd, Pat::Absurd) => Ok(()),
            (Pat::Wildcard, Pat::Wildcard) => Ok(()),
            (Pat::Wildcard, Pat::Var(..)) => Ok(()),
            (Pat::Var(..), Pat::Wildcard) => Ok(()),
            (a, b) => Err(Error::DifferentPat(box a.clone(), box b.clone())),
        }
    }
}

impl Unify for Case {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        Unify::unify(tcs, &left.pattern, &right.pattern)?;
        Unify::unify(tcs, &left.body, &right.body)
    }
}

impl Unify for Term {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        debug!("{}Unify {} = {}", tcs.tc_depth_ws(), left, right);
        use Term::*;
        match (left, right) {
            (left, right) if left.is_whnf() && right.is_whnf() => tcs.unify_val(left, right),
            (Redex(Func::Index(i), _, a), Redex(Func::Index(j), _, b)) if a.len() == b.len() => {
                Unify::unify(tcs, i, j)?;
                Unify::unify(tcs, a.as_slice(), b.as_slice())
            }
            (Redex(Func::Lam(_i), _, a), Redex(Func::Lam(_j), _, b)) if a.len() == b.len() => {
                todo!("lambda reduction unification")
            }
            (Match(x, cs1), Match(y, cs2)) => {
                Unify::unify(tcs, x, y)?;
                Unify::unify(tcs, cs1.as_slice(), cs2.as_slice())
            }
            (a, b) => {
                let a_simp = tcs.simplify(a.clone())?;
                let b_simp = tcs.simplify(b.clone())?;
                tcs.unify_val(&a_simp, &b_simp)
                // Unify::unify(tcs, &a_simp, &b_simp)
            }
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
        self.unify_depth_inc(1);
        let res = match (left, right) {
            (Plain(a), Plain(b)) => term_cmp(self, a, b),
        };
        self.unify_depth_dec(1);
        res?;
        Ok(())
    }

    pub fn unify_depth_set(&mut self, n: DBI) {
        self.unify_depth = n;
        debug!("{}Unify depth ={}", self.tc_depth_ws(), n);
    }

    pub fn unify_depth_dec(&mut self, n: DBI) {
        self.unify_depth -= n;
        debug!(
            "{}Unify depth -{} -> {}",
            self.tc_depth_ws(),
            n,
            self.unify_depth
        );
    }

    pub fn unify_depth_inc(&mut self, n: DBI) {
        self.unify_depth += n;
        debug!(
            "{}Unify depth +{} -> {}",
            self.tc_depth_ws(),
            n,
            self.unify_depth
        );
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

impl Unify for Bind {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        Unify::unify(tcs, &left.ty, &right.ty)
    }
}

impl Unify for Tele {
    fn unify(tcs: &mut TypeCheckState, left: &Self, right: &Self) -> Result<()> {
        if left.len() != right.len() {
            return Err(Error::DifferentTeleLen(left.len(), right.len()));
        }
        for (a, b) in left.iter().zip(right.iter()) {
            Unify::unify(tcs, a, b)?;
        }
        Ok(())
    }
}

fn check_solution(meta: MI, rhs: &Term) -> Result<()> {
    rhs.try_fold_val((), |(), v| match v {
        Term::Meta(mi, ..) if mi == &meta => Err(Error::MetaRecursion(*mi)),
        _ => Ok(()),
    })
}

impl TypeCheckState {
    fn unify_meta_with(&mut self, term: &Term, mi: MI) -> Result<()> {
        let depth = self.unify_depth;
        match self.meta_ctx().solution(mi).clone() {
            MetaSol::Unsolved => {
                check_solution(mi, term)?;
                if self.trace_tc {
                    debug!("{}?{} := {} at {}", self.tc_depth_ws(), mi, term, depth);
                }
                let solution = term.clone();
                self.mut_meta_ctx().solve_meta(mi, depth, solution);
                Ok(())
            }
            MetaSol::Solved(ix, sol) => {
                debug!(
                    "{}using ?{} := {} at {}. cd = {}",
                    self.tc_depth_ws(),
                    mi,
                    sol,
                    ix,
                    depth
                );
                match ix.cmp(&depth) {
                    Ordering::Equal => {
                        let sol = self.simplify(*sol)?;
                        Unify::unify(self, &sol, term)
                    }
                    Ordering::Less => {
                        let sol = sol.subst_with(Substitution::raise(depth - ix), self);
                        let sol = self.simplify(sol)?;
                        Unify::unify(self, &sol, term)
                    }
                    Ordering::Greater => {
                        let sol_ix = ix;
                        let term = term
                            .clone()
                            .subst_with(Substitution::raise(sol_ix - depth), self);
                        self.unify_depth_set(sol_ix);
                        let res = Unify::unify(self, &*sol, &term);
                        self.unify_depth_set(depth);
                        res?;
                        Ok(())
                    }
                }
            }
        }
    }

    #[allow(clippy::many_single_char_names)]
    #[track_caller]
    fn unify_val(&mut self, left: &Term, right: &Term) -> Result<()> {
        debug!("{}Unify val {} = {}", self.tc_depth_ws(), left, right);
        use Term::*;
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
            (Cons(c0, a), Cons(c1, b)) if c0.cons_gi == c1.cons_gi => {
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
            (Meta(_, a), _) | (_, Meta(_, a)) if !a.is_empty() => {
                // FIXME: figure out how to handle this case
                Ok(())
            }
            (Var(i, a), Var(j, b)) if i == j => Unify::unify(self, a.as_slice(), b.as_slice()),
            (Id(left), Id(right)) => {
                Unify::unify(self, &left.ty, &right.ty)?;
                Unify::unify(self, &left.tele, &right.tele)?;
                Unify::unify(self, &left.a1, &right.a1)?;
                Unify::unify(self, &left.a2, &right.a2)?;
                Unify::unify(self, &left.a1, &right.a2)
            }
            (a, b) => {
                debug!("Got different terms when unifying {} {}", a, b);

                Err(Error::DifferentTerm(box a.clone(), box b.clone()))
            }
        }
    }
}
