use crate::check::{HasMeta, TypeCheckState};
use crate::syntax::core::redex::SubstWith;
use crate::syntax::core::{DeBruijn, Pat, Substitution, Term, Val};
use crate::syntax::{DBI, MI};
use itertools::Itertools;
use std::rc::Rc;

/// `Simplification` in
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Monad.Base.html#Simplification).
#[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Debug, Hash)]
pub enum Simpl {
    Yes,
    No,
}

impl From<bool> for Simpl {
    fn from(b: bool) -> Self {
        if b {
            Simpl::Yes
        } else {
            Simpl::No
        }
    }
}

impl From<Simpl> for bool {
    fn from(v: Simpl) -> Self {
        match v {
            Simpl::Yes => true,
            Simpl::No => false,
        }
    }
}

impl Default for Simpl {
    fn default() -> Self {
        Simpl::No
    }
}

impl std::ops::Add for Simpl {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match self {
            Simpl::Yes => Simpl::Yes,
            Simpl::No => rhs,
        }
    }
}

impl Pat {
    /// Fig. 6 in Norell's PhD.
    pub(crate) fn match_term(&self, t: &Term) -> Option<Rc<Substitution>> {
        debug!("match_term? [{}/{}]", self, t);
        match (t, self) {
            (v, Pat::Var(_)) => Some(Substitution::one(v.clone())),
            (_, Pat::Forced(..)) => Some(Substitution::id()),
            (Term::Whnf(Val::Cons(con_head, ts)), Pat::Cons(forced, pat_head, ps)) => {
                if !*forced && con_head != pat_head {
                    return None;
                }
                debug_assert_eq!(ts.len(), ps.len());

                ts.iter()
                    .zip(ps.iter())
                    .map(|(u, p)| p.match_term(u))
                    .fold_options(Substitution::id(), Substitution::union)
                // .map(|x| {
                // debug!("lifting by {}", ts.len());
                // x.lift_by(ts.len())
                // })
            }
            (_u, _p) => None,
        }
    }
}

impl Term {
    pub fn pop_out(self, tcs: &mut TypeCheckState, x: DBI, maybe_x_max: Option<DBI>) -> Term {
        let x_min = x;
        let subst = if let Some(x_max) = maybe_x_max {
            let _len = x_max - x_min + 1;
            Substitution::raise(1).union(
                Substitution::parallel((x_min..=x_max).map(|idx| {
                    let meta = tcs.fresh_meta();
                    let mi = meta.as_meta().unwrap().0;
                    tcs.mut_meta_ctx().solve_meta(mi, 0, Term::from_dbi(idx));
                    meta
                }))
                .lift_by(x_min),
            )
        } else {
            Substitution::raise(1).lift_by(x_min)
        };
        self.subst_with(subst, tcs)
    }

    pub fn push_in(
        self,
        tcs: &mut TypeCheckState,
        x: DBI,
        maybe_x_max: Option<DBI>,
        _fresh_mi: MI,
        pat_term: Term,
    ) -> Term {
        let x_min = x;
        // let mut temp_tcs = TypeCheckState::default();
        // temp_tcs.enter_def(0, 0);
        // for mi in 0..fresh_mi {
        //     temp_tcs
        //         .mut_meta_ctx()
        //         .mut_solutions()
        //         .push(MetaSol::Solved(0, box Term::meta(mi, Vec::new())));
        // }
        let subst = if let Some(x_max) = maybe_x_max {
            let len = x_max - x_min + 1;
            let _y = x;
            // for _ in fresh_mi..fresh_mi + len {
            //     temp_tcs
            //         .mut_meta_ctx()
            //         .mut_solutions()
            //         .push(MetaSol::Solved(0, box Term::from_dbi(y)));
            //     y += 1;
            // }
            Substitution::raise(len).union(Substitution::singleton(x, pat_term))
        } else {
            Substitution::one(pat_term).lift_by(x)
        };
        self.subst_with(subst, tcs).inline_meta(tcs).unwrap()
    }

    pub fn push_in_without_pat_subst(
        self,
        tcs: &mut TypeCheckState,
        x: DBI,
        maybe_x_max: Option<DBI>,
        _fresh_mi: MI,
    ) -> Term {
        let x_min = x;
        // let mut temp_tcs = TypeCheckState::default();
        // temp_tcs.enter_def(0, 0);
        let subst = if let Some(x_max) = maybe_x_max {
            let len = x_max - x_min + 1;
            // for mi in 0..fresh_mi {
            //     temp_tcs
            //         .mut_meta_ctx()
            //         .mut_solutions()
            //         .push(MetaSol::Solved(0, box Term::meta(mi, Vec::new())));
            // }
            let _y = x;
            // for _ in fresh_mi..fresh_mi + len {
            // temp_tcs
            //     .mut_meta_ctx()
            //     .mut_solutions()
            //     .push(MetaSol::Solved(0, box Term::from_dbi(y)));
            // y += 1;
            // }
            Substitution::raise(len).lift_by(x)
        } else {
            Substitution::id()
            // Substitution::strengthen(1).lift_by(x + 1)
        };
        self.subst_with(subst, tcs).inline_meta(tcs).unwrap()
    }
}
