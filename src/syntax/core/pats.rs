use crate::check::TypeCheckState;
use crate::syntax::core::redex::SubstWith;
use crate::syntax::core::term::BoundFreeVars;
use crate::syntax::core::{DeBruijn, Pat, Substitution, Term, Var};
use crate::syntax::{DBI, UID};
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
            (Term::Cons(con_head, ts), Pat::Cons(forced, pat_head, ps)) => {
                // skipping (implicit) type params passed to the constructor
                let ts = &ts[ts.len() - ps.len()..];
                if !*forced && con_head != pat_head {
                    return None;
                }
                debug_assert_eq!(ts.len(), ps.len());

                let ps_len = ps.len();
                if ps_len > 0 {
                    let vars = ps.last().unwrap().vars();
                    debug_assert_eq!(vars.len(), 1);
                    let x_min = vars[0];
                    let subst = ts
                        .iter()
                        .zip(ps.iter())
                        .map(|(u, p)| p.match_term(u))
                        .fold_options(Substitution::id(), Substitution::union)?;
                    Some(Substitution::concat(
                        (0..x_min).map(Term::from_dbi),
                        Substitution::raise(x_min).union(subst),
                    ))
                } else {
                    Some(Substitution::id())
                }
            }
            (_u, _p) => None,
        }
    }
}

impl Term {
    pub fn pop_out_non_var(self, tcs: &mut TypeCheckState, x: DBI, x_max: DBI) -> Term {
        let x_min = x;
        let subst = Substitution::raise(0).union(
            Substitution::parallel((x_min..=x_max).map(|_| tcs.fresh_free_var())).lift_by(x_min),
        );
        self.subst_with(subst, tcs)
    }

    pub fn pop_out(self, tcs: &mut TypeCheckState, x: DBI, maybe_x_max: Option<DBI>) -> Term {
        let x_min = x;
        let subst = if let Some(x_max) = maybe_x_max {
            let _len = x_max - x_min + 1;
            Substitution::raise(1).union(
                Substitution::parallel((x_min..=x_max).map(|_| tcs.fresh_free_var()))
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
        from_uid: UID,
        pat_term: Term,
    ) -> Term {
        let x_min = x;
        let (subst, vars) = if let Some(x_max) = maybe_x_max {
            let len = x_max - x_min + 1;
            let mut y = x;
            trace!("[push_in] Binding vars from {}", Var::free(from_uid));

            let vars = (from_uid..from_uid + len)
                .rev()
                .map(|uid| {
                    let x = (uid, y);
                    y += 1;
                    x
                })
                .collect();
            (
                Substitution::raise(len).union(Substitution::singleton(x, pat_term)),
                vars,
            )
        } else {
            (Substitution::one(pat_term).lift_by(x), Default::default())
        };
        let mut t = self.subst_with(subst, tcs);
        t.bound_free_vars(&vars, 0);
        t
    }

    pub fn push_in_without_pat_subst(
        self,
        tcs: &mut TypeCheckState,
        x: DBI,
        maybe_x_max: Option<DBI>,
        from_uid: UID,
    ) -> Term {
        let x_min = x;
        let (subst, vars) = if let Some(x_max) = maybe_x_max {
            let len = x_max - x_min + 1;
            let mut y = x;

            trace!(
                "[push_in_without_pat_subst] Binding vars from {}",
                Var::free(from_uid)
            );
            let vars = (from_uid..from_uid + len)
                .rev()
                .map(|uid| {
                    let x = (uid, y);
                    y += 1;
                    x
                })
                .collect();

            (Substitution::raise(len).lift_by(x), vars)
        } else {
            (Substitution::id(), Default::default())
        };
        trace!("[push_in_without_pat_subst] formed subst {}", subst);
        let mut t = self.subst_with(subst, tcs);
        t.bound_free_vars(&vars, 0);
        t
    }

    pub fn push_in_without_pat_subst_non_var(
        self,
        tcs: &mut TypeCheckState,
        x: DBI,
        x_max: DBI,
        from_uid: UID,
    ) -> Term {
        let x_min = x;
        let (subst, vars) = {
            let len = x_max - x_min + 1;
            let mut y = x;

            trace!(
                "[push_in_without_pat_subst_non_var] Binding vars from {}",
                Var::free(from_uid)
            );
            let vars = (from_uid..from_uid + len)
                .rev()
                .map(|uid| {
                    let x = (uid, y);
                    y += 1;
                    x
                })
                .collect();

            (Substitution::raise(len).lift_by(x), vars)
        };
        trace!("[push_in_without_pat_subst_non_var] formed subst {}", subst);
        let mut t = self.subst_with(subst, tcs);
        t.bound_free_vars(&vars, 0);
        t
    }
}

#[cfg(test)]
mod tests {
    use crate::check::TypeCheckState;
    use crate::syntax::core::{DeBruijn, Pat, Subst, Term, Var};
    use crate::syntax::ConHead;
    use std::sync::atomic::Ordering;

    #[test]
    fn test_pop_term() {
        let con_head = ConHead::new("cons", 0);
        let term = Term::cons(con_head.clone(), [2, 0].map(Term::from_dbi).to_vec());
        let mut tcs = TypeCheckState::default();
        let fresh_uid = tcs.next_uid.load(Ordering::Relaxed);
        let term_new = term.clone().pop_out_non_var(&mut tcs, 0, 0);
        assert_eq!(
            term_new,
            Term::cons(
                con_head,
                vec![Term::from_dbi(1), Term::Var(Var::free(0), vec![])]
            )
        );
        assert_eq!(
            term_new.push_in_without_pat_subst_non_var(&mut tcs, 0, 0, fresh_uid),
            term,
        );
    }

    #[test]
    fn gen_match_subst() {
        let con_head = ConHead::new("cons", 0);
        let pat = Pat::cons(con_head.clone(), [4, 3, 2].map(Pat::Var).to_vec());
        let subst = pat
            .match_term(&Term::cons(
                con_head.clone(),
                [12, 11, 10].map(Term::from_dbi).to_vec(),
            ))
            .unwrap();
        let term = Term::cons(
            con_head.clone(),
            [0, 1, 2, 3, 4, 5, 6].map(Term::from_dbi).to_vec(),
        );
        assert_eq!(
            term.subst(subst),
            Term::cons(
                con_head.clone(),
                [0, 1, 10, 11, 12, 5 - 3, 6 - 3]
                    .map(Term::from_dbi)
                    .to_vec()
            )
        );

        let pat = Pat::cons(con_head.clone(), [2].map(Pat::Var).to_vec());
        let subst = pat
            .match_term(&Term::cons(
                con_head.clone(),
                [10].map(Term::from_dbi).to_vec(),
            ))
            .unwrap();
        let term = Term::cons(
            con_head.clone(),
            [0, 1, 2, 3, 4].map(Term::from_dbi).to_vec(),
        );
        assert_eq!(
            term.subst(subst),
            Term::cons(
                con_head,
                [0, 1, 10, 3 - 1, 4 - 1].map(Term::from_dbi).to_vec()
            )
        );
    }
}
