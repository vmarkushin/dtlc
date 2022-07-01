use crate::syntax::core::{Pat, Substitution, Term, Val};
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
            (Term::Whnf(Val::Cons(con_head, us)), Pat::Cons(forced, pat_head, ps)) => {
                if !*forced && con_head != pat_head {
                    return None;
                }
                debug_assert_eq!(us.len(), ps.len());
                us.iter()
                    .zip(ps.iter())
                    .map(|(u, p)| p.match_term(u))
                    .fold_options(Substitution::id(), Substitution::union)
            }
            (_u, _p) => None,
        }
    }
}
