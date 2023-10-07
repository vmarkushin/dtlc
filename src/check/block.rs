use crate::syntax::core::Elim;
use crate::syntax::MI;
use std::fmt::{Display, Error, Formatter};
use std::ops::Add;

/// A modified version of
/// [this](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.Syntax.Internal.html#NotBlocked)
/// thing in Agda.
#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub enum NotBlocked {
    /// The `Elim` is neutral and blocks a pattern match.
    OnElim(Elim),
    /// Not enough arguments were supplied to complete the matching.
    UnderApplied,
    /// We matched an absurd clause, results in a neutral `Def`.
    AbsurdMatch,
    /// We ran out of clauses, all considered clauses
    /// produced an actual mismatch.
    /// This can happen when try to reduce a function application,
    /// but we are still missing some function clauses.
    /// See `Agda.TypeChecking.Patterns.Match`.
    MissingClauses,
    /// Reduction was not blocked, we reached a whnf
    /// which can be anything, but a stuck `Whnf::Redex`.
    NotBlocked,
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub enum Blocker {
    /// Blocked by meta.
    OnMeta(MI),
}

impl Display for Blocker {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match self {
            Blocker::OnMeta(m) => write!(f, "blocked by meta {:?}", m),
        }
    }
}

impl Default for NotBlocked {
    fn default() -> Self {
        NotBlocked::NotBlocked
    }
}

impl Add for NotBlocked {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (NotBlocked::NotBlocked, b) => b,
            // `MissingClauses` is dominant (absorptive)
            (NotBlocked::MissingClauses, _) | (_, NotBlocked::MissingClauses) => {
                NotBlocked::MissingClauses
            }
            // `StuckOn` is second strongest
            (NotBlocked::OnElim(e), _) | (_, NotBlocked::OnElim(e)) => NotBlocked::OnElim(e),
            (b, _) => b,
        }
    }
}

impl Display for NotBlocked {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match self {
            NotBlocked::OnElim(e) => write!(f, "blocked on argument `{}`", e),
            NotBlocked::UnderApplied => write!(f, "missing necessary arguments"),
            NotBlocked::AbsurdMatch => write!(f, "trying to instantiate an absurd match"),
            NotBlocked::MissingClauses => write!(f, "cannot find a suitable clause"),
            NotBlocked::NotBlocked => {
                write!(f, "not blocked by anything")
            }
        }
    }
}

impl NotBlocked {
    pub fn is_elim(&self) -> bool {
        matches!(self, NotBlocked::OnElim(_))
    }
}

/// Something where a meta variable may block reduction.
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.Syntax.Internal.html#Blocked).
#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub enum Blocked<T> {
    Yes(Blocker, T),
    No(NotBlocked, T),
}

// impl Add for Blocked<()> {
//     type Output = Self;
//
//     fn add(self, rhs: Self) -> Self::Output {
//         Blocked::new(self.stuck + rhs.stuck, ())
//     }
// }

impl<T> Blocked<T> {
    // pub fn is_meta(&self) -> Option<MI> {
    //     self.stuck.is_meta()
    // }

    // pub fn is_elim(&self) -> bool {
    //     self.stuck.is_elim()
    // }

    pub fn no(status: NotBlocked, anyway: T) -> Self {
        Self::No(status, anyway)
    }

    pub fn yes(blocker: Blocker, anyway: T) -> Self {
        Self::Yes(blocker, anyway)
    }

    pub fn ignore_blocking(self) -> T {
        match self {
            Blocked::Yes(_, anyway) => anyway,
            Blocked::No(_, anyway) => anyway,
        }
    }

    // pub fn map_anyway<R>(self, f: impl FnOnce(T) -> R) -> Blocked<R> {
    //     Blocked::new(self.stuck, f(self.anyway))
    // }
}

impl<T: Display> Display for Blocked<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match self {
            Blocked::Yes(b, t) => write!(f, "blocked by {}: {}", b, t),
            Blocked::No(b, t) => write!(f, "not blocked: {}: {}", b, t),
        }
    }
}
