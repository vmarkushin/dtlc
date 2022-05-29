use crate::syntax::core::Elim;
use crate::syntax::MI;
use std::fmt::{Display, Error, Formatter};
use std::ops::Add;

/// A modified version of
/// [this](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.Syntax.Internal.html#NotBlocked)
/// thing in Agda.
#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone)]
pub enum Stuck {
    /// Blocked by meta.
    OnMeta(MI),
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

impl Default for Stuck {
    fn default() -> Self {
        Stuck::NotBlocked
    }
}

impl Add for Stuck {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Stuck::NotBlocked, b) => b,
            // Primary in `Blocked`
            (Stuck::OnMeta(m), _) | (_, Stuck::OnMeta(m)) => Stuck::OnMeta(m),
            // `MissingClauses` is dominant (absorptive)
            (Stuck::MissingClauses, _) | (_, Stuck::MissingClauses) => Stuck::MissingClauses,
            // `StuckOn` is second strongest
            (Stuck::OnElim(e), _) | (_, Stuck::OnElim(e)) => Stuck::OnElim(e),
            (b, _) => b,
        }
    }
}

impl Display for Stuck {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match self {
            Stuck::OnMeta(m) => write!(f, "blocked by meta {:?}", m),
            Stuck::OnElim(e) => write!(f, "blocked on argument `{}`", e),
            Stuck::UnderApplied => write!(f, "missing necessary arguments"),
            Stuck::AbsurdMatch => write!(f, "trying to instantiate an absurd match"),
            Stuck::MissingClauses => write!(f, "cannot find a suitable clause"),
            Stuck::NotBlocked => write!(f, "not blocked by anything, you may have found a bug"),
        }
    }
}

impl Stuck {
    pub fn is_meta(&self) -> Option<MI> {
        match self {
            Stuck::OnMeta(m) => Some(*m),
            _ => None,
        }
    }
}

/// Something where a meta variable may block reduction.
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.Syntax.Internal.html#Blocked).
#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, Clone, Default)]
pub struct Blocked<T> {
    pub stuck: Stuck,
    /// The thing blocked by `stuck`.
    pub anyway: T,
}

impl Add for Blocked<()> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Blocked::new(self.stuck + rhs.stuck, ())
    }
}

impl<T> Blocked<T> {
    pub fn is_meta(&self) -> Option<MI> {
        self.stuck.is_meta()
    }

    pub fn new(stuck: Stuck, anyway: T) -> Self {
        Self { stuck, anyway }
    }

    pub fn map_anyway<R>(self, f: impl FnOnce(T) -> R) -> Blocked<R> {
        Blocked::new(self.stuck, f(self.anyway))
    }
}

impl<T: Display> Display for Blocked<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(
            f,
            "I'm not sure if I should give `{}` because I'm {}.",
            self.anyway, self.stuck
        )
    }
}
