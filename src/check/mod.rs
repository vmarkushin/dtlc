use crate::check::block::Blocker;
pub use crate::check::norm::try_match;
use crate::syntax::abs::{Expr, Pat as PatA};
use crate::syntax::core::{pretty, Elim, Pat, Pretty, Term};
use crate::syntax::{Ident, Loc, Universe, MI};
pub use case::{CaseTree, Clause, Constraint, LshProblem};
pub use meta::{HasMeta, MetaSol};
pub use state::TypeCheckState;
use std::fmt;
use std::fmt::{Display, Formatter};
pub use unify::Unify;

mod block;
mod case;
mod decls;
mod id;
mod infer;
mod meta;
mod norm;
mod state;
pub mod unification;
mod unify;

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("`{0}`")]
    Wrapped(Box<Self>, Loc),
    #[error("Not head: `{0}`")]
    NotHead(Expr),
    #[error("Not Π: `{0}`")]
    NotPi(Term, Loc),
    #[error("An elimination is not a term: `{0}`")]
    NotTerm(String),
    #[error("Meta recursion: `{0}`")]
    MetaRecursion(MI),
    #[error("Haven't solved meta: `{0}`")]
    MetaUnsolved(MI),
    #[error("Different universe: `{1}` and `{2}`")]
    DifferentUniverse(Loc, Universe, Universe),
    #[error("Expected `{0}`, got `{1}`")]
    DifferentTerm(Box<Term>, Box<Term>),
    #[error("Expected `{0}`, got `{1}`")]
    DifferentPat(Box<Pat>, Box<Pat>),
    #[error("Different elim: `{0}` and `{1}`")]
    DifferentElim(Box<Elim>, Box<Elim>),
    #[error("Different name: `{0}` and `{1}`")]
    DifferentName(Ident, Ident),
    #[error("Π components should be of type `Type`, but got: `{0}` and `{1}`")]
    InvalidPi(Box<Term>, Box<Term>),
    #[error("Blocked: {0}")]
    Blocked(Blocker, Box<Term>),
    #[error("Expected universe for data declaration `{0}`")]
    ExpectedUniverseForData(Ident),
    #[error("Non-exhaustive `match` expression")]
    NonExhaustiveMatch,
    #[error("Expected `!`, but got `{0}`")]
    ExpectedAbsurd(Box<PatA>),
    #[error("Expected right-hand side")]
    UnexpectedRhs,
    #[error("Too many patterns used in a clause")]
    TooManyPatterns,
    #[error("Not enough patterns used in a clause")]
    TooFewPatterns,
    #[error("IdTelePathsLenMismatch")]
    IdTelePathsLenMismatch,
    #[error("Expected Id, but got `{0}`")]
    NotId(Box<Term>, Loc),
    #[error("Expected empty telescope or substitutions")]
    IdTeleOrSubstsNotEmpty,
    #[error("Not refl {0}")]
    NotRefl(Box<Term>, Loc),
    #[error("Different telescope lengths: `{0}` and `{1}`")]
    DifferentTeleLen(usize, usize),
    #[error("RigidRigidMismatch")]
    RigidRigidMismatch,
    #[error("SpineMismatch")]
    SpineMismatch,
    #[error("Occurrence")]
    Occurrence,
}

pub type Result<T, E = Error> = std::result::Result<T, E>;

impl Error {
    pub fn wrap(self, info: Loc) -> Self {
        Error::Wrapped(Box::new(self), info)
    }
}

impl Display for Pretty<'_, Error> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self.inner {
            Error::Wrapped(e, _) => write!(f, "{}", pretty(&**e, &self.s)),
            Error::DifferentTerm(t1, t2) => write!(
                f,
                "Expected `{}`, got `{}`",
                pretty(&**t1, &self.s),
                pretty(&**t2, &self.s)
            ),
            e => panic!("Not implemented {}", e),
        }
    }
}
