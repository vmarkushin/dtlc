use crate::check::block::Blocked;
use crate::syntax::abs::{Expr, Pat as PatA};
use crate::syntax::core::{Elim, Pat, Term, Val};
use crate::syntax::{Ident, Loc, Universe, MI};

pub use crate::check::norm::try_match;
pub use case::{CaseTree, Clause, Constraint, LshProblem};
pub use state::TypeCheckState;
pub use unify::Unify;

mod block;
mod case;
mod decls;
mod infer;
mod meta;
mod norm;
mod state;
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
    InvalidPi(Box<Val>, Box<Val>),
    #[error("Blocked: {0}")]
    Blocked(Box<Blocked<Term>>),
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
}

pub type Result<T, E = Error> = std::result::Result<T, E>;

impl Error {
    pub fn wrap(self, info: Loc) -> Self {
        Error::Wrapped(Box::new(self), info)
    }
}
