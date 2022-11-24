use crate::check::Error as CheckError;
use crate::parser::ParseError;
use crate::syntax::core::{pretty, Pretty};
use crate::syntax::desugar::DesugarError;
use std::fmt;
use std::fmt::{Display, Formatter};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("Parse error: {0}")]
    Parse(#[from] ParseError<'static>),
    #[error("Desugar error: {0}")]
    Desugar(#[from] DesugarError),
    #[error("Check error: {0}")]
    TypeCheck(#[from] CheckError),
}

impl Display for Pretty<'_, Error> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match &self.inner {
            Error::TypeCheck(e) => write!(f, "{}", pretty(e, &self.s)),
            Error::Parse(e) => write!(f, "{}", e),
            Error::Desugar(e) => write!(f, "{}", e),
        }
    }
}
