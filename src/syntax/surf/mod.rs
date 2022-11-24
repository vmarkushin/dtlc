mod decl;
mod expr;
mod lit;
mod meta_attr;

use crate::syntax::{surf::Type, Ident, Plicitness};
pub use decl::*;
pub use expr::*;
pub use lit::*;
pub use meta_attr::*;
use std::fmt::{Display, Formatter};

pub type Prog = Vec<Decl>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Param {
    pub name: Option<Ident>,
    pub ty: Option<Type>,
    pub plic: Plicitness,
}

impl Param {
    pub fn new(name: Ident, ty: Type, plic: Plicitness) -> Self {
        Param {
            name: Some(name),
            ty: Some(ty),
            plic,
        }
    }

    pub fn from_ident(name: Ident, plic: Plicitness) -> Self {
        Param {
            name: Some(name),
            ty: None,
            plic,
        }
    }

    pub fn from_type(ty: Type, plic: Plicitness) -> Self {
        Param {
            name: None,
            ty: Some(ty),
            plic,
        }
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = &self.name {
            if let Some(t) = &self.ty {
                write!(f, "({} : {})", name, t)
            } else {
                write!(f, "{}", name)
            }
        } else if let Some(t) = &self.ty {
            write!(f, "{}", t)
        } else {
            Ok(())
        }
    }
}
