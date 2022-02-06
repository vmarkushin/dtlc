use crate::typeck::BType;
use crate::typeck::Type::Base;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};

pub type Sym = String;
pub type BExpr = Box<Expr>;

#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum Expr {
    Var(Sym),
    App(BExpr, BExpr),
    Lam(Sym, BType, BExpr),
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Var(i) => f.write_str(i),
            Expr::App(ff, a) => {
                f.write_str(&format!("{} ", ff))?;
                match a.as_ref() {
                    app @ Expr::App(_, _) => f.write_str(&format!("({})", app)),
                    e => f.write_str(&format!("{}", e)),
                }
            }
            Expr::Lam(i, t, b) => f.write_str(&format!("(λ{}:{}. {})", i, t, b)),
        }
    }
}

pub fn app(f: impl Into<BExpr>, a: impl Into<BExpr>) -> BExpr {
    box Expr::App(f.into(), a.into())
}

pub fn lam(s: impl Into<String>, t: impl Into<BType>, e: impl Into<BExpr>) -> BExpr {
    box Expr::Lam(s.into(), t.into(), e.into())
}

pub fn var(s: impl Into<String>) -> BExpr {
    box Expr::Var(s.into())
}

impl<T: Into<String>> From<T> for BExpr {
    fn from(s: T) -> Self {
        box Expr::Var(s.into())
    }
}
