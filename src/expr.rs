use crate::typeck::{BType, Type};
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};

pub type Sym = String;
pub type BExpr = Box<Expr>;

#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum Expr {
    Var(Sym),
    Lam(Sym, BType, BExpr),
    App(BExpr, BExpr),
    TLam(Sym, BExpr),
    TApp(BExpr, BType),
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
            Expr::TLam(s, b) => {
                write!(f, "(Λ{s}. {b})")
            }
            Expr::TApp(ff, a) => {
                f.write_str(&format!("{} ", ff))?;
                match a.as_ref() {
                    app @ Type::Arrow(_, _) => f.write_str(&format!("({})", app)),
                    e => f.write_str(&format!("{}", e)),
                }
            }
        }
    }
}

pub fn app(f: impl Into<BExpr>, a: impl Into<BExpr>) -> Expr {
    Expr::App(f.into(), a.into())
}

pub fn lam(s: impl Into<String>, t: impl Into<BType>, e: impl Into<BExpr>) -> Expr {
    Expr::Lam(s.into(), t.into(), e.into())
}

pub fn var(s: impl Into<String>) -> Expr {
    Expr::Var(s.into())
}

pub fn tapp(f: impl Into<BExpr>, a: impl Into<BType>) -> Expr {
    Expr::TApp(f.into(), a.into())
}

pub fn tlam(s: impl Into<String>, e: impl Into<BExpr>) -> Expr {
    Expr::TLam(s.into(), e.into())
}

impl<T: Into<String>> From<T> for BExpr {
    fn from(s: T) -> Self {
        box Expr::Var(s.into())
    }
}

/// Generates a fresh variable name based on the given one considering variables in the context.
pub fn gen_fresh_name(i: &Sym, vars: HashSet<Sym>) -> String {
    let mut i_new = i.clone();
    while vars.contains(&i_new) {
        i_new.push('\'');
    }
    i_new
}
