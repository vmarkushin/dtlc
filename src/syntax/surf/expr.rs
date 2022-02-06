use crate::syntax::surf::Param;
use crate::syntax::{Ident, Loc, Plicitness, Universe};
use itertools::Itertools;
use std::fmt::{Debug, Display, Formatter};
use vec1::Vec1;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    Var(Ident),
    Lam(Vec1<Param>, Box<Self>),
    /// `f a b` represented as `App(f, [a, b])`
    App(Box<Self>, Vec1<Self>),
    Universe(Loc, Universe),
    /// `A -> B -> C` represented as `Pi([A, B], C)`.
    Pi(Vec1<Param>, Box<Self>),
    Hole(Loc),
}

impl Expr {
    pub fn app_many(f: impl Into<Expr>, args: impl IntoIterator<Item = impl Into<Expr>>) -> Expr {
        Expr::App(
            Box::new(f.into()),
            Vec1::try_from_vec(args.into_iter().map(Into::into).collect()).unwrap(),
        )
    }

    pub fn lam_many(
        term: Expr,
        params: impl Sized + DoubleEndedIterator<Item = (Ident, Type)>,
    ) -> Expr {
        Expr::Lam(
            Vec1::try_from_vec(
                params
                    .map(|(ident, ty)| Param::new(ident, ty, Plicitness::Explicit))
                    .collect(),
            )
            .unwrap(),
            Box::new(term),
        )
    }

    pub fn pi_many(
        params: impl Sized + DoubleEndedIterator<Item = (Ident, Type)>,
        term: Expr,
    ) -> Expr {
        Expr::Pi(
            Vec1::try_from_vec(
                params
                    .map(|(ident, ty)| Param::new(ident, ty, Plicitness::Explicit))
                    .collect(),
            )
            .unwrap(),
            Box::new(term),
        )
    }

    pub fn arrow(param_ty: impl Into<Type>, ty: impl Into<Type>) -> Self {
        Expr::Pi(
            Vec1::new(Param::from_type(param_ty.into(), Plicitness::Explicit)),
            Box::new(ty.into()),
        )
    }

    pub fn var(name: impl Into<String>, loc: impl Into<Loc>) -> Self {
        Self::Var(Ident::new(name, loc.into()))
    }
}

pub type Type = Expr;

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(i) => write!(f, "{}", i),
            Self::App(func, args) => {
                write!(f, "{}", func)?;
                for arg in args {
                    match arg {
                        app @ Self::App(..) => write!(f, "({})", app)?,
                        e => write!(f, "{}", e)?,
                    }
                }
                Ok(())
            }
            Self::Lam(params, body) => {
                write!(f, "(λ {} => {})", params.into_iter().join(" "), body)
            }
            Self::Pi(params, ty) => write!(f, "(Π {}, {})", params.into_iter().join(" "), ty),
            Self::Universe(_, k) => write!(f, "{}", k),
            Self::Hole(_) => write!(f, "_"),
        }
    }
}
