use std::fmt::{Debug, Display, Formatter};

use crate::syntax::core::{pretty_list, Boxed};
use crate::syntax::surf::{Expr, MetaAttr, Param, Type};
use crate::syntax::{Ident, Universe};
use derive_more::From;
use vec1::Vec1;

#[derive(Debug)]
pub struct Constructor {
    pub name: Ident,
    pub params: Params,
}

impl Constructor {
    pub fn new(name: Ident, params: impl Into<Params>) -> Self {
        Constructor {
            name,
            params: params.into(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, From)]
pub struct Params(pub Vec<Param>);

impl Params {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Converts type params (e.g. `(A B C : T)`) to `Pi` (i.e. `forall (A B: T), T`).
    pub fn to_pi(mut self) -> Option<Type> {
        let param = self.0.pop()?;
        let last = param
            .ty
            .unwrap_or_else(|| Type::Hole(param.name.expect("either should be known").loc));
        Some(self.to_pi_with(last))
    }

    /// Example: converting params `(A B C : T)` with `Expr` to lambda will give `lam (A B C : T) => Expr`
    pub fn to_lam(self, body: Expr) -> Expr {
        let params = self.0;
        if params.is_empty() {
            body
        } else {
            Expr::Lam(Vec1::try_from_vec(params).unwrap(), body.boxed())
        }
        // params.into_iter().rev().fold(body, |acc, p| {
        //     let name = p.name.unwrap_or_else(|| "_".into());
        //     Lam::new(name, p.ty, acc).into()
        // })
    }

    /*
    /// Example: applying params `(A B C : T)` to `Expr` will give `Expr A B C`
    pub fn app(self, f: Expr) -> Type {
        let params = self.0;
        if params.is_empty() {
            f
        } else {
            Expr::App(box f, Vec1::try_from_vec(params.into_iter).unwrap())
        }

        // let mut n = 0;
        // params.into_iter().fold(f, |acc, p| {
        //     let name = match p.name {
        //         Some(name) => name,
        //         None => {
        //             n += 1;
        //             Ident::new(Default::default(), format!("__x{}", n))
        //         }
        //     };
        //     App::new(acc, Expr::Var(name)).into()
        // })
    }
     */

    /// Example: merging `(A B : T)` and `C` will give `forall (A B : T), C`
    pub fn merge_pis(params: Vec<Param>, pi2: Expr) -> Expr {
        Params(params).to_pi_with(pi2)
        // let mut n = 0;
        // params.into_iter().rev().fold(pi2, |acc, p| {
        //     let name = match p.name {
        //         Some(name) => name,
        //         None => {
        //             n += 1;
        //             format!("__x{}", n).into()
        //         }
        //     };
        //     Pi::new(name, box p.ty, box acc).into()
        // })
    }

    /// Example: merging `(A B : T)` and `C` will give `forall (A B : T), C`
    pub fn to_pi_with(self, term: Expr) -> Expr {
        let params = self.0;
        if params.is_empty() {
            term
        } else {
            Expr::Pi(Vec1::try_from_vec(params).unwrap(), term.boxed())
        }

        // let mut n = 0;
        // params.into_iter().rev().fold(term, |acc, p| {
        //     let name = match p.name {
        //         Some(name) => name.to_string(),
        //         None => {
        //             n += 1;
        //             format!("__x{}", n)
        //         }
        //     };
        //     Expr::Pi()
        //     Pi::new(name, p.ty, acc).into()
        // })
    }
}

impl Display for Params {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for p in &self.0 {
            write!(f, " {}", p)?;
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NamedTele {
    pub name: Ident,
    pub tele: Params,
}

impl NamedTele {
    pub fn new(name: Ident, tele: Params) -> Self {
        NamedTele { name, tele }
    }
}

impl Display for NamedTele {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} : {}", self.name, self.tele)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Data {
    pub sig: NamedTele,
    pub cons: Vec<NamedTele>,
    pub universe: Option<Universe>,
    pub meta_attrs: Vec<MetaAttr>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Func {
    pub name: Ident,
    pub params: Params,
    pub ret_ty: Option<Expr>,
    pub body: Expr,
    pub meta_attrs: Vec<MetaAttr>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Lam {
    param: Vec1<Param>,
    body: Expr,
}

#[derive(Debug, PartialEq, Eq, Clone, From)]
pub enum Decl {
    Data(Data),
    Fn(Func),
}

impl Decl {
    pub fn name(&self) -> &Ident {
        match self {
            Decl::Data(d) => &d.sig.name,
            Decl::Fn(f) => &f.name,
        }
    }
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Decl::Fn(Func {
                name,
                params,
                ret_ty: ty,
                body,
                meta_attrs,
            }) => {
                pretty_list(f, meta_attrs, "\n")?;
                write!(f, "fn {}", name)?;
                if !params.is_empty() {
                    write!(f, "{}", params)?;
                }
                if let Some(ty) = ty {
                    write!(f, " : {}", ty)?;
                }
                write!(f, " => {}", body)
            }
            Decl::Data(Data {
                sig,
                universe,
                cons,
                meta_attrs,
            }) => {
                pretty_list(f, meta_attrs, "\n")?;
                write!(f, "data {}", sig)?;
                if let Some(t) = universe {
                    write!(f, " : {}", t)?;
                }
                f.write_str("\n")?;
                for con in cons {
                    write!(f, "\t | {}", con.name)?;
                    write!(f, "{}", con.tele)?;
                    f.write_str("\n")?;
                }
                Ok(())
            }
        }
    }
}
