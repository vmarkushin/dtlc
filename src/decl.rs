use crate::parser::Parser;
use crate::term::{App, Lam, Param, Pi, Var};
use crate::{
    env::Env,
    term::{TCError, Term, Type},
};
use std::{
    borrow::Cow,
    fmt::{Debug, Display, Formatter},
};

use derive_more::From;

#[derive(Debug)]
pub struct Constructor {
    pub name: Var,
    pub params: Params,
}

impl Constructor {
    pub fn new(name: Var, params: impl Into<Params>) -> Self {
        Constructor {
            name,
            params: params.into(),
        }
    }
}

#[derive(Clone, Debug, From)]
pub struct Params(pub Vec<Param>);

impl Params {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Converts type params (e.g. `(A B C : T)`) to `Pi` (i.e. `forall (A B: T), T`).
    pub fn to_pi(mut self) -> Option<Type> {
        let last = self.0.pop()?.ty;
        Some(self.to_pi_with(last))
        // Some(params.into_iter().rev().fold(last, |acc, p| match p.name {
        //     Some(name) => Pi::new(name, box acc, box p.ty).into(),
        //     None => Pi::arrow(acc, p.ty).into(),
        // }))
    }

    /// Example: converting params `(A B C : T)` with `Term` to lambda will give `lam (A B C : T) => Term`
    pub fn to_lam(self, body: Term) -> Term {
        let params = self.0;
        params.into_iter().rev().fold(body, |acc, p| {
            let name = p.name.unwrap_or_else(|| "_".into());
            Lam::new(name, p.ty, acc).into()
        })
    }

    /// Example: applying params `(A B C : T)` to `Term` will give `Term A B C`
    pub fn app(self, f: Term) -> Type {
        let params = self.0;
        let mut n = 0;
        params.into_iter().fold(f, |acc, p| {
            let name = match p.name {
                Some(name) => name,
                None => {
                    n += 1;
                    format!("__x{}", n).into()
                }
            };
            App::new(acc, name.parse::<Term>().unwrap()).into()
        })
    }

    /// Example: merging `(A B : T)` and `C` will give `forall (A B : T), C`
    pub fn merge_pis(params: Vec<Param>, pi2: Term) -> Term {
        let mut n = 0;
        params.into_iter().rev().fold(pi2, |acc, p| {
            let name = match p.name {
                Some(name) => name,
                None => {
                    n += 1;
                    format!("__x{}", n).into()
                }
            };
            Pi::new(name, box p.ty, box acc).into()
        })
    }

    /// Example: merging `(A B : T)` and `C` will give `forall (A B : T), C`
    pub fn to_pi_with(self, term: Term) -> Term {
        let params = self.0;
        if params.is_empty() {
            return term;
        }
        let mut n = 0;
        params.into_iter().rev().fold(term, |acc, p| {
            let name = match p.name {
                Some(name) => name.to_string(),
                None => {
                    n += 1;
                    format!("__x{}", n)
                }
            };
            Pi::new(name, p.ty, acc).into()
        })
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

#[derive(Debug)]
pub struct FnDecl {
    pub name: Var,
    pub params: Params,
    pub ret_ty: Option<Type>,
    pub body: Term,
}

#[derive(Debug, From)]
pub enum Decl {
    Fn(FnDecl),
    Data {
        name: Var,
        ty_params: Params,
        universe: Option<Type>,
        cons: Vec<Constructor>,
    },
}

impl Decl {
    pub fn infer_or_check_type_in(&mut self, r: &mut Cow<Env>) -> Result<(), TCError> {
        match self {
            Decl::Fn(FnDecl {
                ret_ty: return_ty,
                body,
                ..
            }) => match return_ty {
                Some(ty) => {
                    body.typeck(r, ty.clone())?;
                    Ok(())
                }
                None => {
                    *return_ty = Some(r.to_mut().infer_type(body.clone())?);
                    Ok(())
                }
            },
            Decl::Data {
                name,
                universe: ret_ty,
                ty_params,
                cons,
            } => {
                let ret_ty = match ret_ty {
                    Some(ty) => ty.ensure_well_formed_type(r)?,
                    None => ret_ty.insert(Term::Universe(Default::default())).clone(),
                };

                let params_pi = ty_params.clone().to_pi();
                let data_ty = match params_pi {
                    Some(pi) => Pi::arrow(pi, ret_ty).into(),
                    None => ret_ty,
                };
                r.to_mut().add_type(name.clone(), data_ty);
                let data_ident = name.parse::<Term>().unwrap();

                // TODO: check for positivity
                for con in cons {
                    let data_app_ty = ty_params.clone().app(data_ident.clone());
                    let con_ty = con.params.clone().to_pi_with(data_app_ty);
                    let con_ty = ty_params.clone().to_pi_with(con_ty);
                    r.to_mut().infer_type(con_ty)?;
                }
                Ok(())
            }
        }
    }
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Decl::Fn(FnDecl {
                name,
                params,
                ret_ty: ty,
                body,
            }) => {
                write!(f, "fn {}", name)?;
                if !params.is_empty() {
                    write!(f, "{}", params)?;
                }
                if let Some(ty) = ty {
                    write!(f, " : {}", ty)?;
                }
                write!(f, " => {}", body)
            }
            Decl::Data {
                name,
                ty_params,
                universe,
                cons,
            } => {
                write!(f, "data {}", name)?;
                write!(f, "{}", ty_params)?;
                if let Some(t) = universe {
                    write!(f, " : {}", t)?;
                }
                f.write_str("\n")?;
                for con in cons {
                    write!(f, "\t | {}", con.name)?;
                    write!(f, "{}", con.params)?;
                    f.write_str("\n")?;
                }
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::Parser;

    use super::*;

    #[test]
    fn test_data() -> eyre::Result<()> {
        let mut env = Env::default();
        let parser = Parser::default();
        let out = env.run(parser.parse_prog(
            r#"
    data Nat
        | O
        | S Nat

    data List (T : Type)
        | nil
        | cons T (List T)

    fn main := cons Nat (S (S O)) (cons Nat (S O) (cons Nat O (nil Nat)))
    "#,
        )?);
        assert_eq!(
            out,
            parser.parse_term("cons Nat (S (S O)) (cons Nat (S O) (cons Nat O (nil Nat)))")?
        );
        assert_eq!(env.infer_type(out)?, parser.parse_term("List Nat")?);
        assert_eq!(
            *env.get_type(&Var("nil".to_owned())).unwrap(),
            parser.parse_term("forall (T : Type), List T")?
        );
        let x = env.get_type(&Var("cons".to_owned())).unwrap();
        let term = parser.parse_term("forall (T : Type) (__x2 : T) (__x1 : List T), (List T)")?;
        assert_eq!(*x, term);
        Ok(())
    }
}
