use crate::term::{App, Param, Pi, Var};
use crate::{
    env::Env,
    term::{TCError, Term, Type},
};
use std::{
    borrow::Cow,
    fmt::{Debug, Display, Formatter},
};

#[derive(Debug)]
pub struct Constructor {
    pub name: Var,
    pub params: Vec<Param>,
}

impl Constructor {
    pub fn new(name: Var, params: Vec<Param>) -> Self {
        Constructor { name, params }
    }
}

#[derive(Debug)]
pub enum Decl {
    Fn {
        name: Var,
        return_ty: Option<Type>,
        body: Term,
    },
    Data {
        name: Var,
        ty_params: Vec<Param>,
        universe: Option<Type>,
        cons: Vec<Constructor>,
    },
}

/// Converts type params (e.g. `(A B C : T)`) to `Pi` (i.e. `forall (A B: T), T`).
pub fn params_to_pi(mut params: Vec<Param>) -> Option<Type> {
    let last = params.pop()?.ty;
    Some(params.into_iter().fold(last, |acc, p| match p.name {
        Some(name) => Pi::new(name, box acc, box p.ty).into(),
        None => Pi::arrow(acc, p.ty).into(),
    }))
}

/// Example `Term` and `(A B C : T)` will give `Term A B C`
pub fn params_to_app(f: Term, params: Vec<Param>) -> Type {
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

impl Decl {
    pub fn infer_or_check_type_in(&mut self, r: &mut Cow<Env>) -> Result<(), TCError> {
        match self {
            Decl::Fn {
                return_ty, body, ..
            } => {
                let got_ty = body.typeck(r)?;
                match return_ty {
                    Some(ty) if *ty == got_ty => Err(TCError::WrongType {
                        expected: ty.clone(),
                        got: got_ty,
                    }),
                    Some(_) => Ok(()),
                    None => {
                        *return_ty = Some(got_ty);
                        Ok(())
                    }
                }
            }
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

                let params_pi = params_to_pi(ty_params.clone());
                let data_ty = match params_pi {
                    Some(pi) => Pi::arrow(pi, ret_ty).into(),
                    None => ret_ty,
                };
                r.to_mut().add_type(name.clone(), data_ty);
                let data_ident = name.parse::<Term>().unwrap();

                // TODO: check for positivity
                for con in cons {
                    let data_app_ty = params_to_app(data_ident.clone(), ty_params.clone());
                    let con_ty = if !con.params.is_empty() {
                        merge_pis(con.params.clone(), data_app_ty)
                    } else {
                        data_app_ty
                    };
                    let con_ty = if !ty_params.is_empty() {
                        merge_pis(ty_params.clone(), con_ty)
                    } else {
                        con_ty
                    };
                    con_ty.typeck(r)?;
                }
                Ok(())
            }
        }
    }
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Decl::Fn {
                name,
                return_ty,
                body,
            } => {
                if let Some(ty) = return_ty {
                    write!(f, "let {} : {} => {}", name, ty, body)
                } else {
                    write!(f, "let {} => {}", name, body)
                }
            }
            Decl::Data {
                name,
                ty_params,
                universe,
                cons,
            } => {
                write!(f, "data {}", name)?;
                for param in ty_params {
                    write!(f, " {}", param)?;
                }
                if let Some(t) = universe {
                    write!(f, " : {}", t)?;
                }
                f.write_str("\n")?;
                for con in cons {
                    write!(f, "\t | {}", con.name)?;

                    for param in &con.params {
                        write!(f, " {}", param)?;
                    }
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

    let main := cons Nat (S (S O)) (cons Nat (S O) (cons Nat O (nil Nat)))
    "#,
        )?);
        assert_eq!(
            out,
            parser.parse_term("cons Nat (S (S O)) (cons Nat (S O) (cons Nat O (nil Nat)))")?
        );
        assert_eq!(
            out.typeck(&mut Cow::Borrowed(&env))?,
            parser.parse_term("List Nat")?
        );
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
