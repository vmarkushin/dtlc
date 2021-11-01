use crate::expr::{app, arrow, pi, Param};
use crate::parser::Parser;
use crate::{
    env::Env,
    expr::{Expr, Sym, TCError, Type},
};
use std::{
    borrow::Cow,
    fmt::{Debug, Display, Formatter},
};

#[derive(Debug)]
pub struct Constructor {
    pub name: Sym,
    pub params: Vec<Param>,
}

impl Constructor {
    pub fn new(name: Sym, params: Vec<Param>) -> Self {
        Constructor { name, params }
    }
}

#[derive(Debug)]
pub enum Item {
    Fn {
        name: Sym,
        ty: Option<Type>,
        body: Expr,
    },
    Data {
        name: Sym,
        ty_params: Vec<Param>,
        ty: Option<Type>,
        cons: Vec<Constructor>,
    },
}

/// Converts type params (e.g. `(A B C : T)`) to `Pi` (i.e. `forall (A B: T), T`).
pub fn params_to_pi(mut params: Vec<Param>) -> Option<Type> {
    let last = params.pop()?.ty;
    Some(params.into_iter().fold(last, |acc, p| match p.name {
        Some(name) => pi(name, acc, p.ty),
        None => arrow(acc, p.ty),
    }))
}

pub fn params_to_app(f: Expr, params: Vec<Param>) -> Type {
    let mut n = 0;
    params.into_iter().fold(f, |acc, p| {
        let name = match p.name {
            Some(name) => name,
            None => {
                n += 1;
                format!("_x{}", n)
            }
        };
        app(acc, name.parse::<Expr>().unwrap())
    })
}

impl Item {
    pub fn infer_or_check_type_in(&mut self, mut r: &mut Cow<Env>) -> Result<(), TCError> {
        match self {
            Item::Fn { ty, body, .. } => {
                let got_ty = body.typeck(r)?;
                match ty {
                    Some(ty) if *ty == got_ty => Err(TCError::WrongType {
                        expected: ty.clone(),
                        got: got_ty,
                    }),
                    Some(_) => Ok(()),
                    None => {
                        *ty = Some(got_ty);
                        Ok(())
                    }
                }
            }
            Item::Data {
                name,
                ty: ret_ty,
                ty_params,
                cons,
            } => {
                let ret_ty = match ret_ty {
                    Some(ty) => ty.ensure_well_formed_type(r)?,
                    None => ret_ty.insert(Expr::Universe(0)).clone(),
                };

                for param in ty_params.iter() {
                    if let Some(name) = &param.name {
                        r.add_type(name.clone(), param.ty.clone());
                    }
                }

                let data_ty = match params_to_pi(ty_params.clone()) {
                    Some(pi) => arrow(pi, ret_ty.clone()),
                    None => ret_ty.clone(),
                };
                r.add_type(name.clone(), data_ty);
                let data_ident = name.parse::<Expr>().unwrap();

                // TODO: check for positivity
                for con in cons {
                    // dbg!(&con.name);
                    let data_app_ty = params_to_app(data_ident.clone(), ty_params.clone());
                    let con_ty = match params_to_pi(con.params.clone()) {
                        Some(pi) => arrow(pi, data_app_ty),
                        None => data_app_ty,
                    };
                    dbg!(&con_ty);
                    con_ty.typeck(r.clone())?;
                }
                Ok(())
            }
        }
    }
}

impl Display for Item {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Item::Fn { name, ty, body } => {
                if let Some(ty) = ty {
                    write!(f, "let {} : {} => {}", name, ty, body)
                } else {
                    write!(f, "let {} => {}", name, body)
                }
            }
            Item::Data {
                name,
                ty_params,
                ty,
                cons,
            } => {
                write!(f, "data {}", name)?;
                for param in ty_params {
                    write!(f, " {}", param)?;
                }
                if let Some(t) = ty {
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

#[test]
fn test_data() {
    let mut env = Env::default();
    let parser = Parser::default();
    let out = env.run(
        parser
            .parse_prog(
                r#"
    data List (T : Type)
        | nil
        | cons T

    let main :=
    "#,
            )
            .unwrap(),
    );
}
