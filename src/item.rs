use crate::{
    ensure,
    env::Env,
    expr::{Expr, Sym, TCError, Type},
};
use std::fmt::{Debug, Display, Formatter};

#[derive(Debug)]
pub enum Item {
    Fn {
        name: Sym,
        ty: Option<Type>,
        body: Expr,
    },
    Data {
        name: Sym,
        ty_params: Vec<(Option<Sym>, Type)>,
        ty: Option<Type>,
        cons: Vec<(Sym, Option<Type>)>,
    },
}

impl Item {
    #[must_use]
    pub fn infer_or_check_type_in(&mut self, r: Env) -> Result<(), TCError> {
        match self {
            Item::Fn { ty, body, .. } => {
                let got_ty = body.typeck(r)?;
                match ty {
                    Some(ty) => {
                        ensure!(
                            *ty == got_ty,
                            TCError::WrongType {
                                expected: ty.clone(),
                                got: got_ty
                            },
                        );
                        Ok(())
                    }
                    None => {
                        *ty = Some(got_ty);
                        Ok(())
                    }
                }
            }
            Item::Data {
                name,
                ty: data_ty,
                ty_params,
                cons,
            } => {
                match data_ty {
                    Some(ty) => {
                        let _ = ty.ensure_well_formed_type(r.clone())?;
                    }
                    None => {
                        let _ = data_ty.insert(Expr::Universe(0));
                    }
                }
                for (_, ty) in cons {
                    if let Some(ty) = ty {
                        // forall (A1 : T1) (A2 : T2) ... (An : Tn) -> Data A1 A2 ... An
                        // data List (T : *)
                        //     | nil
                        //     | cons : T -> List T
                        // will become
                        // List : * -> *
                        // nil : forall T: *, List T
                        // cons : forall T: *, T -> List T

                        // let cons_ty = pi_many(name, ty_params) ++ ty;
                        // ty.ensure_ret_type_eq(name, ty_params, &r)?;
                        todo!()
                    }
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
                for (name, ty) in ty_params {
                    if let Some(name) = name {
                        write!(f, "({} : {})", name, ty)?;
                    } else {
                        write!(f, "{}", ty)?;
                    }
                }
                if let Some(t) = ty {
                    write!(f, " : {}", t)?;
                }
                f.write_str("\n")?;
                for (name, ty) in cons {
                    write!(f, "\t | {}", name)?;
                    if let Some(ty) = ty {
                        write!(f, " : {}", ty)?;
                    }
                    f.write_str("\n")?;
                }
                Ok(())
            }
        }
    }
}
