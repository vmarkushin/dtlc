use crate::ensure;
use crate::expr::{Env, Expr, Sym, TCError, Type};

#[derive(Debug)]
pub enum Item {
    Fn {
        name: Sym,
        ty: Option<Type>,
        body: Expr,
    },
    Data {
        name: Sym,
        cons: Vec<(Sym, Type)>,
    },
}

impl Item {
    // pub fn infer_or_check_type(&mut self) -> Result<&mut Type, TCError> {
    //     let r = Default::default();
    //     self.infer_or_check_type_in(r)
    // }

    pub fn infer_or_check_type_in(&mut self, r: Env) -> Result<(), TCError> {
        match self {
            Item::Fn { ty, body, .. } => {
                let inferred_ty = body.typeck(r)?;
                match ty {
                    Some(ty) => {
                        ensure!(
                            *ty == inferred_ty,
                            format!("Expected type {}, got {}", ty, inferred_ty)
                        );
                        Ok(())
                    }
                    None => {
                        ty.insert(inferred_ty);
                        Ok(())
                    }
                }
            }
            Item::Data { name, cons } => {
                for (_, ty) in cons {
                    ty.ensure_ret_type_eq(name)?;
                }
                Ok(())
            }
        }
    }
}