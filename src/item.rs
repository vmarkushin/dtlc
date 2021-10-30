use crate::{
    ensure,
    expr::{Env, Expr, Kinds, Sym, TCError, Type},
};

#[derive(Debug)]
pub enum Item {
    Fn {
        name: Sym,
        ty: Option<Type>,
        body: Expr,
    },
    Data {
        name: Sym,
        ty: Option<Type>,
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
                cons,
            } => {
                match data_ty {
                    Some(ty) => ty.ensure_well_formed_type(r),
                    None => {
                        data_ty.insert(Kinds::Star.into());
                        Ok(())
                    }
                }
                for (_, ty) in cons {
                    ty.ensure_ret_type_eq(name)?;
                }
                Ok(())
            }
        }
    }
}
