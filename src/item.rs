use crate::{
    ensure,
    env::Env,
    expr::{Expr, Kinds, Sym, TCError, Type},
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
        ty_args: Vec<(Option<Sym>, Type)>,
        cons: Vec<(Sym, Option<Type>)>,
    },
}

impl Item {
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
                ty_args,
                cons,
            } => {
                match data_ty {
                    Some(ty) => {
                        let _ = ty.ensure_well_formed_type(r.clone())?;
                    }
                    None => {
                        let _ = data_ty.insert(Kinds::Star.into());
                    }
                }
                for (_, ty) in cons {
                    if let Some(ty) = ty {
                        // forall (A1 : T1) (A2 : T2) ... (An : Tn) -> Data A1 A2 ... An
                        // data List (T : *)
                        //     | nil
                        //     | cons : T -> List T
                        // will become
                        // List : * -> * ???
                        // nil : forall T: *, List T
                        // cons : forall T: *, T -> List T

                        // let cons_ty = pi_many(name, ty_args) ++ ty;
                        // ty.ensure_ret_type_eq(name, ty_args, &r)?;
                        todo!()
                    }
                }
                Ok(())
            }
        }
    }
}
