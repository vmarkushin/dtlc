use super::Result;
use crate::check::meta::HasMeta;
use crate::check::state::TypeCheckState;
use crate::check::Error;
use crate::syntax::abs::{
    ConsInfo as AConsInfo, DataInfo as ADataInfo, Decl as ADecl, Expr, Tele as ATele,
};
use crate::syntax::core::{
    Closure, ConsInfo, DataInfo, DeBruijn, Decl, FuncInfo, Tele, Term, Val, ValData,
};
use crate::syntax::desugar::DesugarState;
use crate::syntax::{Universe, GI};
use itertools::Either::*;

impl TypeCheckState {
    pub fn check_prog(&mut self, desugar_state: DesugarState) -> Result<()> {
        self.check_decls(desugar_state.decls.into_iter(), desugar_state.cur_meta_id)?;
        Ok(())
    }

    pub fn check_decls(
        &mut self,
        decls: impl Iterator<Item = ADecl>,
        meta_ids: Vec<GI>,
    ) -> Result<()> {
        let curr_decl_len = self.sigma.len();
        let mut decls = decls.map(Some).collect::<Vec<_>>();
        let take = |decls: &mut [Option<ADecl>], i: usize| decls[i].take().unwrap();

        for i in 0..decls.len() {
            self.enter_def(i + curr_decl_len, meta_ids[i + curr_decl_len]);
            if decls[i].is_none() {
                continue;
            }
            let decl = take(&mut decls, i);
            self.tc_reset_depth();
            match decl {
                ADecl::Data(info) => {
                    let cs = (info.conses.iter())
                        .map(|j| match take(&mut decls, *j - curr_decl_len) {
                            ADecl::Cons(i) => i,
                            _ => unreachable!(),
                        })
                        .collect();
                    // TODO: Inline meta??
                    self.check_data(info, cs)?;
                }
                ADecl::Cons(_) => {
                    // Cons is checked in the Data case above.
                }
                ADecl::Fn(f) => {
                    let signature = self.check(
                        f.ty.as_ref().expect("please specify type"),
                        &Val::Universe(Universe(u32::MAX)), // TODO: this is Setω in Agda. Consider other ways for checking type here.
                    )?;

                    let signature = signature.ast;
                    let body = self.lam(f.expr, signature.clone())?;
                    let body = body.inline_meta(self)?;
                    let term = signature.inline_meta(self)?;
                    let signature = self.simplify(term)?.into();
                    let func = FuncInfo {
                        loc: f.id.loc,
                        name: f.id,
                        signature,
                        body,
                    };
                    self.sigma.push(Decl::Func(func));
                }
            }
            self.exit_def();
            self.sanity_check();
        }
        Ok(())
    }

    /// The checked tele is put into the returned `tcs.gamma`.
    pub fn check_tele(&mut self, tele: ATele, ty: &Val) -> Result<()> {
        for bind in tele {
            let checked = self.check(bind.ty.as_ref().unwrap(), ty)?;
            let bind = bind.map_term(|_| checked.ast);
            self.gamma.push(bind);
        }
        Ok(())
    }

    fn check_cons(&mut self, cons: AConsInfo, data: &DataInfo, ty: &Val) -> Result<ConsInfo> {
        let param_len = self.gamma.len();
        self.check_tele(cons.tele, ty)?;
        let params = self.gamma.split_off(param_len);
        let mut tele = data.params.clone();
        tele.append(&mut params.clone());
        let args = (0..data.params.len())
            .rev()
            .map(|x| Term::from_dbi(x + params.len()))
            .collect();
        let ret = Term::data(ValData::new(cons.data_ix, args));
        let signature = Term::pi_from_tele(tele, ret);
        let info = ConsInfo {
            loc: cons.loc,
            name: cons.name,
            params,
            data: cons.data_ix,
            signature,
        };
        Ok(info)
    }

    pub fn check_data(&mut self, data: ADataInfo, conses: Vec<AConsInfo>) -> Result<()> {
        let universe1 = data
            .uni
            .ok_or_else(|| Error::ExpectedUniverseForData(data.ident().clone()))?;
        let t = Val::Universe(universe1);
        self.check_tele(data.tele, &t)?;
        let param_len = self.gamma.len();
        let signature = Term::pi_from_tele(self.gamma.clone(), Term::universe(universe1));
        let info = DataInfo {
            params: self.gamma.clone(),
            loc: data.loc,
            name: data.name,
            universe: data.uni.unwrap(),
            conses: data.conses,
            signature,
        };
        self.sigma.push(Decl::Data(info.clone()));

        // For debugging only.
        let mut data_ix = None;

        for cons in conses {
            let cons = self.check_cons(cons, &info, &t)?;
            match data_ix {
                None => data_ix = Some(cons.data),
                Some(ix) => debug_assert_eq!(ix, cons.data),
            }
            debug_assert_eq!(param_len, self.gamma.len());

            self.sigma.push(Decl::Cons(cons));
        }
        self.gamma.clear();
        Ok(())
    }

    #[allow(unused)]
    fn tele(&mut self, abs: ATele, mut val: Val) -> Result<(Tele, Val)> {
        use itertools::Itertools;

        let mut tele = Vec::new();
        if self.trace_tc {
            debug!(
                "{}Checking telescope {} against {}",
                self.indentation,
                abs.iter()
                    .cloned()
                    .map(|x| { x.map_term(|y| y.unwrap()) })
                    .join(" -> "),
                val
            );
        }

        let len = abs.len();
        for bind in abs {
            let target_ty = match val.into_pi() {
                Right((target_bind, Closure::Plain(cl))) => {
                    val = self.simplify(*cl.clone())?;
                    self.simplify(*target_bind.ty.clone())?
                }
                Left(v) => {
                    panic!("Expected Π, but got: {}", v);
                }
            };
            let (inferred, _) = self.infer(bind.ty.as_ref().unwrap())?;
            let inferred_simp = self.simplify(inferred.ast.clone())?;
            self.subtype(&inferred_simp, &target_ty)?;
            let bind = bind.map_term(|_| inferred.ast);
            self.gamma.push(bind.clone());
            tele.push(bind);
        }
        self.gamma.truncate(self.gamma.len() - len);

        Ok((tele, val))
    }

    fn lam(&mut self, body: Expr, against: Term) -> Result<Term> {
        let against_val = self.simplify(against)?;
        let body_ch = self.check(&body, &against_val)?.ast;
        Ok(body_ch)
    }

    /// Bind as patterns
    #[allow(unused)]
    fn bind_as_and_tele<T>(
        &mut self,
        mut tele: Tele,
        f: impl FnOnce(&mut TypeCheckState) -> Result<T>,
    ) -> Result<T> {
        use std::mem::swap;

        swap(&mut self.gamma, &mut tele);
        let thing = f(self)?;
        swap(&mut self.gamma, &mut tele);
        Ok(thing)
    }
}
