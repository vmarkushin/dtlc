use crate::check::block::{Blocked, NotBlocked};
use crate::check::state::TypeCheckState;
use crate::check::unification::{Equation, Param, Problem};
use crate::check::{Error, Result};
use crate::syntax::core::{
    build_subst, Boxed, Case, Closure, Decl, Elim, Func, Lambda, Simpl, SubstWith, Substitution,
    Term,
};
use crate::syntax::{ConHead, Ident, Loc, GI};
use std::collections::HashMap;
use std::rc::Rc;

fn elims_to_terms(elims: Vec<Elim>) -> Result<Vec<Term>> {
    elims
        .into_iter()
        .map(Elim::try_into_app)
        .collect::<Result<_, String>>()
        .map_err(Error::NotTerm)
}

/// Returns `Some(i, n)` for ith-matched case with n new variables bound, and None
/// for a stuck match.
pub fn try_match(x: &Term, cs: &[Case]) -> Option<(usize, Rc<Substitution>)> {
    let term = x.clone();
    cs.iter()
        .enumerate()
        .filter_map(|(i, c)| c.pattern.match_term(&term).map(|j| (i, j)))
        .next()
}

impl TypeCheckState {
    pub fn simplify_blocked(&mut self, term: Blocked<Term>, shallow: bool) -> Result<Term> {
        match term {
            Blocked::Yes(_, t) => Ok(t),
            Blocked::No(_, t) => self.reduce(t, shallow),
        }
    }

    pub fn normalize_problem(&mut self, prob: Problem) -> Result<Problem> {
        match prob {
            Problem::Unify(Equation { tm1, ty1, tm2, ty2 }) => {
                let tm1 = self.normalize(tm1)?;
                let ty1 = self.normalize(ty1)?;
                let tm2 = self.normalize(tm2)?;
                let ty2 = self.normalize(ty2)?;
                Ok(Problem::Unify(Equation { tm1, ty1, tm2, ty2 }))
            }
            Problem::All(mut param, prob) => {
                let ty = match param.ty {
                    Param::P(term) => Param::P(self.normalize(term)?),
                    Param::Twins(t1, t2) => Param::Twins(self.normalize(t1)?, self.normalize(t2)?),
                };
                param.ty = ty;
                let prob = self.normalize_problem(*prob)?;
                Ok(Problem::All(param, prob.boxed()))
            }
        }
    }

    /// Normalize a term to NF.
    pub fn normalize(&mut self, term: Term) -> Result<Term> {
        let term_out = self.simplify_impl(term.clone(), false)?;
        debug!(
            "{}[normalize]\n\t{}\n\t{}",
            self.tc_depth_ws(),
            term,
            term_out
        );
        Ok(term_out)
    }

    /// Normalize a term to WHNF.
    pub fn simplify(&mut self, term: Term) -> Result<Term> {
        let term_out = self.simplify_impl(term.clone(), true)?;
        debug!(
            "{}[simplify]\n\t{}\n\t{}",
            self.tc_depth_ws(),
            term,
            term_out
        );
        Ok(term_out)
    }

    /// Normalize a term.
    pub fn reduce(&mut self, term: Term, shallow: bool) -> Result<Term> {
        let term_out = self.simplify_impl(term.clone(), shallow)?;
        debug!(
            "{}[reduce {shallow}]\n\t{}\n\t{}",
            self.tc_depth_ws(),
            term,
            term_out
        );
        Ok(term_out)
    }

    fn normalize_neutral(&mut self, term: Term) -> Result<Term> {
        match term {
            Term::Data(mut data) => data
                .clone()
                .args
                .into_iter()
                .map(|t| self.normalize(t))
                .collect::<Result<Vec<_>>>()
                .map(|args| {
                    data.args = args;
                    Term::Data(data)
                }),
            Term::Cons(head, args) => {
                let args = args
                    .into_iter()
                    .map(|t| self.normalize(t))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Term::Cons(head, args))
            }
            Term::Pi(mut a, b) => {
                a.ty = self.normalize(*a.ty)?.boxed();
                let bb = self.normalize(b.into_inner())?;
                Ok(Term::Pi(a, Closure::Plain(bb.boxed())))
            }
            Term::Lam(mut lam) => {
                let mut body = lam.1;
                body = Closure::Plain(self.normalize(body.into_inner())?.boxed());
                lam.0.ty = self.normalize(*lam.0.ty)?.boxed();
                Ok(Term::Lam(Lambda(lam.0, body)))
            }
            Term::Var(head, elims) => {
                let elims = elims
                    .into_iter()
                    .map(|e| match e {
                        Elim::App(t) => Ok(Elim::App(self.normalize(*t)?.boxed())),
                        e => Ok(e),
                    })
                    .collect::<Result<_>>()?;
                Ok(Term::Var(head, elims))
            }
            Term::Id(_) => {
                todo!("Id norm")
            }
            Term::Refl(_) => {
                todo!("Refl norm")
            }
            t => Ok(t),
        }
    }

    pub fn simplify_impl(&mut self, term: Term, shallow: bool) -> Result<Term> {
        debug!("simplifying term: {}", &term);
        if matches!(term, Term::Match(..)) {
            trace!("simplifying match: {}", &term);
        }
        match term {
            Term::Id(mut id) => {
                id.a1 = self.reduce(*id.a1, shallow)?.boxed();
                id.a2 = self.reduce(*id.a2, shallow)?.boxed();
                Ok(Term::Id(id).into())
            }
            t if t.is_whnf() => {
                if shallow {
                    Ok(t)
                } else {
                    trace!(target: "reduce", "normalizing neutral term: {}", t);
                    self.normalize_neutral(t)
                }
            },
            Term::Redex(f, id, elims) => match f {
                Func::Index(def) => match self.def(def) {
                    // TODO: make a separate function for each data and constructor
                    Decl::Data(_) => Ok(Term::inductive(def, elims_to_terms(elims)?).into()),
                    Decl::Cons(cons) => {
                        let head = ConHead::new(id, cons.data_gi);
                        Ok(Term::Cons(head, elims_to_terms(elims)?).into())
                    }
                    Decl::Proj { .. } => unimplemented!(),
                    Decl::Func(func) => {
                        let (simp, term) = self.unfold_func(
                            def,
                            id.clone(),
                            func.body.as_ref().unwrap().clone(),
                            elims.clone(),
                        )?;
                        info!("unfolded {simp:?}, {term}");
                        // Ok((simp, term)) =>{
                            match simp {
                                Simpl::Yes => {
                                    self.simplify_blocked(term, shallow).map(|t| {
                                        info!("simplified term: {}", &t);
                                        t
                                    })
                                }
                                Simpl::No => {
                                    Ok(Term::Redex(
                                        f,
                                        id,
                                        elims
                                            .into_iter()
                                            .map(|e| match e {
                                                Elim::App(t) => {
                                                    Ok(Elim::App(self.reduce(*t, shallow)?.boxed()))
                                                }
                                                e => Ok(e),
                                            })
                                            .collect::<Result<_>>()?,
                                    ))
                                }
                            }
                            // self.reduce(term)
                        // }
                        // {
                            /*
                            Ok((simp, term)) => match simp {
                                Simpl::Yes => self.simplify_blocking(term),
                                Simpl::No => Ok(Term::Redex(
                                    f,
                                    id,
                                    elims
                                        .into_iter()
                                        .map(|e| match e {
                                            Elim::App(t) => {
                                                Ok(Elim::App(self.simplify_blocking(*t)?.boxed()))
                                            }
                                            e => Ok(e),
                                        })
                                        .collect::<Result<_>>()?,
                                )),
                            },
                             */

                            // Err(blockage) => match blockage.stuck {
                            //     NotBlocked::NotBlocked => self.reduce(blockage.anyway),
                            //     NotBlocked::OnElim(e) => {
                            //         trace!("stuck on elim: {}", e);
                            //         // TODO: simplify elims?
                            //         Ok(Term::Redex(f, id, elims))
                            //     }
                            //     _ => Err(Error::Blocked(box blockage)),
                            // },
                        // }
                    }
                },
                Func::Lam(lam) => {
                    let mut term = lam.1;
                    debug!("[Func::Lam] term  = {}", term);
                    let mut elims = elims;
                    if let Some(elim) = elims.get(0).cloned() {
                        elims.remove(0);
                        term = Closure::Plain(
                            term
                                .instantiate_safe_with(elim.into_app(), self)
                                .unwrap()
                                .boxed(),
                        );
                        debug!("[Func::Lam] term' = {}", term);
                    }
                    // for elim in elims {
                    //     term = Closure::Plain(
                    //         term
                    //             .instantiate_safe_with(elim.into_app(), self)
                    //             .unwrap().boxed()
                    //             // .tele_view_n(0)
                    //             // .1.boxed(),
                    //     );
                    //     debug!("[Func::Lam] term' = {}", term);
                    // }
                    let Closure::Plain(term) = term;
                    let term2 = *term;
                    let term = if elims.is_empty() {
                        term2
                    } else {
                        term2.apply_elim(elims)
                    };
                    self.reduce(term, shallow)
                }
            },
            Term::Match(x, ty, mut cs) => {
                debug!("Simplifying match");
                let simplified = self.reduce(*x.clone(), shallow)?;
                // substitute free variables in cases
                if let Some(uid) = simplified.free_var_view() {
                    cs = Term::subst_non_var_in_cases_instead_of_free_var(
                        self,
                        cs,
                        &uid,
                    )
                }
                match try_match(&simplified, &cs) {
                    Some((i, sigma)) => {
                        debug!("matched {}th case with σ = {}", i, sigma);
                        let matched_case = cs.remove(i);
                        trace!("matched_case.body = {}", matched_case.body);
                        let term1 = matched_case.body.subst_with(sigma, self);
                        trace!("matched_case.bodyσ = {}", term1);
                        self.reduce(term1, shallow)
                    }
                    None => {
                    // TODO: simplify cases?
                        Ok(Term::Match(simplified.boxed(), self.reduce(*ty, shallow)?.boxed(), cs))
                    },
                    /*
                    None => Err(Error::Blocked(box Blocked::new(
                        NotBlocked::OnElim(Elim::App(x.clone())),
                        Term::Match(x, cs),
                    ))),
                     */
                }
            }
            Term::Ap(tele, ps, t) => {
                if tele.is_empty() {
                    debug_assert!(ps.is_empty());
                    Ok(Term::Refl(self.reduce(*t, shallow)?.boxed()).into())
                    // Ok(Term::ap([], [], self.reduce(*t)?))
                } else {
                    let ps = ps
                        .into_iter()
                        .map(|p| self.reduce(p, shallow))
                        .collect::<Result<Vec<_>>>()?;
                    let ps = ps
                        .into_iter()
                        .map(|p| match p {
                            Term::Refl(t) => Ok(*t),
                            _ => Err(Error::NotRefl(p.boxed(), Loc::default())),
                        })
                        .rev()
                        .collect::<Result<Vec<_>>>()?;
                    let refl = t.subst_with(Substitution::parallel(ps.into_iter()), self);
                    Ok(Term::Refl(self.reduce(refl, shallow)?.boxed()).into())
                    // Ok(Term::ap([], [], self.reduce(refl)?))
                }
            }
            _ => unreachable!(
                "all the cases should be handled. Otherwise, check `is_whnf` function implementation"
            ),
        }
    }

    /// Build up a substitution and unfold the declaration.
    pub fn unfold_func(
        &mut self,
        _def: GI,
        func_name: Ident,
        body: Term,
        elims: Vec<Elim>,
    ) -> Result<(Simpl, Blocked<Term>)> {
        let name = func_name.text;
        // if name == "+-zero" {
        //     println!("func_name is empty");
        // }
        let mut es = elims;
        let es_len = es.len();
        let (tele, body) = body.tele_view_n(es_len);

        let tele_len = tele.len();
        let rest = es.split_off(tele_len);
        let vs = (0..es_len)
            .into_iter()
            .rev()
            .zip(&es)
            .map(|(i, t)| {
                (i, {
                    match t {
                        Elim::App(v) => *v.clone(),
                        _ => unimplemented!(),
                    }
                })
            })
            .collect::<HashMap<_, _>>();
        let subst = build_subst(vs, tele_len);

        let term = body.subst_with(subst, self).apply_elim(rest);
        let s = Simpl::Yes;
        Ok((s, Blocked::No(NotBlocked::NotBlocked, term)))
    }
}
/*
A = 0
S = 1
B = 2
T = 3

a = 0
b = 1
c = 2
d = 3
e = 4
f = 5
g = 6
h = 7
 */

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::unification::Occurrence;
    use crate::syntax::core::DeBruijn;
    use crate::syntax::desugar::desugar_prog;
    use crate::syntax::parser::Parser;
    use crate::syntax::tele_len::TeleLen;
    use crate::syntax::Bind;

    #[test]
    fn test_simplification() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let term = Term::lams(
            [Bind::unnamed(Term::meta(0)), Bind::unnamed(Term::meta(0))],
            Term::meta(1).apply(vec![
                Term::lam(
                    Bind::unnamed(Term::meta(0).boxed()),
                    Term::meta(1).apply(vec![Term::from_dbi(1), Term::from_dbi(2)]),
                ),
                Term::from_dbi(0),
                Term::from_dbi(1),
            ]),
        );
        let ctx_len = term.lam_len() - 1;
        let term = term.apply(vec![Term::from_dbi(ctx_len)]);
        println!("term = {}", term);
        let simp = env.simplify(term)?;
        println!("term' = {}", simp);
        let ctx_len = simp.lam_len() - 1;
        let simp = env.simplify(simp.apply(vec![Term::from_dbi(ctx_len)]))?;
        println!("term'' = {}", simp);
        Ok(())
    }

    #[test]
    fn test_simplification2() -> eyre::Result<()> {
        // (((\?0. (\?0. ?(1 @1 @1))))( @1)
        let _ = env_logger::try_init();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let term = Term::lams(
            [Bind::unnamed(Term::meta(0)), Bind::unnamed(Term::meta(0))],
            Term::meta(1).apply(vec![Term::from_dbi(1), Term::from_dbi(1)]),
        )
        .apply(vec![Term::from_dbi(1)]);
        // let ctx_len = term.lam_len() - 1;
        let fvs = term.fvs();
        println!("term = {}", term);
        let simp = env.simplify(term)?;
        let fvs2 = simp.fvs();
        println!("term' = {}", simp);
        assert_eq!(fvs, fvs2);
        Ok(())
    }

    #[test]
    fn test_simplification3() -> eyre::Result<()> {
        // ((\?0. (\?0. ?(2 @0))))( @1 @1)
        let _ = env_logger::try_init();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let term = Term::lams(
            [Bind::unnamed(Term::meta(0)), Bind::unnamed(Term::meta(0))],
            Term::meta(2).apply(vec![Term::from_dbi(0)]),
        )
        .apply(vec![Term::from_dbi(1), Term::from_dbi(1)]);
        let fvs = term.fvs();
        println!("term = {}", term);
        let simp = env.simplify(term)?;
        println!("term' = {}", simp);
        // assert_eq!(fvs, fvs2);
        Ok(())
    }
}
