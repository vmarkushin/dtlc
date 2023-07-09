use crate::check::block::{Blocked, NotBlocked};
use crate::check::state::TypeCheckState;
use crate::check::{Error, Result};
use crate::syntax::core::{
    build_subst, Boxed, Case, Closure, Decl, Elim, Func, Simpl, SubstWith, Substitution, Term,
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
    pub fn simplify_blocked(&mut self, term: Blocked<Term>) -> Result<Term> {
        match term {
            Blocked::Yes(_, t) => Ok(t),
            Blocked::No(_, t) => self.simplify(t),
        }
    }

    /// Normalize a term.
    pub fn simplify(&mut self, term: Term) -> Result<Term> {
        let term_out = self.simplify_impl(term.clone())?;
        debug!(
            "{}[simplify]\n\t{}\n\t{}",
            self.tc_depth_ws(),
            term,
            term_out
        );
        Ok(term_out)
    }

    pub fn simplify_impl(&mut self, term: Term) -> Result<Term> {
        if matches!(term, Term::Match(..)) {
            trace!("simplifying match: {}", &term);
        }
        match term {
            Term::Id(mut id) => {
                id.a1 = self.simplify(*id.a1)?.boxed();
                id.a2 = self.simplify(*id.a2)?.boxed();
                Ok(Term::Id(id).into())
            }
            t if t.is_whnf() => Ok(t),
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
                        // Ok((simp, term)) =>{
                            match simp {
                                Simpl::Yes => {
                                    self.simplify_blocked(term)
                                }
                                Simpl::No => {
                                    Ok(Term::Redex(
                                        f,
                                        id,
                                        elims
                                            .into_iter()
                                            .map(|e| match e {
                                                Elim::App(t) => {
                                                    Ok(Elim::App(self.simplify(*t)?.boxed()))
                                                }
                                                e => Ok(e),
                                            })
                                            .collect::<Result<_>>()?,
                                    ))
                                }
                            }
                            // self.simplify(term)
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
                            //     NotBlocked::NotBlocked => self.simplify(blockage.anyway),
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
                    for elim in elims {
                        term = Closure::Plain(
                            term
                                .instantiate_safe_with(elim.into_app(), self)
                                .unwrap()
                                .tele_view()
                                .1.boxed(),
                        );
                    }
                    let Closure::Plain(term) = term;
                    self.simplify(*term)
                }
            },
            Term::Match(x, mut cs) => {
                debug!("Simplifying match");
                let simplified = self.simplify(*x.clone())?;
                match try_match(&simplified, &cs) {
                    Some((i, sigma)) => {
                        debug!("matched {}th case with σ = {}", i, sigma);
                        let matched_case = cs.remove(i);
                        trace!("matched_case.body = {}", matched_case.body);
                        let term1 = matched_case.body.subst_with(sigma, self);
                        trace!("matched_case.bodyσ = {}", term1);
                        self.simplify(term1)
                    }
                    None => {
                    // TODO: simplify cases?
                        Ok(Term::Match(simplified.boxed(), cs))
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
                    Ok(Term::Refl(self.simplify(*t)?.boxed()).into())
                    // Ok(Term::ap([], [], self.simplify(*t)?))
                } else {
                    let ps = ps
                        .into_iter()
                        .map(|p| self.simplify(p))
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
                    Ok(Term::Refl(self.simplify(refl)?.boxed()).into())
                    // Ok(Term::ap([], [], self.simplify(refl)?))
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
        if name == "+-zero" {
            println!("func_name is empty");
        }
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
