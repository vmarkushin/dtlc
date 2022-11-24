use crate::check::block::{Blocked, Stuck};
use crate::check::state::TypeCheckState;
use crate::check::{Error, Result};
use crate::syntax::core::{
    build_subst, Boxed, Case, Closure, Decl, Elim, Func, Simpl, SubstWith, Substitution, Term, Val,
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
    /// Normalize a term.
    pub fn simplify(&mut self, term: Term) -> Result<Term> {
        if matches!(term, Term::Match(..)) {
            trace!("simplifying match: {}", &term);
        }
        match term {
            Term::Id(mut id) => {
                id.a1 = Term::from(self.simplify(*id.a1)?).boxed();
                id.a2 = Term::from(self.simplify(*id.a2)?).boxed();
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
                        match self.unfold_func(
                            def,
                            id.clone(),
                            func.body.as_ref().unwrap().clone(),
                            elims.clone(),
                        ) {
                            /*
                            Ok((simp, term)) => match simp {
                                Simpl::Yes => self.simplify(term),
                                Simpl::No => Ok(Term::Redex(
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
                                )),
                            },
                             */
                            Ok((_, term)) =>{
                                self.simplify(term)
                            }
                            Err(blockage) => match blockage.stuck {
                                Stuck::NotBlocked => self.simplify(blockage.anyway),
                                // Stuck::OnElim(e) => {
                                //     trace!("stuck on elim: {}", e);
                                //     // TODO: simplify elims?
                                //     Ok(Term::Redex(f, id, elims))
                                // }
                                _ => Err(Error::Blocked(box blockage)),
                            },
                        }
                    }
                },
                Func::Lam(lam) => {
                    let mut term = lam.1;
                    for elim in elims {
                        term = Closure::Plain(
                            box term
                                .instantiate_safe_with(elim.into_app(), self)
                                .unwrap()
                                .tele_view()
                                .1,
                        );
                    }
                    let Closure::Plain(term) = term;
                    self.simplify(*term)
                }
            },
            Term::Match(x, mut cs) => {
                debug!("Simplifying match");
                match try_match(&self.simplify(*x.clone())?, &cs) {
                    Some((i, sigma)) => {
                        debug!("matched {}th case with σ = {}", i, sigma);
                        let matched_case = cs.remove(i);
                        trace!("matched_case.body = {}", matched_case.body);
                        let term1 = matched_case.body.subst_with(sigma, self);
                        trace!("matched_case.bodyσ = {}", term1);
                        self.simplify(term1)
                    }
                    None => Err(Error::Blocked(box Blocked::new(
                        Stuck::OnElim(Elim::App(x.clone())),
                        Term::Match(x, cs),
                    ))),
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
        _func_name: Ident,
        body: Term,
        elims: Vec<Elim>,
    ) -> Result<(Simpl, Term), Blocked<Term>> {
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

        let s = Simpl::No;
        Ok((s, body.subst_with(subst, self).apply_elim(rest)))
    }
}
