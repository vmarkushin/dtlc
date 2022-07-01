use crate::check::block::{Blocked, Stuck};
use crate::check::state::TypeCheckState;
use crate::check::{Error, Result};
use crate::syntax::core::{
    build_subst, Case, Closure, Decl, Elim, Func, Simpl, Subst, Substitution, Term, Val,
};
use crate::syntax::{ConHead, Ident, GI};
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
pub fn try_match(x: &Val, cs: &[Case]) -> Option<(usize, Rc<Substitution>)> {
    let term = x.clone().into();
    cs.iter()
        .enumerate()
        .filter_map(|(i, c)| c.pattern.match_term(&term).map(|j| (i, j)))
        .next()
}

impl TypeCheckState {
    /// Normalize a term.
    pub fn simplify(&self, term: Term) -> Result<Val> {
        match term {
            Term::Whnf(whnf) => Ok(whnf),
            Term::Redex(f, id, elims) => match f {
                Func::Index(def) => match self.def(def) {
                    // TODO: make a separate function for each data and constructor
                    Decl::Data(_) => Ok(Val::inductive(def, elims_to_terms(elims)?)),
                    Decl::Cons(cons) => {
                        let head = ConHead::new(id, cons.data_gi);
                        Ok(Val::Cons(head, elims_to_terms(elims)?))
                    }
                    Decl::Proj { .. } => unimplemented!(),
                    Decl::Func(func) => {
                        match self.unfold_func(def, id, func.body.as_ref().unwrap().clone(), elims)
                        {
                            Ok((_, term)) => self.simplify(term),
                            Err(blockage) => match blockage.stuck {
                                Stuck::NotBlocked => self.simplify(blockage.anyway),
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
                                .instantiate_safe(elim.into_app())
                                .unwrap()
                                .tele_view()
                                .1,
                        );
                    }
                    let Closure::Plain(term) = term;
                    self.simplify(*term)
                }
            },
            Term::Match(x, mut cs) => match try_match(&self.simplify(*x.clone())?, &cs) {
                Some((i, sigma)) => {
                    let matched_case = cs.remove(i);
                    self.simplify(matched_case.body.subst(sigma))
                }
                None => Err(Error::Blocked(box Blocked::new(
                    Stuck::OnElim(Elim::App(x.clone())),
                    Term::Match(x, cs),
                ))),
            },
        }
    }

    /// Build up a substitution and unfold the declaration.
    pub fn unfold_func(
        &self,
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
        Ok((s, body.subst(subst).apply_elim(rest)))
    }
}
