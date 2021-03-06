use crate::check::block::{Blocked, Stuck};
use crate::check::state::TypeCheckState;
use crate::check::{Error, Result};
use crate::syntax::core::{build_subst, Closure, Decl, Elim, Func, Simpl, Subst, Term, Val};
use crate::syntax::{ConHead, Ident, GI};
use std::collections::HashMap;

fn elims_to_terms(elims: Vec<Elim>) -> Result<Vec<Term>> {
    elims
        .into_iter()
        .map(Elim::try_into_app)
        .collect::<Result<_, String>>()
        .map_err(Error::NotTerm)
}

impl TypeCheckState {
    /// Normalize a term.
    pub fn simplify(&self, term: Term) -> Result<Val> {
        match term {
            Term::Whnf(whnf) => Ok(whnf),
            Term::Redex(f, id, elims) => match f {
                Func::Index(def) => match self.def(def) {
                    Decl::Data(_) => Ok(Val::inductive(def, elims_to_terms(elims)?)),
                    Decl::Cons(cons) => {
                        let head = ConHead::new(id, cons.data);
                        Ok(Val::Cons(head, elims_to_terms(elims)?))
                    }
                    Decl::Proj { .. } => unimplemented!(),
                    Decl::Func(func) => match self.unfold_func(def, id, func.body.clone(), elims) {
                        Ok((_, term)) => self.simplify(term),
                        Err(blockage) => match blockage.stuck {
                            Stuck::NotBlocked => self.simplify(blockage.anyway),
                            _ => Err(Error::Blocked(box blockage)),
                        },
                    },
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
        // dsp!(&body);
        let (tele, body) = body.tele_view_n(es_len);
        // dsp!(&body);
        // dbg!(&tele);
        // dbg!(&es);
        // debug_assert!(es.len() <= tele.len());

        let tele_len = tele.len();
        let rest = es.split_off(tele_len);
        let vs = (0..es_len)
            // let vs = ((tele_len - es_len)..tele_len)
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
