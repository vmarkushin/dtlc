//! Paper: (Andreas Abel and Brigitte Pientka. Higher-Order Dynamic Pattern Unification for
//! Dependent Types and Records)[https://www.cse.chalmers.se/~abela/unif-sigma-long.pdf].

use crate::check::Result;
use crate::check::{Clause, TypeCheckState};
use crate::syntax::core::{
    Bind, Boxed, Closure, Ctx, DeBruijn, Elim, Func, Lambda, Subst, Substitution, Term,
};
use crate::syntax::{Ident, MI};
use itertools::Itertools;
use std::collections::HashMap;
use std::iter;
use vec1::{vec1, Vec1};

/// Unification constraint.
pub enum Constraint {
    /// ⊤
    Unit,
    /// ⊥
    Inconsistency,
    /// Unify `Ψ |- M = N : C`.
    Unify {
        ctx: Ctx,
        a: Term,
        b: Term,
        ty: Term,
    },
    /// Unify evaluation context `Ψ | R:A |- E = E'`.
    UnifyEvalCtx {
        ctx: Ctx,
        head: Term,
        head_ty: Term,
        elims_a: Vec<Elim>,
        elims_b: Vec<Elim>,
    },
    /// Solution found for `Ψ |- u <- M : C`.
    Solution {
        ctx: Ctx,
        meta: MI,
        a: Term,
        ty: Term,
    },
}

pub struct UnificationProblem {
    pub ctx: Ctx,
    pub constraints: Vec1<Constraint>,
}

pub type ConstraintSet = Vec1<Constraint>;
pub type MetaSubstitution = HashMap<MI, MetaSubstitutionSingle>;

impl Constraint {
    /// Local simplification (fig. 2).
    fn local_simplification(self, tcs: &mut TypeCheckState) -> Result<ConstraintSet> {
        let cs = self
            .decomposition(tcs)?
            .into_iter()
            .map(|c| c.eta_contraction().map(|x| x.into_vec()))
            .flatten_ok()
            .collect::<Result<Vec<_>>>()?;
        Ok(Vec1::try_from_vec(cs).unwrap())
    }

    fn decomposition(self, tcs: &mut TypeCheckState) -> Result<ConstraintSet> {
        let c = match self {
            Constraint::Unit => Constraint::Unit,
            Constraint::Inconsistency => Constraint::Inconsistency,
            Constraint::Unify {
                mut ctx,
                mut a,
                mut b,
                ty,
            } => {
                let (ctx, a, b, ty) = match ty {
                    // Decomposition of functions
                    Term::Pi(x, body) => {
                        ctx.push(x.clone().unboxed());
                        let Closure::Plain(body) = body;
                        let update = |term| {
                            match term {
                                Term::Lam(Lambda(y, n)) => {
                                    debug_assert_eq!(y.ty, x.ty);
                                    let Closure::Plain(n) = n;
                                    n.unboxed()
                                }
                                t => {
                                    // ctx:  x : A, y : B
                                    // t  = foo x@1 y@0
                                    // ctx': x : A, y : B, z : C
                                    // t' = foo x@2 y@1 z@0
                                    t.subst(Substitution::raise(1))
                                        .apply(vec![Term::from_dbi(0)])
                                }
                            }
                        };
                        let a = update(a);
                        let b = update(b);
                        (ctx, a, b, body.unboxed())
                    }
                    // TODO: Decomposition of pairs (Σ)
                    ty => {
                        if a.is_meta() || b.is_meta() {
                            // Orientation
                            if b.is_meta() {
                                if a.is_meta() {
                                    return Ok(Vec1::new(Constraint::Unify { ctx, a, b, ty }));
                                } else {
                                    std::mem::swap(&mut a, &mut b);
                                }
                            }

                            (ctx, a, b, ty)
                        } else {
                            // Decomposition of neutrals
                            let (head_a, elims_a) = a.head_elims_view();
                            let (head_b, elims_b) = b.head_elims_view();
                            let head_mismatch = head_a != head_b;
                            if head_mismatch {
                                debug!(target: "unification", "head mismatch: {} != {}", head_a, head_b);
                                return Ok(Vec1::new(Constraint::Inconsistency));
                            }
                            let head_ty = tcs.with_ctx(ctx.clone(), |tcs| tcs.type_of(&head_a))?;
                            return Ok(Vec1::new(Constraint::UnifyEvalCtx {
                                ctx,
                                head: head_a,
                                head_ty,
                                elims_a,
                                elims_b,
                            }));
                        }
                    }
                };
                Constraint::Unify { ctx, a, b, ty }
            }
            Constraint::UnifyEvalCtx {
                ctx,
                head,
                head_ty,
                mut elims_a,
                mut elims_b,
            } => {
                // Decomposition of evaluation contexts
                if elims_a.is_empty() && elims_b.is_empty() {
                    return Ok(Vec1::new(Constraint::Unit));
                }
                if elims_a.is_empty() || elims_b.is_empty() {
                    return Ok(Vec1::new(Constraint::UnifyEvalCtx {
                        ctx,
                        head,
                        head_ty,
                        elims_a,
                        elims_b,
                    }));
                }

                let a = elims_a.remove(0);
                let b = elims_b.remove(0);
                match (a, b) {
                    (Elim::App(a), Elim::App(b)) => {
                        let a = a.unboxed();
                        let b = b.unboxed();

                        let c1 = Constraint::Unify {
                            ctx: ctx.clone(),
                            a: a.clone(),
                            b,
                            ty: head_ty.clone(),
                        };
                        let head_app = head.apply(vec![a.clone()]);
                        let head_app_ty =
                            tcs.with_ctx(ctx.clone(), |tcs| tcs.type_of(&head_app))?;
                        let c2 = Constraint::UnifyEvalCtx {
                            ctx: ctx.clone(),
                            head: head_app,
                            head_ty: head_app_ty,
                            elims_a,
                            elims_b,
                        };
                        return Ok(vec1![c1, c2]);
                    }
                    (Elim::Proj(_a), Elim::Proj(_b)) => {
                        todo!("unify projections")
                    }
                    _ => {
                        return Ok(Vec1::new(Constraint::Inconsistency));
                    }
                }
            }
            c => c,
            // TODO: Eliminating projections
        };
        Ok(Vec1::new(c))
    }

    /// η-Contraction
    fn eta_contraction(self) -> Result<ConstraintSet> {
        let c = match self {
            Constraint::Unify {
                mut ctx,
                mut a,
                mut b,
                ty,
            } => {
                if a.is_meta() || b.is_meta() {
                    let contract = |a: &mut Term| {
                        if let Term::Meta(_, es) = a {
                            for e in es.iter_mut() {
                                if let Elim::App(app) = e {
                                    *app = app.clone().eta_contract().boxed();
                                }
                            }
                        }
                    };
                    contract(&mut a);
                    contract(&mut b);
                }
                Constraint::Unify { ctx, a, b, ty }
            }
            c => c,
        };
        Ok(Vec1::new(c))
    }
}

/// Unification problem: `∆ ||- K`.
pub struct Problem {
    pub meta_ctx: Ctx,
    pub constraints: Vec<Constraint>,
}

/// Meta substitution.
/// `Φ.M/u`
struct MetaSubstitutionSingle {
    ctx: Ctx,
    term: Term,
    meta_id: MI,
}

impl MetaSubstitutionSingle {
    pub fn new(ctx: Ctx, term: Term, meta_id: MI) -> Self {
        Self { ctx, term, meta_id }
    }
}

/// Unification steps (fig. 3). `∆ ||- K |-> ∆' ||- Κ'`
impl Problem {
    /// Local simplification
    pub fn local_simplification(&mut self, tcs: &mut TypeCheckState) -> Result<()> {
        let mut new_constraints = Vec::new();
        for c in self.constraints.drain(..) {
            let c = c.local_simplification(tcs)?;
            new_constraints.extend(c.into_iter());
        }
        self.constraints = new_constraints;
        Ok(())
    }

    /// Instantiation.
    /// `∆ ||- K + (Φ ⊢ u <- M : A)  =  [[θ]]∆ ||- [[θ]]K ∧ [[θ]]Φ ⊢ u <- M : [[θ]]A`
    ///                                   `where θ = Φ.M/u`
    pub fn instantiation(
        &mut self,
        // tcs: &mut TypeCheckState,
        ctx: Ctx,
        mi: MI,
        term: Term,
        mut ty: Term,
    ) -> Result<()> {
        let subst_one = MetaSubstitutionSingle::new(ctx, term.clone(), mi);
        let subst = iter::once(subst_one).map(|s| (s.meta_id, s)).collect();
        self.meta_ctx.subst_meta(&subst);
        self.constraints.subst_meta(&subst);
        ty.subst_meta(&subst);
        self.constraints.push(Constraint::Solution {
            ctx: self.meta_ctx.clone(),
            meta: mi,
            a: term,
            ty,
        });
        Ok(())
    }

    /// Lowering
    pub fn lower(&mut self) {}
}

trait MetaSubst {
    fn subst_meta(&mut self, subst: &MetaSubstitution);
}

impl MetaSubst for Ctx {
    fn subst_meta(&mut self, subst: &MetaSubstitution) {
        for ty in self.iter_mut() {
            ty.subst_meta(subst);
        }
    }
}

impl MetaSubst for Bind {
    fn subst_meta(&mut self, subst: &MetaSubstitution) {
        self.ty.subst_meta(subst);
    }
}

impl MetaSubst for Term {
    fn subst_meta(&mut self, subst: &MetaSubstitution) {
        todo!()
    }
}

impl MetaSubst for Constraint {
    fn subst_meta(&mut self, subst: &MetaSubstitution) {
        todo!()
    }
}

impl<T> MetaSubst for Vec<T>
where
    T: MetaSubst,
{
    fn subst_meta(&mut self, subst: &MetaSubstitution) {
        for t in self.iter_mut() {
            t.subst_meta(subst);
        }
    }
}
