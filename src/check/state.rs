use crate::check::meta::MetaContext;
use crate::syntax::core::{
    Bind, Ctx, DeBruijn, Decl, Indentation, Subst, Substitution, Tele, Term, Val,
};
use crate::syntax::{DBI, GI, UID};
use std::fmt::{Display, Error, Formatter, Write};
use std::mem::swap;

/// Typing context.
pub type Sigma = Vec<Decl>;

/// Type-checking state.
#[derive(Debug, Clone, Default)]
pub struct TypeCheckState {
    pub(crate) indentation: Indentation,
    /// Where are we?
    pub(crate) current_checking_def: Option<GI>,
    /// Are we tracing the type checking process?
    pub trace_tc: bool,
    /// Conversion check depth.
    pub unify_depth: DBI,

    /// Global context (definitions are attached with type annotations).
    pub sigma: Sigma,
    /// Local typing context.
    pub gamma: Ctx,
    /// Meta variable context, scoped. Always global.
    pub meta_ctx: Vec<MetaContext<Term>>,
}

impl TypeCheckState {
    pub(crate) fn is_caseless(&self, ty: &Term) -> bool {
        match ty {
            Term::Whnf(Val::Data(data)) => match self.def(data.def) {
                Decl::Data(data) => data.conses.is_empty(),
                _ => panic!("Not a data type: {}", ty),
            },
            _ => panic!("Not a data type: {}", ty),
        }
    }
}

impl TypeCheckState {
    pub(crate) fn lookup(&self, p0: DBI) -> &Bind {
        &self.gamma.lookup(p0)
    }
}

impl TypeCheckState {
    /// For debugging purpose.
    pub fn tc_depth_ws(&self) -> impl Display {
        self.indentation
    }

    pub fn indentation_size(&mut self, size: usize) {
        self.indentation.indentation_size = size;
    }

    pub fn tc_deeper(&mut self) {
        self.indentation.tc_depth += 1;
    }

    pub fn enter_def(&mut self, def: GI, metas_count: usize) {
        self.current_checking_def = Some(def);
        self.meta_ctx.push(Default::default());
        self.mut_meta_ctx().expand_with_fresh_meta(metas_count);
    }

    pub fn exit_def(&mut self) {
        self.current_checking_def = None;
    }

    pub fn with_ctx<R, F: FnOnce(&mut Self) -> R>(&mut self, ctx: Ctx, f: F) -> R {
        let old_len = self.gamma.len();
        self.gamma.0.extend(ctx.0);
        let res = f(self);
        self.gamma.0.truncate(old_len);
        res
    }

    pub fn under_ctx<R, F: FnOnce(&mut Self) -> R>(&mut self, mut ctx: Ctx, f: F) -> R {
        swap(&mut self.gamma, &mut ctx);
        let res = f(self);
        swap(&mut self.gamma, &mut ctx);
        res
    }

    pub fn tc_shallower(&mut self) {
        if self.indentation.tc_depth > 0 {
            self.indentation.tc_depth -= 1;
        }
    }

    pub fn tc_reset_depth(&mut self) {
        self.indentation.tc_depth = 0;
    }

    /// Should be invoked only before/after a decl check
    pub fn sanity_check(&self) {
        debug_assert_eq!(self.unify_depth, 0);
        debug_assert!(self.gamma.is_empty());
    }

    pub fn reserve_local_variables(&mut self, additional: usize) {
        self.gamma.0.reserve(additional);
        self.sigma.reserve(additional);
        self.meta_ctx.reserve(additional);
    }

    /// Create a new valid but unsolved meta variable,
    /// used for generating fresh metas during elaboration.
    pub fn fresh_meta(&mut self) -> Term {
        self.mut_meta_ctx().fresh_meta(|m| Term::meta(m, vec![]))
    }

    pub fn def(&self, ix: GI) -> &Decl {
        &self.sigma[ix]
    }

    pub fn local_by_id(&self, id: UID) -> (Bind<Term>, Term) {
        self.local_by_id_safe(id)
            .unwrap_or_else(|| panic!("unresolved local {}", id))
    }

    pub fn local_by_id_safe(&self, id: UID) -> Option<(Bind<Term>, Term)> {
        let (i, ty) = self.gamma_by_id_safe(id)?;
        let ty = ty.clone().subst(Substitution::raise(i + 1));
        Some((ty, DeBruijn::from_dbi(i)))
    }

    fn gamma_by_id_safe(&self, id: UID) -> Option<(DBI, &Bind)> {
        let gamma_len = self.gamma.len();
        (self.gamma.iter().enumerate())
            .find(|(_, b)| b.name == id)
            .map(|(ix, bind)| (gamma_len - ix - 1, bind))
    }

    pub fn mut_def(&mut self, ix: GI) -> &mut Decl {
        &mut self.sigma[ix]
    }

    pub fn meta_ctx(&self) -> &MetaContext<Term> {
        let we_are_here = self.current_checking_def.unwrap();
        &self.meta_ctx[we_are_here]
    }

    pub fn mut_meta_ctx(&mut self) -> &mut MetaContext<Term> {
        let we_are_here = self.current_checking_def.unwrap();
        &mut self.meta_ctx[we_are_here]
    }
}
