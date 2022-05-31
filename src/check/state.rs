use crate::check::meta::MetaContext;
use crate::syntax::core::{Bind, DeBruijn, Decl, Subst, Substitution, Tele, Term};
use crate::syntax::{DBI, GI, UID};
use std::fmt::{Display, Error, Formatter, Write};

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
    pub gamma: Tele,
    /// Meta variable context, scoped. Always global.
    pub meta_ctx: Vec<MetaContext<Term>>,
}

#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct Indentation {
    tc_depth: usize,
    /// How many indentations should we add when enter each sub-inference-rule?
    indentation_size: usize,
}

impl Display for Indentation {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        for _ in 0..self.tc_depth * self.indentation_size {
            f.write_char(' ')?;
        }
        Ok(())
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
        self.gamma.reserve(additional);
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

    pub fn local(&self, ix: DBI) -> &Bind {
        let len = self.gamma.len();
        &self.gamma[len - ix - 1]
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

    pub fn mut_local(&mut self, ix: DBI) -> &mut Bind {
        &mut self.gamma[ix]
    }
}
