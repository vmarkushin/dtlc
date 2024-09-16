// use crate::check::meta::MetaContext;
use crate::check::unification::{Context, Param};
use crate::check::Error;
use crate::syntax::core::{
    Bind, Ctx, DeBruijn, Decl, Indentation, Let, LetList, Name, SubstCtx, SubstWith, Substitution,
    Term, Twin, Type, Var,
};
use crate::syntax::{LangItem, DBI, GI, MI, UID};
use std::collections::HashMap;
use std::fmt::Display;
use std::mem::swap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

/// Typing context.
pub type Sigma = Vec<Decl>;

/// Type-checking state.
#[derive(Debug, Clone)]
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
    pub gamma2: Ctx<Bind<Param>>,
    /// Let bindings.
    pub lets: LetList,
    /// Meta variable context, scoped. Always global.
    pub meta_ctx2: Context,
    pub next_uid: Arc<AtomicUsize>,
    // pub next_mi: MI,
    pub lang_items: HashMap<LangItem, GI>,
    pub lang_items_back: HashMap<GI, LangItem>,
    // pub cons_to_data_gi: HashMap<GI, GI>,
    /// Don't check universe levels.
    pub type_in_type: bool,
    /// If this flag is enabled, the most general solution will be generated for meta variables,
    /// where more than 1 solution is possible (and if the general solution is possible).
    ///
    /// For example, if the flag is enabled, in the code
    /// ```dtl
    ///     data Sigma (A : Type) (B : A -> Type) : Type1
    ///         | mkSigma (x : A) (y : B x)
    ///
    ///     fn main = mkSigma {_} {?m} zero true
    /// ```
    ///
    /// the solution for `?m` will be `?m := lam _ => Bool`, although, multiple solutions are possible here,
    /// because we can match on the argument, returning different types.
    pub generalize_metas: bool,
}

impl Default for TypeCheckState {
    fn default() -> Self {
        Self {
            indentation: Default::default(),
            current_checking_def: Default::default(),
            trace_tc: Default::default(),
            unify_depth: Default::default(),
            sigma: Default::default(),
            gamma: Default::default(),
            gamma2: Default::default(),
            lets: Default::default(),
            meta_ctx2: Default::default(),
            next_uid: Arc::new(AtomicUsize::new(1)),
            // next_mi: Default::default(),
            lang_items: Default::default(),
            lang_items_back: Default::default(),
            type_in_type: true,
            generalize_metas: false,
        }
    }
}

impl TypeCheckState {
    pub(crate) fn is_caseless(&self, ty: &Term) -> bool {
        match ty {
            Term::Data(data) => match self.def(data.def) {
                Decl::Data(data) => data.conses.is_empty(),
                _ => panic!("Not a data type: {}", ty),
            },
            _ => panic!("Not a data type: {}", ty),
        }
    }
}

impl TypeCheckState {
    #[track_caller]
    pub(crate) fn lookup(&self, p0: DBI) -> Bind<&Type> {
        self.gamma.lookup(p0)
    }

    #[track_caller]
    pub(crate) fn lookup2(&self, p0: Name) -> Bind<&Param> {
        self.gamma2.lookup(p0)
    }

    #[track_caller]
    pub(crate) fn lookup_var(&self, p0: Name, twin: Twin) -> Result<Bind<&Type>, Error> {
        info!(target: "additional", "lookup_var: {p0} {:?} in {}", twin, self.gamma2);
        let bind = self
            .gamma2
            .maybe_lookup(p0)
            .ok_or_else(|| Error::Other(format!("Variable not found: {:?}", p0)))?;
        Ok(match (twin, bind.ty) {
            (Twin::Left, Param::Twins(ty, _)) => bind.map_term(|_| ty),
            (Twin::Right, Param::Twins(_, ty)) => bind.map_term(|_| ty),
            (Twin::Only, Param::P(ty)) => bind.map_term(|_| ty),
            (x, y) => panic!(
                "Expected {x:?}, found {}, when looking up for the variable",
                y
            ),
        })
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

    pub fn under_ctx2<R, F: FnOnce(&mut Self) -> R>(
        &mut self,
        mut ctx: Ctx<Bind<Param>>,
        f: F,
    ) -> R {
        // info!(target: "additional", "under new ctx: {}", ctx);
        swap(&mut self.gamma2, &mut ctx);
        let res = f(self);
        swap(&mut self.gamma2, &mut ctx);
        res
    }

    /*
    @1 (?21 ( @0 (((\x[e]. (\_[-]. (?21 @1)))))))  ( @1 (?0 @1))

     */
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
        debug_assert!(self.lets.is_empty());
    }

    pub fn reserve_local_variables(&mut self, additional: usize) {
        self.gamma.0.reserve(additional);
        self.sigma.reserve(additional);
    }

    /// Create a new valid but unsolved meta variable,
    /// used for generating fresh metas during elaboration.
    pub fn fresh_meta(&mut self) -> Term {
        Term::meta(self.next_uid())
    }

    pub fn fresh_name(&self) -> Name {
        Name::Free(self.next_uid())
    }

    pub fn next_uid(&self) -> UID {
        self.next_uid.fetch_add(1, Ordering::Relaxed)
    }

    pub fn def(&self, ix: GI) -> &Decl {
        &self.sigma[ix]
    }

    pub fn def_mut(&mut self, ix: GI) -> &mut Decl {
        &mut self.sigma[ix]
    }

    pub fn def_id_by_name(&self, name: &str) -> usize {
        self.sigma
            .iter()
            .enumerate()
            .find(|(i, d)| d.ident().text == name)
            .map(|(i, _)| i)
            .unwrap()
    }

    pub fn def_by_name(&self, name: &str) -> &Decl {
        &self.sigma[self.def_id_by_name(name)]
    }

    pub fn cons_to_data_gi(&self, ix: GI) -> GI {
        assert!(self.sigma[ix].is_cons());
        // TODO: use hashmap in cons_to_data_gi
        let mut ix = ix - 1;
        while !self.sigma[ix].is_data() {
            ix -= 1;
        }
        ix
    }

    pub fn local_by_id(&mut self, id: UID) -> Let {
        self.local_by_id_safe(id)
            .unwrap_or_else(|| panic!("unresolved local {}", id))
    }

    pub fn local_by_id_safe(&mut self, id: UID) -> Option<Let> {
        let v = self.let_by_id_safe(id).cloned();
        let lookup_gamma = || {
            let (i, ty) = self.gamma_by_id_safe(id)?;
            let ty = ty.clone().subst_with(Substitution::raise(i + 1), self);
            Some(Let::new(ty, DeBruijn::from_dbi(i)))
        };
        v.or_else(lookup_gamma)
    }

    fn let_by_id_safe(&self, id: UID) -> Option<&Let> {
        self.lets.iter().find(|b| b.bind.name == id)
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

    pub fn lang_item(&self, item: LangItem) -> Option<GI> {
        self.lang_items.get(&item).copied()
    }
}

impl SubstCtx for TypeCheckState {
    fn fresh_uid(&mut self) -> UID {
        self.next_uid.fetch_add(1, Ordering::Relaxed)
    }

    fn next_fresh_uid(&mut self) -> UID {
        self.next_uid.load(Ordering::Relaxed)
    }
}

impl<T> Bind<T> {
    pub fn unbind<C: SubstCtx>(mut self, tcs: &mut C) -> Self {
        self.name = tcs.fresh_uid();
        assert_ne!(self.name, 0);
        self
    }
}

// pub trait Unbind<T>: Sized {
//     type Body: SubstWith;
//
//     fn into_closure(self) -> (Bind<T>, Option<Self::Body>);
//
//     fn unbind_smart(self, tcs: &mut TypeCheckState) -> (Bind<T>, Option<Self::Body>) {
//         let (x, b) = Unbind::<T>::into_closure(self);
//         let bind = x.unbind(tcs);
//         let uid = bind.name;
//         assert_ne!(uid, 0);
//         match b {
//             None => (bind, None),
//             Some(b) => (
//                 bind,
//                 Some(b.subst_with(Substitution::one(Term::free_var(uid)), tcs)),
//             ),
//         }
//     }
// }
