mod dbi;
mod decl;
mod fold;
mod id;
mod pats;
mod pretty;
mod redex;
mod subst;
mod term;

use crate::check::unification::{Flavour, Occurrence};
use crate::check::TypeCheckState;
use crate::syntax;
use crate::syntax::{Loc, DBI};
pub use dbi::DeBruijn;
pub use decl::{ConsInfo, DataInfo, Decl, FuncInfo, ProjInfo};
pub use fold::FoldVal;
use itertools::Itertools;
pub use pats::Simpl;
pub use pretty::{display_application, pretty, pretty_list, Indentation, Pretty};
pub use redex::{Subst, SubstWith};
use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};
use std::rc::Rc;
pub use subst::{build_subst, PrimSubst, Substitution};
pub use term::{
    Bind, BoundFreeVars, Case, Closure, Elim, Func, Id, Lambda, Name, Pat, Term, Twin, Type, Val,
    ValData, Var,
};

impl Term {
    pub fn at(self, loc: Loc) -> TermInfo {
        TermInfo::new(self, loc)
    }
}

/// A value with syntax info.
/// This is what should be stored inside of the context.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TermInfo {
    pub ast: Term,
    pub loc: Loc,
}

impl TermInfo {
    pub fn new(ast: Term, loc: Loc) -> Self {
        Self { ast, loc }
    }

    pub fn map_ast(self, f: impl FnOnce(Term) -> Term) -> Self {
        Self::new(f(self.ast), self.loc)
    }
}

pub type Let<T = Term> = syntax::Let<T>;

/// Telescopes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tele<T = Bind>(pub Vec<T>);

impl<T> Default for Tele<T> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<T: Clone> Tele<T> {
    pub(crate) fn skipping(&self, n: usize) -> Self {
        Self(self.0.iter().skip(n).cloned().collect())
    }
}

impl<T> Tele<T> {
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub fn into_ctx(self) -> Ctx<T> {
        Ctx(self.0)
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut()
    }

    pub fn push(&mut self, b: T) {
        self.0.insert(0, b);
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        Some(self.0.remove(0))
    }

    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn to_elims(self) -> Vec<Elim> {
        self.0
            .into_iter()
            .enumerate()
            .map(|(i, b)| Elim::app(Term::from_dbi(i)))
            .collect()
    }
}

impl<T: Binder> Tele<T> {
    pub fn names(&self) -> Vec<Name> {
        self.0
            .iter()
            .enumerate()
            .map(|(i, x)| match x.to_name() {
                Name::Bound(_) => Name::Bound(i),
                x => x,
            })
            .collect()
    }
}

impl<T: Display> Display for Tele<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0.iter().map(|b| format!("({})", b)).join(", ")
        )
    }
}

impl SubstWith<'_> for Tele {
    fn subst_with(self, mut subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Self {
        Tele(
            self.0
                .into_iter()
                .enumerate()
                .map(|(i, b)| {
                    if i != 0 {
                        subst = subst.clone().lift_by(1);
                    }
                    b.subst_with(subst.clone(), tcs)
                })
                .collect(),
        )
    }
}

impl<T> IntoIterator for Tele<T> {
    type Item = T;
    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// Contexts. Dual to telescopes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ctx<B = Bind>(pub Vec<B>);

impl<B: Occurrence> Occurrence for Ctx<B> {
    fn go(&self, depth: usize, vars: &mut HashSet<Name>, kind: Flavour, in_flexible: bool) {
        self.0
            .iter()
            .for_each(|b| b.go(depth, vars, kind, in_flexible));
    }
}

impl<B> Default for Ctx<B> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

pub trait Binder {
    type Param: Display;
    type Var: Into<usize> + Display + Copy;

    fn lookup(&self, var: &Self::Var) -> Option<Bind<&Self::Param>>;
    fn to_name(&self) -> Name;
}

impl Binder for Bind {
    type Param = Type;
    type Var = DBI;

    fn lookup(&self, _var: &Self::Var) -> Option<Bind<&Type>> {
        Some(Bind {
            licit: self.licit,
            name: self.name.clone(),
            ty: &self.ty,
            ident: self.ident.clone(),
        })
    }

    fn to_name(&self) -> Name {
        self.to_name()
    }
}

impl<B: Binder + Debug> Ctx<B> {
    #[track_caller]
    fn var_to_idx(&self, v: B::Var) -> usize {
        let v: usize = v.into();
        debug_assert!(self.0.len() > v, "invalid DBI: {}", v);
        self.0.len() - v - 1
    }

    #[track_caller]
    pub fn lookup(&self, v: B::Var) -> Bind<&B::Param> {
        // self.0
        //     .get(self.var_to_idx(v))
        //     .unwrap_or_else(|| panic!("Invalid DBI: {}", v))
        let x = self
            .0
            .get(self.var_to_idx(v))
            .unwrap_or_else(|| panic!("Invalid DBI: {}", v));
        x.lookup(&v)
            .unwrap_or_else(|| panic!("Invalid binder: {:?}", x))
    }

    pub fn remove(&mut self, v: B::Var) -> B {
        self.0.remove(self.var_to_idx(v))
    }

    /// Splits the context into two contexts with a binder in between.
    pub fn split(&mut self, v: B::Var) -> (B, Ctx<B>) {
        let idx = self.var_to_idx(v);
        let bind = self.0.remove(idx);
        let Γ2 = self.0.split_off(idx);
        (bind, Ctx(Γ2))
    }
}

impl<B: Clone> Ctx<B> {
    pub(crate) fn skipping(&self, n: usize) -> Self {
        Self(self.0.iter().skip(n).cloned().collect())
    }
}

impl<B> Ctx<B> {
    pub fn extend<I: IntoIterator<Item = B>>(&mut self, iter: I) {
        self.0.extend(iter)
    }

    pub fn into_tele(self) -> Tele<B> {
        Tele::<B>(self.0)
    }

    pub fn iter(&self) -> impl Iterator<Item = &B> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut B> {
        self.0.iter_mut()
    }

    pub fn push(&mut self, b: B) {
        self.0.push(b);
    }

    pub fn pop(&mut self) -> Option<B> {
        self.0.pop()
    }

    pub(crate) fn popn(&mut self, count: usize) -> Self {
        Self(self.0.split_off(self.0.len() - count))
    }

    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }
}

impl<T> IntoIterator for Ctx<T> {
    type Item = T;
    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T: Display> Display for Ctx<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0.iter().map(|b| format!("({})", b)).join(", ")
        )
    }
}

impl SubstWith<'_> for Ctx<Bind<Type>> {
    fn subst_with(self, mut subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Self {
        Ctx(self
            .0
            .into_iter()
            .enumerate()
            .map(|(i, b)| {
                if i != 0 {
                    subst = subst.clone().lift_by(1);
                }
                b.subst_with(subst.clone(), tcs)
            })
            .collect())
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LetList(pub Vec<Let>);

impl LetList {
    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn new(field0: Vec<Let>) -> Self {
        Self(field0)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Let> {
        self.0.iter()
    }
}

pub trait Boxed {
    fn boxed(self) -> Box<Self>;

    fn unboxed(self: Box<Self>) -> Self
    where
        Self: Sized,
    {
        *self
    }
}

impl<T> Boxed for T {
    fn boxed(self) -> Box<Self> {
        Box::new(self)
    }
}

#[cfg(test)]
mod tests {

    use crate::check::{TypeCheckState, Unify};
    use crate::syntax::desugar::desugar_prog;
    use crate::syntax::parser::Parser;
    use crate::{pct, pe};

    #[test]
    fn test_id() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | O
            | S Nat
        data Bool : Type
            | true
            | false

        fn id := lam (A : Type) (x : A) => x
        fn zero := lam (s : Nat -> Nat) (z : Nat) => z
        fn main := id Nat (zero S O)
        fn comp
            (A : Type)
            (B : Type)
            (C : B -> Type)
            (f : (x : B) -> C x)
            (g : A -> B)
            (x : A)
            : C (g x)
            := f (g x)
        "#,
        )?)?;
        let mut env = TypeCheckState::default();
        env.check_prog(des.clone())?;

        let val = pct!(p, des, env, "main");
        let val1 = pct!(p, des, env, "O");
        Unify::unify(&mut env, &val, &val1)?;

        let val = pct!(p, des, env, "Nat -> Nat");
        env.check(&pe!(p, des, "id Nat"), &val)?;

        let val = pct!(p, des, env, "Bool -> Bool");
        env.check(&pe!(p, des, "id Bool"), &val)?;
        Ok(())
    }
}
