mod dbi;
mod decl;
mod fold;
mod id;
mod pats;
mod pretty;
mod redex;
mod subst;
mod term;

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
use std::fmt::{Display, Formatter};
use std::rc::Rc;
pub use subst::{build_subst, PrimSubst, Substitution};
pub use term::{Bind, Case, Closure, Elim, Func, Id, Lambda, Pat, Term, Val, ValData, Var};

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
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Tele(pub Vec<Bind>);

impl Tele {
    pub(crate) fn skipping(&self, n: usize) -> Self {
        Self(self.0.iter().skip(n).cloned().collect())
    }

    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub fn into_ctx(self) -> Ctx {
        Ctx(self.0)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Bind> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Bind> {
        self.0.iter_mut()
    }

    pub fn push(&mut self, b: Bind) {
        self.0.insert(0, b);
    }

    pub fn pop(&mut self) -> Option<Bind> {
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
}

impl Display for Tele {
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

impl IntoIterator for Tele {
    type Item = Bind;
    type IntoIter = <Vec<Bind> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// Contexts. Dual to telescopes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Ctx(pub Vec<Bind>);

impl Ctx {
    pub(crate) fn skipping(&self, n: usize) -> Self {
        Self(self.0.iter().skip(n).cloned().collect())
    }

    #[track_caller]
    fn dbi_to_idx(&self, v: DBI) -> usize {
        debug_assert!(self.0.len() > v, "invalid DBI: {}", v);
        self.0.len() - v - 1
    }

    #[track_caller]
    pub fn lookup(&self, v: DBI) -> &Bind {
        self.0
            .get(self.dbi_to_idx(v))
            .unwrap_or_else(|| panic!("Invalid DBI: {}", v))
    }

    pub fn remove(&mut self, v: DBI) -> Bind {
        self.0.remove(self.dbi_to_idx(v))
    }

    /// Splits the context into two contexts with a binder in between.
    pub fn split(&mut self, v: DBI) -> (Bind, Ctx) {
        let idx = self.dbi_to_idx(v);
        let bind = self.0.remove(idx);
        let Γ2 = self.0.split_off(idx);
        (bind, Ctx(Γ2))
    }

    pub fn extend<I: IntoIterator<Item = Bind>>(&mut self, iter: I) {
        self.0.extend(iter)
    }

    pub fn into_tele(self) -> Tele {
        Tele(self.0)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Bind> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Bind> {
        self.0.iter_mut()
    }

    pub fn push(&mut self, b: Bind) {
        self.0.push(b);
    }

    pub fn pop(&mut self) -> Option<Bind> {
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

impl IntoIterator for Ctx {
    type Item = Bind;
    type IntoIter = <Vec<Bind> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Display for Ctx {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0.iter().map(|b| format!("({})", b)).join(", ")
        )
    }
}

impl SubstWith<'_> for Ctx {
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
}

impl<T> Boxed for T {
    fn boxed(self) -> Box<Self> {
        Box::new(self)
    }
}

#[cfg(test)]
mod tests {

    use crate::check::{TypeCheckState, Unify};
    use crate::parser::Parser;
    use crate::syntax::desugar::desugar_prog;
    use crate::{pct, pe};

    #[test]
    fn test_id() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let p = Parser::default();
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
            (f : Π (x : B), C x)
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
