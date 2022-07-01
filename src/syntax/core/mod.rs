mod dbi;
mod decl;
mod fold;
mod pats;
mod pretty;
mod redex;
mod subst;
mod term;

use crate::syntax;
use crate::syntax::{Loc, DBI};
pub use dbi::DeBruijn;
pub use decl::{ConsInfo, DataInfo, Decl, FuncInfo, ProjInfo};
pub use fold::FoldVal;
use itertools::Itertools;
pub use pats::Simpl;
pub use pretty::{pretty_application, pretty_list, Indentation};
pub use redex::Subst;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
pub use subst::{build_subst, PrimSubst, Substitution};
pub use term::{Bind, Case, Closure, Elim, Func, Lambda, Pat, Term, Val, ValData};

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

/// Telescopes.
pub type Tele = Vec<Bind>;
pub type TeleS = [Bind];
pub type Let<T = Term> = syntax::Let<T>;

/// Contexts. Dual to telescopes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Ctx(pub Vec<Bind>);

impl Ctx {
    pub(crate) fn skipping(&self, n: usize) -> Self {
        Self(self.0.iter().skip(n).cloned().collect())
    }

    fn dbu_to_idx(&self, v: DBI) -> usize {
        self.0.len() - v - 1
    }

    pub fn lookup(&self, v: DBI) -> &Bind {
        self.0
            .get(self.dbu_to_idx(v))
            .unwrap_or_else(|| panic!("Invalid DBI: {}", v))
    }

    /// Splits the context into two contexts with a binder in between.
    pub fn split(&mut self, v: DBI) -> (Bind, Ctx) {
        let idx = self.dbu_to_idx(v);
        let bind = self.0.remove(idx);
        let Γ2 = self.0.split_off(idx);
        (bind, Ctx(Γ2))
    }

    pub fn extend<I: IntoIterator<Item = Bind>>(&mut self, iter: I) {
        self.0.extend(iter)
    }

    pub fn into_tele(self) -> Tele {
        self.0
    }

    pub fn iter(&self) -> impl Iterator<Item = &Bind> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = Bind> {
        self.0.into_iter()
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

impl Iterator for Ctx {
    type Item = Bind;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
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

impl Subst for Ctx {
    fn subst(self, mut subst: Rc<Substitution>) -> Self {
        Ctx(self
            .0
            .into_iter()
            .enumerate()
            .map(|(i, b)| {
                if i != 0 {
                    subst = subst.clone().lift_by(1);
                }
                b.subst(subst.clone())
            })
            .collect())
        // match self {
        //     Closure::Plain(body) => Self::plain(body.subst(subst.lift_by(1))),
        // }
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
