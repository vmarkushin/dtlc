mod dbi;
mod decl;
mod fold;
mod pats;
mod pretty;
mod redex;
mod subst;
mod term;

use crate::syntax::Loc;
pub use dbi::DeBruijn;
pub use decl::{ConsInfo, DataInfo, Decl, FuncInfo, ProjInfo};
pub use fold::FoldVal;
pub use pats::Simpl;
pub use pretty::pretty_application;
pub use redex::Subst;
pub use subst::{build_subst, PrimSubst, Substitution};
pub use term::{Bind, Closure, Elim, Func, Lambda, Term, Val, ValData};

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

/// Contexts.
pub type Ctx = Vec<Term>;

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
