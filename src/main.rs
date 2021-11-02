#![feature(box_syntax, box_patterns)]

#[allow(
    clippy::needless_lifetimes,
    clippy::new_without_default,
    clippy::just_underscores_and_digits,
    clippy::clone_on_copy,
    clippy::type_complexity,
    clippy::unit_arg,
    clippy::extra_unused_lifetimes,
    dead_code,
    unused_imports
)]
mod grammar {
    pub use grammar::*;
    use lalrpop_util::lalrpop_mod;

    lalrpop_mod!(grammar);
}

pub mod decl;
mod env;
pub mod macros;
pub mod parser;
mod repl;
pub mod term;
mod token;

fn main() {
    repl::repl("> ", repl::run_repl);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        env::{EnvedMut},
        parser::Parser,
        term::{Term},
    };

    #[test]
    fn test_parser() {
        assert!(Parser::default().parse_term("x").is_ok());
    }

    fn run_prog(s: impl AsRef<str>) -> Term {
        let prog = Parser::default().parse_prog(s.as_ref()).unwrap();
        EnvedMut::from((prog, &mut Default::default())).run()
    }

    #[test]
    #[ignore]
    fn test_uni() {
        let e = run_prog(
            r#"
            data Nat
                | O : Nat
                | S : Nat -> Nat

            let replicate := lam (A : Type) (n : Nat) => Vec n A

            data Vector | Vec : Nat -> Type -> Vector

            let main := replicate Nat O
        "#,
        );
        assert_eq!(e, t! { Vec O Nat })
    }
}
