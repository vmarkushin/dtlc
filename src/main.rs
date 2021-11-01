#![feature(box_syntax)]

#[allow(
    clippy::needless_lifetimes,
    clippy::new_without_default,
    clippy::just_underscores_and_digits,
    clippy::clone_on_copy,
    clippy::type_complexity,
    dead_code,
    unused_imports
)]
mod grammar {
    pub use grammar::*;
    use lalrpop_util::lalrpop_mod;

    lalrpop_mod!(grammar);
}

mod env;
pub mod expr;
pub mod item;
pub mod macros;
pub mod parser;
mod repl;
mod token;

use crate::parser::Parser;

fn main() {
    repl::repl("> ", repl::run_repl);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        env::Env,
        expr::{app_many, BExpr},
    };

    #[test]
    fn test_parser() {
        assert!(Parser::default().parse_expr("x").is_ok());
    }

    fn run_prog(s: impl AsRef<str>) -> BExpr {
        Env::new().run(Parser::default().parse_prog(s.as_ref()).unwrap())
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
