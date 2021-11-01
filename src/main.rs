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
    let parser = Parser::default();
    let mut env = crate::env::Env::new();
    repl::repl("> ", |input| repl::run_repl(&parser, &mut env, input));
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parser() {
        assert!(Parser::default().parse_expr("x").is_ok());
    }

    #[test]
    #[ignore]
    fn test_uni() {
        let parser = Parser::default();
        let mut env = crate::env::Env::new();

        let prog = parser
            .parse_prog(
                r#"
            data Nat
                | O : Nat
                | S : Nat -> Nat

            let replicate => lam A : Type => lam n : Nat => Vec n A

            data Vector | Vec : Nat -> Type -> Vector

            let main => replicate Nat O
        "#,
            )
            .unwrap();

        let e = env.run(prog);
        println!("{}", e);
        println!("{:?}", e);
    }
}
