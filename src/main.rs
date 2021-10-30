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

pub mod expr;
pub mod item;
pub mod macros;
pub mod parser;
mod repl;
mod token;

use crate::parser::Parser;

fn main() {
    let parser = Parser::new(grammar::ExprParser::new(), grammar::ItemParser::new());
    let mut env = expr::Env::new();
    repl::repl("> ", |input| repl::run_repl(&parser, &mut env, input));
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::expr::{app, app_many};

    #[test]
    fn test_parser() {
        assert!(grammar::ExprParser::new().parse("x").is_ok());
    }

    #[test]
    fn test_uni() {
        let parser = Parser::new(grammar::ExprParser::new(), grammar::ItemParser::new());
        let mut env = expr::Env::new();

        let replicate = parser
            .parse_expr("fun A : * => fun n : Nat => Vec n A")
            .unwrap();
        env.add_item(
            parser
                .parse_item("data Nat | O : Nat | S : Nat -> Nat")
                .unwrap(),
        );

        env.add_item(
            parser
                .parse_item("data Vector | Vec : Nat -> * -> Vector")
                .unwrap(),
        );
        let e = app_many(t! { Vec }, [t! { O }, t! { Nat }]);
        e.typeck(env.clone()).unwrap();
        let e = e.nf_in(&env);

        let e = app_many(replicate, ["Nat", "O"]);
        e.typeck(env.clone()).unwrap();
        let e = e.normalize_in(&env);
        println!("{}", e);
        println!("{:?}", e);
    }
}
