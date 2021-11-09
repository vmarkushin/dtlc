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

#[macro_use]
extern crate log;

pub mod decl;
pub mod env;
pub mod infer;
pub mod macros;
pub mod parser;
pub mod repl;
pub mod term;
pub mod token;
