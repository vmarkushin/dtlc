#![feature(box_syntax, box_patterns, type_alias_impl_trait)]
#![feature(cell_update)]
#![feature(generic_associated_types)]
#![feature(try_blocks)]

#[allow(
    clippy::needless_lifetimes,
    clippy::new_without_default,
    clippy::just_underscores_and_digits,
    clippy::clone_on_copy,
    clippy::type_complexity,
    clippy::unit_arg,
    clippy::extra_unused_lifetimes,
    clippy::match_single_binding,
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

mod check;
pub mod macros;
pub mod parser;
pub mod repl;
pub mod syntax;
pub mod token;
