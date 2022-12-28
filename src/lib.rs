#![allow(
    non_snake_case,
    confusable_idents,
    mixed_script_confusables,
    dead_code,
    incomplete_features
)]
#![feature(
    box_syntax,
    box_patterns,
    type_alias_impl_trait,
    cell_update,
    try_blocks,
    never_type,
    closure_lifetime_binder,
    specialization,
    adt_const_params,
    trait_alias
)]
#![feature(let_chains)]

#[macro_use]
extern crate log;

pub mod check;
pub mod error;
pub mod macros;
pub mod repl;
pub mod syntax;

#[cfg(test)]
mod tests;

#[cfg(test)]
extern crate quickcheck;
