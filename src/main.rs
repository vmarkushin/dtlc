#![feature(box_syntax)]

#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(grammar);

mod expr;
mod item;
pub mod macros;
mod parser;
#[cfg(test)]
mod tests;
mod token;

use crate::expr::{app, app_many};
use crate::parser::Parser;
use anyhow::anyhow;
use std::io;
use std::io::Write;

fn repl(prompt: &str, mut f: impl FnMut(String) -> anyhow::Result<()>) {
    loop {
        print!("{}", prompt);
        io::stdout().flush().unwrap();
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        if let Err(e) = f(input) {
            eprintln!("{}", e);
        }
    }
}

fn main() {
    let parser = Parser::new(grammar::ExprParser::new(), grammar::ItemParser::new());
    let mut env = expr::Env::new();
    repl("> ", |input| {
        if let Some(input) = input.strip_prefix(":let ") {
            let mut item = parser
                .parse_item(input)
                .map_err(|e| anyhow!("Parse error: {}", e))?;
            println!("in: {:?}", &item);
            item.infer_or_check_type_in(env.clone())
                .map_err(|e| anyhow!("Type error: {}", e))?;
            env.add_item(item);
            return Ok(());
        } else if let Some(input) = input.strip_prefix(":t ") {
            let expr = parser
                .parse_expr(&input)
                .map_err(|e| anyhow!("Parse error: {}", e))?;
            println!(
                "{}",
                expr.typeck(env.clone())
                    .map_err(|e| anyhow!("Type error: {}", e))?
            );
            return Ok(());
        }

        let expr = parser
            .parse_expr(&input)
            .map_err(|e| anyhow!("Parse error: {}", e))?;
        println!("in: {}", &expr);
        expr.typeck(env.clone())
            .map_err(|e| anyhow!("Type error: {}", e))?;
        println!("{}", expr.normalize_in(&env));
        Ok(())
    });
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
    let e = app_many("Vec", ["O", "Nat"]);
    e.typeck(env.clone()).unwrap();
    let e = e.normalize_in(&env);
    println!("{}", e);
    println!("{:?}", e);

    // let e = app_many(replicate, ["Nat", "O"]);
    // e.typeck(env.clone()).unwrap();
    // let e = e.normalize_in(&env);
    // println!("{}", e);
    // println!("{:?}", e);
}
