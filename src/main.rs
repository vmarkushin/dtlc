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

use crate::expr::Expr;
use crate::item::Item;
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
        match f(input) {
            Err(e) => eprintln!("{}", e),
            _ => (),
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
            item.infer_or_check_type_in(env.clone())
                .map_err(|e| anyhow!("Type error: {}", e))?;
            env.add_item(item);
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
fn test_parser() {
    assert!(grammar::ExprParser::new().parse("x").is_ok());
}
