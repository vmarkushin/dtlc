use std::fmt;
use std::path::PathBuf;

use crate::expr;
use crate::parser::Parser;

use eyre::{Result, WrapErr};
use rustyline::{error::ReadlineError, Editor};

struct Report(pub eyre::Report);

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut err = self.0.chain().peekable();
        writeln!(f, "Error: {}\n", err.next().unwrap())?;

        if err.peek().is_some() {
            writeln!(f, "Caused by:\n")?;
        }

        err.map(|e| e.to_string())
            .map(|e| e.replace("\n", ". "))
            .enumerate()
            .try_for_each(|(i, err)| writeln!(f, "\t{}: {}", i, err))
    }
}

pub fn repl(prompt: &str, mut f: impl FnMut(&'static str) -> Result<()>) {
    let mut rl = Editor::<()>::new();
    if rl
        .load_history(&PathBuf::from(std::env::var("HOME").unwrap()).join(".dtlc_history"))
        .is_err()
    {
        println!("No previous history.");
    }

    loop {
        let input = match rl.readline(prompt) {
            Err(ReadlineError::Eof | ReadlineError::Interrupted) => break,
            err @ Err(_) => err.unwrap(),
            Ok(ok) => ok,
        };
        let input: &str = &input;

        if input.is_empty() {
            break;
        }

        if input == "\n" {
            continue;
        }

        if let Err(e) = f(unsafe { std::mem::transmute(input) }) {
            eprintln!("\n{}", Report(e));
        }
    }

    rl.save_history("history.txt").unwrap();
}

pub fn run_repl(parser: &Parser, env: &mut expr::Env, input: &'static str) -> Result<()> {
    if let Some(input) = input.strip_prefix(":let ") {
        let mut item = parser
            .parse_item(input)
            .wrap_err("Failed to parse expression")?;
        item.infer_or_check_type_in(env.clone())
            .wrap_err("Failed to typecheck expression")?;
        env.add_item(item);
        return Ok(());
    }

    let expr = parser
        .parse_expr(input)
        .wrap_err("Failed to parse expression")?;
    println!("in: {}", &expr);
    expr.typeck(env.clone())
        .wrap_err("Failed to typecheck expression")?;
    println!("{}", expr.normalize_in(env));
    Ok(())
}
