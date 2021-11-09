use std::path::PathBuf;
use std::{borrow::Cow, fmt};

use crate::env::{Env, Enved};
use crate::parser::Parser;

use eyre::{Result, WrapErr};
use rustyline::{
    completion::Completer,
    config,
    error::ReadlineError,
    highlight::{Highlighter as Highlight, MatchingBracketHighlighter},
    hint::Hinter as DoHint,
    hint::HistoryHinter,
    validate::{
        MatchingBracketValidator, ValidationContext, ValidationResult, Validator as Validate,
    },
    ColorMode, CompletionType, Editor, Helper as Help,
};

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

#[derive(Default)]
struct Validator {
    brackets: MatchingBracketValidator,
}

impl Validate for Validator {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        self.brackets.validate(ctx)
    }
    fn validate_while_typing(&self) -> bool {
        false
    }
}

#[derive(Default)]
struct Highlighter {
    brackets: MatchingBracketHighlighter,
}

impl Highlight for Highlighter {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.brackets.highlight(line, pos)
    }
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        self.brackets.highlight_prompt(prompt, default)
    }
    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        self.brackets.highlight_hint(hint)
    }
    fn highlight_candidate<'c>(
        &self,
        candidate: &'c str,
        completion: CompletionType,
    ) -> Cow<'c, str> {
        self.brackets.highlight_candidate(candidate, completion)
    }
    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.brackets.highlight_char(line, pos)
    }
}

type Hinter = HistoryHinter;

struct Helper {
    validator: Validator,
    highlighter: Highlighter,
    hinter: Hinter,

    parser: Parser,
    env: Env,
}

impl Helper {
    pub fn typecheck(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        macro_rules! validate_incomplete {
            ( $e:expr ) => {
                match $e {
                    Ok(ok) => ok,
                    Err(err) => {
                        return Ok(ValidationResult::Invalid(Some(
                            "\n".to_owned() + &Report(err).to_string(),
                        )))
                    }
                }
            };
        }

        // SAFETY: We convert every error to string, so we dont keep them longer than input.
        let input: &'static str = unsafe { std::mem::transmute(ctx.input()) };

        if input.is_empty() {
            return Ok(ValidationResult::Valid(None));
        }

        if input.starts_with("fn") || input.starts_with("data") {
            let res = self
                .parser
                .parse_decl(input)
                .wrap_err("Failed to parse expression");
            let mut decl = validate_incomplete!(res);
            validate_incomplete!(decl
                .infer_or_check_type_in(&mut Cow::Borrowed(&self.env))
                .wrap_err("Failed to infer type for the expression"));
            return Ok(ValidationResult::Valid(None));
        }
        if let Some(input) = input.strip_prefix(":t ") {
            let term = validate_incomplete!(self
                .parser
                .parse_term(input)
                .wrap_err("Failed to parse expression"));
            let _t = validate_incomplete!(self
                .env
                .infer_type(term)
                .wrap_err("Failed to infer type for the expression"));
            return Ok(ValidationResult::Valid(None));
        }

        let term = validate_incomplete!(self
            .parser
            .parse_term(input)
            .wrap_err("Failed to parse expression"));
        validate_incomplete!(self
            .env
            .infer_type(term)
            .wrap_err("Failed to infer type for the expression"));
        Ok(ValidationResult::Valid(None))
    }
}

impl Default for Helper {
    fn default() -> Self {
        Self {
            validator: Default::default(),
            highlighter: Default::default(),
            hinter: HistoryHinter {},

            parser: Parser::default(),
            env: Env::default(),
        }
    }
}

impl Help for Helper {}
impl Validate for Helper {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        self.validator
            .validate(ctx)
            .and_then(|_| self.typecheck(ctx))
    }
    fn validate_while_typing(&self) -> bool {
        self.validator.validate_while_typing()
    }
}
impl Highlight for Helper {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        self.highlighter.highlight_prompt(prompt, default)
    }
    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        self.highlighter.highlight_hint(hint)
    }
    fn highlight_candidate<'c>(
        &self,
        candidate: &'c str,
        completion: CompletionType,
    ) -> Cow<'c, str> {
        self.highlighter.highlight_candidate(candidate, completion)
    }
    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}
impl DoHint for Helper {
    type Hint = String;
    fn hint(&self, line: &str, pos: usize, ctx: &rustyline::Context<'_>) -> Option<Self::Hint> {
        self.hinter.hint(line, pos, ctx)
    }
}
impl Completer for Helper {
    type Candidate = String;
}

pub fn repl(prompt: &str, mut f: impl FnMut(&Parser, &mut Env, &'static str) -> Result<()>) {
    let mut rl = Editor::with_config(
        config::Config::builder()
            .auto_add_history(true)
            .color_mode(ColorMode::Enabled)
            .build(),
    );
    rl.set_helper(Some(Helper::default()));

    let history = PathBuf::from(std::env::var("HOME").unwrap()).join(".dtlc_history");
    drop(rl.load_history(&history));

    loop {
        let input = match rl.readline(prompt) {
            Err(ReadlineError::Eof | ReadlineError::Interrupted) => break,
            err @ Err(_) => err.unwrap(),
            Ok(ok) => ok,
        };
        let helper = rl.helper_mut().unwrap();
        if input.is_empty() {
            continue;
        }

        let input: &str = &input;
        // SAFETY: safe, as long as we drop string longer than we hold error from
        // repl function.
        let input: &'static str = unsafe { std::mem::transmute(input) };

        if let Err(e) = f(&helper.parser, &mut helper.env, input) {
            eprintln!("\n{}", Report(e));
        }
    }

    rl.save_history(&history).unwrap();
}

pub fn run_repl(parser: &Parser, env: &mut Env, input: &'static str) -> Result<()> {
    if input.starts_with("fn") || input.starts_with("data") {
        let mut decl = parser
            .parse_decl(input)
            .wrap_err("Failed to parse expression")?;
        decl.infer_or_check_type_in(&mut Cow::Borrowed(env))
            .wrap_err("Failed to infer type for the expression")?;
        env.add_decl(decl);
        return Ok(());
    }
    if let Some(input) = input.strip_prefix(":t ") {
        let term = parser
            .parse_term(input)
            .wrap_err("Failed to parse expression")?;
        let t = env
            .infer_type(term)
            .wrap_err("Failed to infer type for the expression")?;
        return Ok(());
    }

    let term = parser
        .parse_term(input)
        .wrap_err("Failed to parse expression")?;
    env.infer_type(term.clone())
        .wrap_err("Failed to typecheck expression")?;
    println!("{}", term.nf(&*env));
    Ok(())
}
