use std::borrow::Borrow;
use std::path::PathBuf;
use std::{borrow::Cow, fmt};

use crate::env::{Env, Enved};
use crate::parser::Parser;

use crate::token::Token;
use eyre::{Result, WrapErr};
use logos::Logos;
use owo_colors::colored::Color;
use owo_colors::colors::css::Orange;
use owo_colors::{OwoColorize, Stream, XtermColors};
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
struct SyntaxHighlighter {
    truecolor: bool,
}

impl SyntaxHighlighter {
    pub fn new(truecolor: bool) -> Self {
        SyntaxHighlighter { truecolor }
    }
}

impl rustyline::highlight::Highlighter for SyntaxHighlighter {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        use owo_colors::AnsiColors::*;
        let tokens = Token::lexer(line);
        let mut copy = line.to_owned();
        let mut offset = 0;

        for (tok, span) in tokens.spanned() {
            let span = span.start + offset..span.end + offset;
            let prev = &copy[span.clone()];
            let maybe_colour = match tok {
                Token::Lam => Some((Red, XtermColors::MuesliOrange)),
                Token::Let => Some((BrightYellow, XtermColors::FlushOrange)),
                Token::Universe(_) => Some((Red, XtermColors::FlushOrange)),
                Token::Pi => Some((Red, XtermColors::MuesliOrange)),
                Token::Sigma => Some((Red, XtermColors::MuesliOrange)),
                Token::Data => Some((BrightYellow, XtermColors::FlushOrange)),
                Token::Codata => Some((BrightYellow, XtermColors::FlushOrange)),
                Token::DArrow => Some((Yellow, XtermColors::MuesliOrange)),
                Token::Assignment => Some((Yellow, XtermColors::MuesliOrange)),
                Token::Ident(n) if n.starts_with(char::is_uppercase) => {
                    Some((Green, XtermColors::BlazeOrange))
                }
                _ => None,
            };
            if let Some(col) = maybe_colour {
                let colored = if self.truecolor {
                    format!("{}", prev.color(col.1))
                } else {
                    format!("{}", prev.color(col.0))
                };
                offset += colored.len() - prev.len();
                copy.replace_range(span, &colored);
            }
        }
        Cow::Owned(copy)
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        Cow::Borrowed(hint)
    }

    fn highlight_candidate<'c>(
        &self,
        candidate: &'c str,
        completion: CompletionType,
    ) -> Cow<'c, str> {
        panic!("{}", candidate)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        true
    }
}

#[derive(Default)]
struct Highlighter {
    brackets: MatchingBracketHighlighter,
    syntax: SyntaxHighlighter,
}

impl Highlight for Highlighter {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.syntax.highlight(line, pos)
    }

    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        self.syntax.highlight_prompt(prompt, default)
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        self.syntax.highlight_hint(hint)
    }

    fn highlight_candidate<'c>(
        &self,
        candidate: &'c str,
        completion: CompletionType,
    ) -> Cow<'c, str> {
        self.syntax.highlight_candidate(candidate, completion)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.syntax.highlight_char(line, pos)
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

        if input.starts_with("let") || input.starts_with("data") {
            let res = self
                .parser
                .parse_decl(input)
                .wrap_err("Failed to parse expression");
            let mut decl = validate_incomplete!(res);
            validate_incomplete!(decl
                .infer_or_check_type_in(&mut Cow::Borrowed(&self.env))
                .wrap_err("Failed to typecheck expression"));
            return Ok(ValidationResult::Valid(None));
        }
        if let Some(input) = input.strip_prefix(":t ") {
            let term = validate_incomplete!(self
                .parser
                .parse_term(input)
                .wrap_err("Failed to parse expression"));
            let t = validate_incomplete!(term
                .typeck(&mut Cow::Borrowed(&self.env))
                .wrap_err("Failed to typecheck expression"));
            return Ok(ValidationResult::Valid(None));
        }

        let term = validate_incomplete!(self
            .parser
            .parse_term(input)
            .wrap_err("Failed to parse expression"));
        validate_incomplete!(term
            .typeck(&mut Cow::Borrowed(&self.env))
            .wrap_err("Failed to typecheck expression"));
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
    rl.set_helper(Some(Helper {
        highlighter: Highlighter {
            syntax: SyntaxHighlighter::new(true),
            ..Default::default()
        },
        ..Default::default()
    }));

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
    if input.starts_with("let") || input.starts_with("data") {
        let mut decl = parser
            .parse_decl(input)
            .wrap_err("Failed to parse expression")?;
        decl.infer_or_check_type_in(&mut Cow::Borrowed(env))
            .wrap_err("Failed to typecheck expression")?;
        env.add_decl(decl);
        return Ok(());
    }
    if let Some(input) = input.strip_prefix(":t ") {
        let term = parser
            .parse_term(input)
            .wrap_err("Failed to parse expression")?;
        let t = term
            .typeck(&mut Cow::Borrowed(env))
            .wrap_err("Failed to typecheck expression")?;
        println!("{}", t);
        return Ok(());
    }

    let term = parser
        .parse_term(input)
        .wrap_err("Failed to parse expression")?;
    println!("in: {}", &term);
    term.typeck(&mut Cow::Borrowed(env))
        .wrap_err("Failed to typecheck expression")?;
    println!("{}", Enved::from((term, &*env)).nf());
    Ok(())
}
