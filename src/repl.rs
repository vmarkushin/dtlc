use std::path::PathBuf;
use std::{borrow::Cow, fmt, fs};

use crate::check::TypeCheckState;
use crate::syntax::core::pretty;
use crate::syntax::desugar::{desugar_prog, DesugarState};
use crate::syntax::parser::Parser;
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
            .map(|e| e.replace('\n', ". "))
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
    des: DesugarState,
    env: TypeCheckState,
}

impl Helper {
    #[allow(unused)]
    pub fn typecheck(
        &mut self,
        ctx: &mut ValidationContext,
    ) -> rustyline::Result<ValidationResult> {
        // SAFETY: We convert every error to string, so we dont keep them longer than input.
        let input: &'static str = unsafe { std::mem::transmute(ctx.input()) };

        if input.is_empty() {
            return Ok(ValidationResult::Valid(None));
        }

        match run_repl(&mut self.parser, &mut self.des, &mut self.env, input) {
            Ok(_) => Ok(ValidationResult::Valid(None)),
            Err(err) => Ok(ValidationResult::Invalid(Some(
                "\n".to_owned() + &Report(err).to_string(),
            ))),
        }
    }
}

impl Default for Helper {
    fn default() -> Self {
        let mut des = DesugarState::default();
        des.enter_local_scope();
        des.cur_meta_id.push(Default::default());

        Self {
            validator: Default::default(),
            highlighter: Default::default(),
            hinter: HistoryHinter {},

            parser: Parser::default(),
            des,
            env: TypeCheckState::default(),
        }
    }
}

impl Help for Helper {}

impl Validate for Helper {
    fn validate(&self, _ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        // self.validator
        //     .validate(ctx)
        //     .and_then(|_| self.typecheck(ctx))
        Ok(ValidationResult::Valid(None))
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

pub fn repl(
    prompt: &str,
    use_std: bool,
    mut f: impl FnMut(&mut Parser, &mut DesugarState, &mut TypeCheckState, &'static str) -> Result<()>,
) {
    let mut rl = Editor::with_config(
        config::Config::builder()
            .auto_add_history(true)
            .color_mode(ColorMode::Enabled)
            .build(),
    );

    let mut helper = Helper::default();
    if use_std {
        load_module(
            &mut helper.parser,
            &mut helper.des,
            &mut helper.env,
            "lib/prelude.dtl",
        )
        .expect("Failed to load prelude");
    }

    rl.set_helper(Some(helper));

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

        if let Err(e) = f(&mut helper.parser, &mut helper.des, &mut helper.env, input) {
            eprintln!("\n{}", Report(e));
        }
    }

    rl.save_history(&history).unwrap();
}

pub fn run_repl(
    parser: &mut Parser,
    des: &mut DesugarState,
    env: &mut TypeCheckState,
    input: &'static str,
) -> Result<()> {
    if let Some(input) = input.strip_prefix(":l ") {
        load_module(parser, des, env, input)?;
        return Ok(());
    }
    if input.starts_with("fn ") || input.starts_with("data ") {
        let decl = parser
            .parse_decl(input)
            .wrap_err("Failed to parse expression")?;
        let len = des.decls.len();
        let _ = des
            .desugar_decl(decl)
            .wrap_err("Failed to desugar expression")?;
        let check_res = env
            .check_decls(des.decls[len..].iter().cloned(), des.cur_meta_id.clone())
            .wrap_err("Failed to type-check expression");
        if check_res.is_err() {
            let decl = des.decls.pop().unwrap();
            des.decls_map.remove(&decl.ident().text);
            des.cur_meta_id.pop();
        }
        check_res?;
        return Ok(());
    }

    let infer_type;
    let input = if let Some(input) = input.strip_prefix(":t ") {
        infer_type = true;
        input
    } else {
        infer_type = false;
        input
    };

    let expr = parser
        .parse_expr(input)
        .wrap_err("Failed to parse expression")?;
    let expr = des
        .desugar_expr(expr)
        .wrap_err("Failed to desugar expression")?;
    if !infer_type {
        let infer_res = env
            .infer(&expr)
            .map(|x| x.0.ast)
            .wrap_err("Failed to infer type for the expression");
        if infer_res.is_err() {
            des.cur_meta_id.pop();
        }
        let term = infer_res?;
        let norm = env
            .normalize(term)
            .wrap_err("Failed to simplify the expression")?;
        println!("{}", pretty(&norm, env));
    } else {
        des.cur_meta_id.push(Default::default());
        env.enter_def(env.sigma.len(), *des.cur_meta_id.last().unwrap());
        let res = env
            .infer(&expr)
            .map(|x| x.1)
            .wrap_err("Failed to infer type for the expression");
        env.exit_def();
        env.meta_ctx.pop();
        des.cur_meta_id.pop();
        let t = res?;
        println!("{}", t);
    }
    Ok(())
}

fn load_module(
    parser: &mut Parser,
    des: &mut DesugarState,
    env: &mut TypeCheckState,
    input: &str,
) -> Result<()> {
    let content = fs::read_to_string(input)?;
    let prog = parser.parse_prog(&content).unwrap();
    *des = desugar_prog(prog).unwrap();
    env.check_prog(des.clone())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::repl::{run_repl, Helper};

    #[test]
    fn test_adding_new_decls() -> eyre::Result<()> {
        let mut helper = Helper::default();
        run_repl(
            &mut helper.parser,
            &mut helper.des,
            &mut helper.env,
            "data B : Type | t | f",
        )?;
        run_repl(
            &mut helper.parser,
            &mut helper.des,
            &mut helper.env,
            "fn id (T : Type) := T",
        )?;
        Ok(())
    }

    #[test]
    fn test_adding_new_decls_intermediate_steps_failed() -> eyre::Result<()> {
        let mut helper = Helper::default();
        assert!(run_repl(
            &mut helper.parser,
            &mut helper.des,
            &mut helper.env,
            "data Nat : Type | O Type1",
        )
        .is_err());
        assert!(run_repl(
            &mut helper.parser,
            &mut helper.des,
            &mut helper.env,
            "data Nat : Type | O Type2",
        )
        .is_err());
        run_repl(
            &mut helper.parser,
            &mut helper.des,
            &mut helper.env,
            "data B : Type | t | f",
        )?;
        run_repl(
            &mut helper.parser,
            &mut helper.des,
            &mut helper.env,
            "fn id (T : Type) := T",
        )?;
        assert!(run_repl(
            &mut helper.parser,
            &mut helper.des,
            &mut helper.env,
            "id t _",
        )
        .is_err());
        assert!(run_repl(
            &mut helper.parser,
            &mut helper.des,
            &mut helper.env,
            "id Type1 _",
        )
        .is_err());
        Ok(())
    }
}
