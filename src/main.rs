#![feature(box_patterns, type_alias_impl_trait, try_trait_v2)]

use dtlc::repl;
use std::convert::Infallible;
use std::ops::FromResidual;

struct OptionResult<T, E>(Option<Result<T, E>>);

impl<T, E> FromResidual<Option<Infallible>> for OptionResult<T, E> {
    fn from_residual(residual: Option<Infallible>) -> Self {
        Self(residual.map(|x| match x {}))
    }
}

impl<T, E> FromResidual<Result<Infallible, E>> for OptionResult<T, E> {
    fn from_residual(residual: Result<Infallible, E>) -> Self {
        Self(Some(residual.map(|x| match x {})))
    }
}

struct ResultOption<T, E>(Result<Option<T>, E>);

impl<T, E> FromResidual<Option<Infallible>> for ResultOption<T, E> {
    fn from_residual(residual: Option<Infallible>) -> Self {
        Self(Ok(residual.map(|x| match x {})))
    }
}

impl<T, E> FromResidual<Result<Infallible, E>> for ResultOption<T, E> {
    fn from_residual(residual: Result<Infallible, E>) -> Self {
        Self(residual.map(|x| match x {}))
    }
}

fn foo() -> Option<String> {
    Some(String::default())
}

fn bar() -> Result<(), String> {
    // Ok(())
    Err("nope".to_string())
}

fn any_try() -> ResultOption<(), String> {
    let _ = foo()?;
    let _ = bar()?;
    ResultOption(Ok(Some(())))
}

#[test]
fn tst() {
    dbg!(any_try().0);
}

fn main() {
    env_logger::init();
    repl::repl("> ", repl::run_repl);
}

#[cfg(test)]
mod tests {
    use dtlc::check::TypeCheckState;
    use dtlc::syntax::desugar::desugar_prog;
    use dtlc::syntax::parser::Parser;

    use std::fs;

    #[test]
    fn test_examples() -> eyre::Result<()> {
        use walkdir::WalkDir;
        let _ = env_logger::try_init();

        let mut p = Parser::default();
        for entry in WalkDir::new("examples") {
            let entry1 = entry?;
            let x = entry1.path();
            if let Some(ext) = x.extension() {
                if ext == "dtl" {
                    let content = fs::read_to_string(x)?;
                    match p.parse_prog(&content) {
                        Err(e) => {
                            panic!("{}", e);
                        }
                        Ok(prog) => {
                            let des = desugar_prog(prog)?;
                            let mut env = TypeCheckState::default();
                            env.check_prog(des.clone())?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
}
