#![feature(box_syntax, box_patterns, type_alias_impl_trait)]

use dtlc::repl;

fn main() {
    env_logger::init();
    repl::repl("> ", true, repl::run_repl);
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
