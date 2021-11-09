use dtlc::repl;

fn main() {
    env_logger::init();
    repl::repl("> ", repl::run_repl);
}

#[cfg(test)]
mod test {
    use super::*;
    use dtlc::t;
    use dtlc::{env::EnvedMut, parser::Parser, term::Term};

    #[test]
    fn test_parser() {
        assert!(Parser::default().parse_term("x").is_ok());
    }

    fn run_prog(s: impl AsRef<str>) -> Term {
        let prog = Parser::default().parse_prog(s.as_ref()).unwrap();
        EnvedMut::from((prog, &mut Default::default())).run()
    }

    #[test]
    #[ignore]
    fn test_uni() {
        let e = run_prog(
            r#"
            data Nat
                | O : Nat
                | S : Nat -> Nat

            fn replicate := lam (A : Type) (n : Nat) => Vec n A

            data Vector | Vec : Nat -> Type -> Vector

            fn main := replicate Nat O
        "#,
        );
        assert_eq!(e, t! { Vec O Nat })
    }
}
