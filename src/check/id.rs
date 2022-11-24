#[cfg(test)]
mod tests {
    use crate::check::{TypeCheckState, Unify};
    use crate::error::Error;
    use crate::parser::Parser;
    use crate::syntax::core::{pretty, Val};
    use crate::syntax::desugar::desugar_prog;
    use crate::{pct, pe, peit, typeck};

    #[test]
    fn test_infer_id() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let mut des = desugar_prog(p.parse_prog_with_std(
            r#"
        data Single : Type
            | sing Nat Nat

        fn foo (s : Single) : Nat := match s {
              | (sing n m) => n
        }
       "#,
            None,
        )?)?;
        let result: Result<(), Error> = try {
            env.check_prog(des.clone())?;
            env.trace_tc = true;

            typeck!(p, des, env, "ap 4", "Id (Nat, 4, (+ 3 1),)");

            let expr_str = "ap (lam A : Type => nil A) (ap Nat)";
            let ty_str = "Id (lam A : Type => ((List A), (nil A), (nil A),)) (ap Nat)";
            typeck!(p, des, env, expr_str, ty_str);
        };
        if let Err(e) = result {
            println!("{}", pretty(&e, &env));
        }
        Ok(())
    }
}
