use dtlc::env::Env;
use dtlc::term::*;

#[track_caller]
pub fn assert_beta_eq(e1: Term, e2: Term) {
    let env = Env::default();
    let nf1 = e1.nf(&env);
    let nf2 = e2.nf(&env);
    let eq = nf1.alpha_eq(&nf2);
    if !eq {
        panic!(
            r#"assertion failed: `(left != right)`
left: `{:?}`,
right: `{:?}`"#,
            nf1, nf2,
        )
    }
}
