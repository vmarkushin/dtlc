#[track_caller]
fn assert_beta_eq(e1: BExpr, e2: BExpr) {
    let nf1 = nf(e1);
    let nf2 = nf(e2);
    let eq = alpha_eq(&nf1, &nf2);
    if !eq {
        panic!(
            r#"assertion failed: `(left != right)`
left: `{:?}`,
right: `{:?}`"#,
            nf1, nf2,
        )
    }
}
