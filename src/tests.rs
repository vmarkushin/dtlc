use crate::expr::BExpr;

#[track_caller]
pub fn assert_beta_eq(e1: BExpr, e2: BExpr) {
    let nf1 = e1.nf();
    let nf2 = e2.nf();
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
