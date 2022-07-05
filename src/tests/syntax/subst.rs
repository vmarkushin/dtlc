use crate::tests::syntax::{eq_sub, SubCx};
use quickcheck::Gen;
use quickcheck_macros::quickcheck;
use std::rc::Rc;

#[quickcheck]
fn prop_subst_split(SubCx(cx, subst): SubCx) -> bool {
    let subst = Rc::new(subst);
    if cx.len() == 0 {
        return true;
    }
    let mut g = Gen::new(10);
    (0..cx.len()).all(|i| {
        let (s1, s2) = subst.clone().split(i);
        eq_sub(&mut g, s1.union(s2), subst.clone(), cx.clone())
    })
}
