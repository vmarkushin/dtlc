#[macro_export]
macro_rules! ty {
    ($v:ident) => {
        crate::typeck::tvar(stringify!($v))
    };
    (($($t0:tt)+) -> $($t1:tt)+) => {
        crate::typeck::arrow($crate::ty!($($t0)+), $crate::ty!($($t1)+))
    };
    ($t0:ident -> $($t1:tt)+) => {
        crate::typeck::arrow($crate::ty!($t0), $crate::ty!($($t1)+))
    };
    (forall $v:ident . $($t:tt)+) => {
        crate::typeck::forall(stringify!($v), $crate::ty!($($t)+))
    };
}

#[macro_export]
macro_rules! e {
    ($v:ident) => {
        crate::expr::var(stringify!($v))
    };
    ($e0:ident ($($e1:tt)+)) => {
        crate::expr::app(e!($e0), e!($($e1)+))
    };
    (($($e0:tt)+) $e1:ident) => {
        crate::expr::app(e!($($e0)+), e!($e1))
    };
    (($($e0:tt)+) ($($e1:tt)+)) => {
        crate::expr::app(e!($($e0)+), e!($($e1)+))
    };
    ($e0:ident $e1:ident) => {
        crate::expr::app(e!($e0), e!($e1))
    };
    (($($e:tt)+) [$($t:tt)+]) => {
        crate::expr::tapp(e!($($e)+), $crate::ty!($($t)+))
    };
    ($e:ident [$($t:tt)+]) => {
        crate::expr::tapp(e!($e), $crate::ty!($($t)+))
    };
    (lam $v:ident : $t:ident . $($e:tt)+) => {
        crate::expr::lam(stringify!($v), $crate::ty!($t), e!($($e)+))
    };
    (lam $v:literal : $t:ident . $($e:tt)+) => {
        crate::expr::lam($v, $crate::ty!($t), e!($($e)+))
    };
    (lam $v:ident : ($($t:tt)+) . $($e:tt)+) => {
        crate::expr::lam(stringify!($v), $crate::ty!($($t)+), e!($($e)+))
    };
    (lam $v:ident . $($t:tt)+) => {
        crate::expr::tlam(stringify!($v), e!($($t)+))
    };
}

#[test]
fn macro_works() {
    use crate::expr::{app, lam, tapp, tlam, var};
    use crate::typeck::{arrow, forall, tvar};

    assert_eq!(ty!(x), tvar("x"));
    assert_eq!(ty!(x -> y), arrow("x", "y"));
    assert_eq!(ty!(x -> y -> z), arrow("x", arrow("y", "z")));
    assert_eq!(ty!((x -> y) -> z), arrow(arrow("x", "y"), "z"));
    assert_eq!(ty!(forall x. x), forall("x", "x"));
    assert_eq!(ty!(forall x. forall x. x), forall("x", forall("x", "x")));

    assert_eq!(e!(x), var("x"));
    assert_eq!(e!(x y), app("x", "y"));
    assert_eq!(e!((x y) z), app(app("x", "y"), "z"));
    assert_eq!(e!(x (y z)), app("x", app("y", "z")));
    assert_eq!(e!((x y) (z w)), app(app("x", "y"), app("z", "w")));
    assert_eq!(e!(x[y]), tapp("x", "y"));
    assert_eq!(e!((x y)[z]), tapp(app("x", "y"), "z"));
    assert_eq!(e!(lam x:a. x), lam("x", "a", "x"));
    assert_eq!(e!(lam a. lam x:a. x), tlam("a", lam("x", "a", "x")));
}
