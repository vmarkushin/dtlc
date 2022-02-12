#[macro_export]
macro_rules! ty {
    ($v:ident) => {
        crate::typeck::base(stringify!($v))
    };
    (($($t0:tt)+) -> $($t1:tt)+) => {
        crate::typeck::arrow($crate::ty!($($t0)+), $crate::ty!($($t1)+))
    };
    ($t0:ident -> $($t1:tt)+) => {
        crate::typeck::arrow($crate::ty!($t0), $crate::ty!($($t1)+))
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
    (lam $v:ident : $t:ident . $($e:tt)+) => {
        crate::expr::lam(stringify!($v), $crate::ty!($t), e!($($e)+))
    };
    (lam $v:literal : $t:ident . $($e:tt)+) => {
        crate::expr::lam($v, $crate::ty!($t), e!($($e)+))
    };
    (lam $v:ident : ($($t:tt)+) . $($e:tt)+) => {
        crate::expr::lam(stringify!($v), $crate::ty!($($t)+), e!($($e)+))
    };
}

#[test]
fn macro_works() {
    use crate::expr::{app, lam, var};
    use crate::typeck::{arrow, base};

    assert_eq!(ty!(x), base("x"));
    assert_eq!(ty!(x -> y), arrow("x", "y"));
    assert_eq!(ty!(x -> y -> z), arrow("x", arrow("y", "z")));
    assert_eq!(ty!((x -> y) -> z), arrow(arrow("x", "y"), "z"));

    assert_eq!(e!(x), var("x"));
    assert_eq!(e!(x y), app("x", "y"));
    assert_eq!(e!((x y) z), app(app("x", "y"), "z"));
    assert_eq!(e!(x (y z)), app("x", app("y", "z")));
    assert_eq!(e!((x y) (z w)), app(app("x", "y"), app("z", "w")));
    assert_eq!(e!(lam x:a. x), lam("x", "a", "x"));
}
