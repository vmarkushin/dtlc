#[macro_export]
macro_rules! t {
    ($($it:tt)+) => {
        crate::parser::Parser::new(crate::grammar::ExprParser::new(), crate::grammar::ItemParser::new())
            .parse_expr(stringify!($($it)+))
            .map(std::boxed::Box::new)
            .unwrap()
    };
    (*) => {
        Kinds::Star
    };
    (fun $x:tt : ($($ty:tt)+) => $($tt:tt)+) => {
        lam(t!($x), t!($($ty)+), t!($($tt)+))
    };
    (fun $x:tt : $ty:tt => $($tt:tt)+) => {
        lam(t!($x), t!($ty), t!($($tt)+))
    };
    (forall $x:tt : ($($tt1:tt)+), $($tt2:tt)+) => {
        pi(t!($x), t!($($tt1)+), t!($($tt2)+))
    };
    (forall $x:tt : $tt1:tt, $($tt2:tt)+) => {
        pi(t!($x), t!($tt1), t!($($tt2)+))
    };
    ({$($tt:tt)+}) => {
        BExpr::from($($tt)+)
    };
    (@ $val:tt) => {
        BExpr::from($val)
    };
    ((@ $val:tt)) => {
        BExpr::from($val)
    };
    (($($tt1:tt)+) -> $($tt2:tt)+) => {
        arrow(t!($($tt1)+), t!($($tt2)+))
    };
    ($tt1:tt -> $tt2:tt) => {
        arrow(t!($tt1), t!($tt2))
    };
    (($($tt:tt)+)) => {
        t!($($tt)+)
    };
    ($val:tt) => { stringify!($f).parse::<BExpr>().unwrap() };
    (@ $f:tt $($aa:tt)+) => {
        app_many($f, [$(t!($aa)),+])
    };
    ($f:tt $($aa:tt)+) => {
        app_many(t!($f), [$(t!($aa)),+])
    };
}

/// Return Err of the expression: `return Err($expression);`.
#[macro_export]
macro_rules! fail {
    ( $y:expr ) => {{
        return Err($y.into());
    }};
}

/// Evaluate `$x:expr` and if not true return `Err($y:expr)`.
#[macro_export]
macro_rules! ensure {
    ( $x:expr, $y:expr $(,)? ) => {{
        if !$x {
            $crate::fail!($y);
        }
    }};
}
