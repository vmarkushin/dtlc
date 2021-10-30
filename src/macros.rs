#[macro_export]
macro_rules! t {
    (*) => {
        Kinds::Star
    };
    (fun $x:tt : ($($ty:tt)+) => $($tt:tt)+) => {
        lam(stringify!($x), t!($($ty)+), t!($($tt)+))
    };
    (fun $x:tt : $ty:tt => $($tt:tt)+) => {
        lam(stringify!($x), t!($ty), t!($($tt)+))
    };
    (forall $x:tt : ($($tt1:tt)+), $($tt2:tt)+) => {
        pi(stringify!($x), t!($($tt1)+), t!($($tt2)+))
    };
    (forall $x:tt : $tt1:tt, $($tt2:tt)+) => {
        pi(stringify!($x), t!($tt1), t!($($tt2)+))
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
    ($val:tt) => {
        BExpr::from(stringify!($val))
    };
    (@ $f:tt $($aa:tt)+) => {
        app_many($f, [$(t!($aa)),+])
    };
    ($f:tt $($aa:tt)+) => {
        app_many(stringify!($f), [$(t!($aa)),+])
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
