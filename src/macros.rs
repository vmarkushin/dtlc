#[macro_export]
macro_rules! t {
    ($($it:tt)+) => {
        crate::parser::Parser::default()
            .parse_expr(stringify!($($it)+))
            .map(std::boxed::Box::new)
            .unwrap()
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
