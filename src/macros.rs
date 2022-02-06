#[macro_export]
macro_rules! pt {
    ($p:ident, $d:ident, $s:literal) => {
        $d.desugar_expr($p.parse_expr($s)?)?
    };
}

#[macro_export]
macro_rules! ptis {
    ($p:ident, $d:ident, $e:ident, $s:literal) => {{
        let term = $e.infer(&$d.desugar_expr($p.parse_expr($s)?)?)?.0.ast;
        let val = $e.simplify(term)?;
        val
    }};
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

/// Evaluate `$x:expr` and if not true return `Err($y:expr)`.
#[macro_export]
macro_rules! assert_err {
    ( $x:expr, $y:expr $(,)? ) => {{
        assert_eq!($x, Err($y.into()));
    }};
}

#[macro_export]
macro_rules! dsp {
    // NOTE: We cannot use `concat!` to make a static string as a format argument
    // of `eprintln!` because `file!` could contain a `{` or
    // `$val` expression could be a block (`{ .. }`), in which case the `eprintln!`
    // will be malformed.
    () => {
        eprintln!("[{}:{}]", file!(), line!())
    };
    ($val:expr $(,)?) => {
        // Use of `match` here is intentional because it affects the lifetimes
        // of temporaries - https://stackoverflow.com/a/48732525/1063961
        match $val {
            tmp => {
                eprintln!("[{}:{}] {} = {}",
                    file!(), line!(), stringify!($val), &tmp);
                tmp
            }
        }
    };
    ($($val:expr),+ $(,)?) => {
        ($($crate::dsp!($val)),+,)
    };
}
