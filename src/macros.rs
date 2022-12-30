/// Parse expression.
#[macro_export]
macro_rules! pe {
    ($p:ident, $d:ident, $s:expr) => {
        $d.desugar_expr($p.parse_expr($s)?)?
    };
}

/// Parse core term.
#[macro_export]
macro_rules! pct {
    ($p:ident, $d:ident, $e:ident, $s:expr) => {{
        let term = $e.infer(&$crate::pe!($p, $d, $s))?.0.ast;
        let val = $e.simplify(term)?;
        val
    }};
}

/// Parse expression and infer its type.
#[macro_export]
macro_rules! peit {
    ($p:ident, $d:ident, $e:ident, $s:expr) => {{
        let term = $e.infer(&$crate::pe!($p, $d, $s))?.1;
        let val = $e.simplify(term)?;
        val
    }};
}

/// Check type.
#[macro_export]
macro_rules! typeck {
    ($p:ident, $d:ident, $e:ident, $expr:expr, $ty:expr) => {{
        let ty = pct!($p, $d, $e, $ty);
        $d.cur_meta_id.push(Default::default());
        let expr = pe!($p, $d, $expr);
        $e.enter_def($e.sigma.len(), *$d.cur_meta_id.last().unwrap());
        $e.check(&expr, &ty)?;
        $e.exit_def();
        $e.meta_ctx.pop();
        $d.cur_meta_id.pop();
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
macro_rules! assert_term_eq {
    ($p:ident, $d:ident, $e:ident, $x:expr, $y:expr) => {
        assert_eq!($crate::pct!($p, $d, $e, $x), $crate::pct!($p, $d, $e, $y));
    };
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

// #[macro_export]
// macro_rules! pretty {
//     ($dst:expr, $state:expr, $($arg:tt)*) => {
//
//         $dst.write_fmt($crate::format_args!($($arg)*))
//     };
// }
