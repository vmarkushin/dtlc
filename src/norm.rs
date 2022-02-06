use crate::expr::{BExpr, Expr, Sym};
use std::collections::HashSet;

fn subst_var(s: &Sym, v: Sym, e: &Expr) -> BExpr {
    subst(s, &Expr::Var(v), e)
}

/// Replaces all *free* occurrences of `v` by `x` in `b`, i.e. `b[v:=x]`.
pub(crate) fn subst(v: &Sym, x: &Expr, b: &Expr) -> BExpr {
    let res = box match b {
        // if the expression is variable `v`, replace it with `e` and we're done
        e @ Expr::Var(i) => {
            if i == v {
                x.clone()
            } else {
                e.clone()
            }
        }
        // substitute in both branches of application
        Expr::App(f, a) => Expr::App(subst(v, x, f), subst(v, x, a)),
        // the lambda case is more subtle...
        Expr::Lam(i, t, e) => {
            let fvx = free_vars(x);
            // if we encountered a lambda with the same argument name as `v`,
            // we can't substitute anything inside of it, because the new argument shadows
            // the previous one, the one we need to replace
            if v == i {
                Expr::Lam(i.clone(), t.clone(), e.clone())
            } else if fvx.contains(i) {
                // if our new expression's (`x`) free variables contain the encountered
                // argument name, it will bind the free variables, which can lead to wrong evaluation.
                // In this case, we just need to rename the argument and all the underlying
                // variables bound to it. (we just appending symbol `'` to the name until we don't
                // have any intersecting names)

                // also, we should consider other free free variables in the lambda body
                let vars = {
                    let mut set = fvx.clone();
                    set.extend(free_vars(e));
                    set
                };
                let mut i_new = i.clone();
                while vars.contains(&i_new) {
                    i_new.push('\'');
                }
                let e_new = subst_var(i, i_new.clone(), &e);
                Expr::Lam(i_new, t.clone(), subst(v, x, &*e_new))
            } else {
                Expr::Lam(i.clone(), t.clone(), subst(v, x, &e))
            }
        }
    };
    res
}

/// Compares expressions modulo α-conversions. For example, λx.x == λy.y.
fn alpha_eq(e1: &Expr, e2: &Expr) -> bool {
    match (e1, e2) {
        (Expr::Var(v1), Expr::Var(v2)) => v1 == v2,
        (Expr::App(f1, a1), Expr::App(f2, a2)) => alpha_eq(f1, f2) && alpha_eq(a1, a2),
        (Expr::Lam(s1, t1, e1), Expr::Lam(s2, t2, e2)) => {
            t1 == t2 && alpha_eq(e1, &*subst_var(s2, s1.clone(), &*e2))
        }
        _ => false,
    }
}

/// Acts like `Cons` in Haskell on `Vec`.
fn cons<T>(e: T, mut es: Vec<T>) -> Vec<T> {
    es.insert(0, e);
    es
}

/// Evaluates the expression to Weak Head Normal Form. Will perform substitution for top-level
/// applications, without reducing their arguments.
pub fn whnf(ee: BExpr) -> BExpr {
    return spine(ee, Vec::new());
    fn spine(e: BExpr, args: Vec<Expr>) -> BExpr {
        match *e {
            Expr::App(f, a) => {
                // collect application arguments
                spine(f, cons(*a, args))
            }
            Expr::Lam(s, _, e) if !args.is_empty() => {
                // substitute the last collected argument in the lambda, if had some (removing the abstraction)
                spine(subst(&s, &args[0], &e), args.clone()[1..].to_vec())
            }
            f => {
                // place all the unsubstituted arguments back (form applications from them)
                args.into_iter()
                    .fold(box f, |acc, e| box Expr::App(acc, box e))
            }
        }
    }
}

/// Returns a set of all free variables (i.e. variables, that are not bound with a corresponding
/// lambda abstraction) in the expression.
fn free_vars(e: &Expr) -> HashSet<Sym> {
    match e {
        Expr::Var(s) => vec![s.clone()].into_iter().collect(),
        Expr::App(f, a) => free_vars(&*f).union(&free_vars(&*a)).cloned().collect(),
        Expr::Lam(i, _, e) => {
            let mut vs = free_vars(&*e);
            vs.remove(i);
            vs
        }
    }
}

/// Reduces the given expression to normal form. Will perform all possible substitutions along
/// with reducing arguments of all applications.
fn nf(e: BExpr) -> BExpr {
    return spine(e, Vec::new());
    fn spine(e: BExpr, args: Vec<Expr>) -> BExpr {
        let res = match *e {
            Expr::App(f, a) => spine(f, cons(*a, args)),
            Expr::Lam(s, t, e) => {
                if args.is_empty() {
                    box Expr::Lam(s, t, nf(e))
                } else {
                    spine(subst(&s, &args[0], &e), args.clone()[1..].to_vec())
                }
            }
            f => args
                .into_iter()
                .map(|x| nf(box x))
                .fold(box f, |acc, e| box Expr::App(acc, e)),
        };
        res
    }
}

/// Compares expressions modulo β-conversions.
pub fn beta_eq(e1: BExpr, e2: BExpr) -> bool {
    alpha_eq(&nf(e1), &nf(e2))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::*;
    use crate::typeck::arrow;
    use crate::typeck::Type::Base;

    #[test]
    fn test_alpha_eq() {
        // \x:B. x α= \y:B. y
        assert!(alpha_eq(&*lam("x", Base, "x"), &*lam("y", Base, "y")));

        // x α/= y
        assert!(!alpha_eq(&*var("x"), &*var("y")));

        // \x:B. x α/= \y:B. z
        assert!(!alpha_eq(&*lam("x", Base, "x"), &*lam("y", Base, var("z"))));

        // \x:B. x α/= \x:B->B. x
        assert!(!alpha_eq(
            &*lam("x", Base, "x"),
            &*lam("x", arrow(Base, Base), "x")
        ));

        // (\x:B. x) z α= (\y:B->B. y) z
        assert!(alpha_eq(
            &*app(lam("x", Base, "x"), var("z")),
            &*app(lam("y", Base, "y"), var("z")),
        ));

        // (\x:B. x) z α/= (\y:B->B. y) w
        assert!(!alpha_eq(
            &*app(lam("x", Base, "x"), var("z")),
            &*app(lam("y", Base, "y"), var("w")),
        ));
    }

    #[test]
    fn test_normalization() {
        // x ~nf~> x
        let e = var("x");
        assert_eq!(nf(e.clone()), e);

        // \x:B. x ~nf~> \x:B. x
        let e = lam("x", Base, "x");
        assert_eq!(nf(e.clone()), e);

        // (\x:B. x) z ~nf~> z
        assert_eq!(nf(app(lam("x", Base, "x"), var("z"))), var("z"));

        // variable substitution with renaming (type isn't checked)
        // (\x:B. \y:B. x y) y ~nf~> \y':B. y y'
        assert_eq!(
            nf(app(lam("x", Base, lam("y", Base, app("x", "y"))), "y")),
            lam("y'", Base, app("y", "y'")),
        );

        // arguments should not reduce
        // (\x:B. \y:B. x y) ((\x:B. x) z) ~whnf~> \y:B. z y
        assert_eq!(
            nf(app(
                lam("x", Base, lam("y", Base, app("x", "y"))),
                app(lam("x", Base, "x"), "z")
            )),
            lam("y", Base, app("z", "y")),
        );

        // inner (deep) applications should reduce
        // (\x:B. \y:B. x ((\x:B. x) y)) z ~whnf~> \y:B. z y
        assert_eq!(
            nf(app(
                lam(
                    "x",
                    Base,
                    lam("y", Base, app("x", app(lam("x", Base, "x"), "y")))
                ),
                "z"
            )),
            lam("y", Base, app("z", "y")),
        );
    }

    #[test]
    fn test_whnf() {
        // x ~whnf~> x
        let e = var("x");
        assert_eq!(nf(e.clone()), e);

        // \x:B. x ~whnf~> \x:B. x
        let e = lam("x", Base, "x");
        assert_eq!(whnf(e.clone()), e);

        // (\x:B. x) z ~whnf~> z
        assert_eq!(whnf(app(lam("x", Base, "x"), var("z"))), var("z"));

        // variable substitution with renaming (type isn't checked)
        // (\x:B. \y:B. x y) y ~whnf~> \y':B. y y'
        assert_eq!(
            whnf(app(lam("x", Base, lam("y", Base, app("x", "y"))), "y")),
            lam("y'", Base, app("y", "y'")),
        );

        // arguments should *not* reduce
        // (\x:B. \y:B. x y) ((\x:B. x) z) ~whnf~> \y:B. z y
        let arg = app(lam("x", Base, "x"), "z");
        assert_eq!(
            whnf(app(
                lam("x", Base, lam("y", Base, app("x", "y"))),
                arg.clone()
            )),
            lam("y", Base, app(arg, "y")),
        );

        // inner (deep) applications should *not* reduce
        // (\x:B. \y:B. x ((\x:B. x) y)) z ~whnf~> \y:B. z y
        let app_term = app(lam("x", Base, "x"), "y");
        assert_eq!(
            whnf(app(
                lam("x", Base, lam("y", Base, app("x", app_term.clone()))),
                "z"
            )),
            lam("y", Base, app("z", app_term)),
        );
    }
}
