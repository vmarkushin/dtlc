use crate::expr::{BExpr, Expr, Sym};
use std::collections::HashSet;

fn subst_var(s: &Sym, v: Sym, e: &Expr) -> BExpr {
    subst(s, &Expr::Var(v), e)
}

/// Replaces all *free* occurrences of `v` (`var`) by `x` (`to`) in `e` (`in_expr`), i.e. `e[v:=x]`.
pub(crate) fn subst(var: &Sym, to: &Expr, in_expr: &Expr) -> BExpr {
    box match in_expr {
        // if the expression is variable `var`, replace it with `to` and we're done
        e @ Expr::Var(i) => {
            if i == var {
                to.clone()
            } else {
                e.clone()
            }
        }
        // substitute in both branches of application
        Expr::App(f, a) => Expr::App(subst(var, to, f), subst(var, to, a)),
        // the lambda case is more subtle...
        Expr::Lam(p, t, b) => {
            let mut fvs = free_vars(to);
            // if we encountered a lambda with the same parameter name as `var`,
            // we can't substitute anything inside of it, because the new argument shadows
            // the previous one, the one we need to replace
            if var == p {
                Expr::Lam(p.clone(), t.clone(), b.clone())
            } else if fvs.contains(p) {
                // if our new expression's (`x`) free variables contain the encountered
                // parameter name, it will bind the free variables, which can lead to wrong evaluation.
                // In this case, we just need to rename the parameter and all the underlying
                // variables bound to it. (we just appending symbol `'` to the name until we don't
                // have any intersecting names)

                // also, we should consider other free free variables in the lambda body
                fvs.extend(free_vars(b));
                let p_new = gen_fresh_name(p, fvs);
                let b_new = subst_var(p, p_new.clone(), b);
                Expr::Lam(p_new, t.clone(), subst(var, to, &*b_new))
            } else {
                Expr::Lam(p.clone(), t.clone(), subst(var, to, b))
            }
        }
    }
}

fn gen_fresh_name(i: &Sym, vars: HashSet<Sym>) -> String {
    let mut i_new = i.clone();
    while vars.contains(&i_new) {
        i_new.push('\'');
    }
    i_new
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
            Expr::Lam(p, _, b) if !args.is_empty() => {
                // substitute the last collected argument in the lambda, if had some (removing the abstraction)
                spine(subst(&p, &args[0], &b), args.clone()[1..].to_vec())
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

/// Reduces the given expression to normal form. Will perform all possible reductions along
/// with reducing arguments of all applications.
fn nf(e: BExpr) -> BExpr {
    return spine(e, Vec::new());
    fn spine(e: BExpr, args: Vec<Expr>) -> BExpr {
        match *e {
            Expr::App(f, a) => spine(f, cons(*a, args)),
            Expr::Lam(p, t, b) => {
                if args.is_empty() {
                    box Expr::Lam(p, t, nf(b))
                } else {
                    spine(subst(&p, &args[0], &b), args.clone()[1..].to_vec())
                }
            }
            f => args
                .into_iter()
                .map(|x| nf(box x))
                .fold(box f, |acc, e| box Expr::App(acc, e)),
        }
    }
}

/// Compares expressions modulo β-conversions.
pub fn beta_eq(e1: BExpr, e2: BExpr) -> bool {
    alpha_eq(&nf(e1), &nf(e2))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::e;
    use crate::expr::*;
    use crate::typeck::arrow;

    #[test]
    fn test_alpha_eq() {
        // \x:T. x α= \y:T. y
        assert!(alpha_eq(&e!(lam x:T. x), &e!(lam y:T. y)));
        // x α/= y
        assert!(!alpha_eq(&e!(x), &e!(y)));

        // \x:T. x α/= \y:T. z
        assert!(!alpha_eq(&e!(lam x:T. x), &e!(lam y:T. z)));

        // \x:T. x α/= \x:T->T. x
        assert!(!alpha_eq(&e!(lam x:T. x), &e!(lam x:(T->T). x)));

        // (\x:T. x) z α= (\y:T. y) z
        assert!(alpha_eq(&e!((lam x:T. x) z), &e!((lam y:T. y) z)));

        // (\x:T. x) z α/= (\y:T->T. y) w
        assert!(!alpha_eq(&e!((lam x:T. x) z), &e!((lam y:(T->T). y) w)));
    }

    #[test]
    fn test_normalization() {
        // x ~nf~> x
        let e = e!(x);
        assert_eq!(nf(e.clone()), e);

        // \x:T. x ~nf~> \x:T. x
        let e = e!(lam x:T. x);
        assert_eq!(nf(e.clone()), e);

        // (\x:T. x) z ~nf~> z
        assert_eq!(nf(e!((lam x:T. x) z)), e!(z));

        // variable substitution with renaming (type isn't checked)
        // (\x:T. \y:T. x y) y ~nf~> \y':T. y y'
        assert_eq!(
            nf(e!((lam x:T. lam y: T. x y) y)),
            lam("y'", "T", app("y", "y'")),
        );

        // arguments should reduce
        // (\x:T. \y:T. x y) ((\x:T. x) z) ~whnf~> \y:T. z y
        assert_eq!(
            nf(e!((lam x:T. lam y:T. x y) ((lam x:T. x) z))),
            e!(lam y:T. z y)
        );

        // inner (deep) applications should reduce
        // (\x:T. \y:T. x ((\x:T. x) y)) z ~whnf~> \y:T. z y
        assert_eq!(
            nf(e!((lam x:T. lam y:T. x ((lam x:T. x) y)) z)),
            e!(lam y:T. z y)
        );
    }

    #[test]
    fn test_whnf() {
        // x ~whnf~> x
        let e = e!(x);
        assert_eq!(whnf(e.clone()), e);

        // \x:T. x ~whnf~> \x:T. x
        let e = e!(lam x:T. x);
        assert_eq!(whnf(e.clone()), e);

        // (\x:T. x) z ~whnf~> z
        assert_eq!(whnf(e!((lam x:T. x) z)), e!(z));

        // variable substitution with renaming (type isn't checked)
        // (\x:T. \y:T. x y) y ~whnf~> \y':T. y y'
        assert_eq!(
            whnf(e!((lam x:T. lam y: T. x y) y)),
            lam("y'", "T", app("y", "y'")),
        );

        // arguments should *not* reduce
        // (\x:T. \y:T. x y) ((\x:T. x) z) ~whnf~> \y:T. z y
        let arg = e!((lam x:T. x) z);
        assert_eq!(
            whnf(app(e!(lam x:T. lam y:T. x y), arg.clone())),
            lam("y", "T", app(arg, "y")),
        );

        // inner (deep) applications should *not* reduce
        // (\x:T. \y:T. x ((\x:T. x) y)) z ~whnf~> \y:T. z y
        let app_term = e!((lam x:T. x) y);
        assert_eq!(
            whnf(app(
                lam("x", "T", lam("y", "T", app("x", app_term.clone()))),
                "z"
            )),
            lam("y", "T", app("z", app_term)),
        );
    }
}
