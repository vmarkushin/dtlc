use crate::expr::{gen_fresh_name, BExpr, Expr, Sym};
use crate::typeck::{
    alpha_eq as type_alpha_eq, free_vars as type_free_vars, subst as subst_type, tvar, BType, Type,
};
use std::collections::HashSet;

fn subst_var(s: &Sym, v: Sym, e: &Expr) -> BExpr {
    subst(s, &Expr::Var(v), e)
}

/// Replaces all *free* occurrences of `v` by `x` in `b`, i.e. `b[v:=x]`.
///
/// Note: expression should be type-checked before calling the function.
pub(crate) fn subst(v: &Sym, x: &Expr, b: &Expr) -> BExpr {
    box match b {
        // if the expression is variable `v`, replace it with `x` and we're done
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
            let mut fvs = free_vars(x);
            // if we encountered a lambda with the same argument name as `v`,
            // we can't substitute anything inside of it, because the new argument shadows
            // the previous one, the one we need to replace
            if v == i {
                Expr::Lam(i.clone(), t.clone(), e.clone())
            } else if fvs.contains(i) {
                // if our new expression's (`x`) free variables contain the encountered
                // argument name, it will bind the free variables, which can lead to wrong evaluation.
                // In this case, we just need to rename the argument and all the underlying
                // variables bound to it. (we just appending symbol `'` to the name until we don't
                // have any intersecting names)

                // also, we should consider other free free variables in the lambda body
                fvs.extend(free_vars(e));
                let i_new = gen_fresh_name(i, fvs);
                let e_new = subst_var(i, i_new.clone(), e);
                Expr::Lam(i_new, t.clone(), subst(v, x, &*e_new))
            } else {
                Expr::Lam(i.clone(), t.clone(), subst(v, x, e))
            }
        }
        // we don't substitute in types here, because the function is working on expression (term) level
        Expr::TApp(e, t) => Expr::TApp(subst(v, x, e), t.clone()),
        // since expression is type-checked, `s` won't clash with another variable
        Expr::TLam(s, e) => Expr::TLam(s.clone(), subst(v, x, e)),
    }
}

/// Replaces all *free* occurrences of type variable `v` by type `x` in expression `b`, i.e. `b[v:=x]`.
///
/// Note: expression should be type-checked before calling the function.
pub(crate) fn subst_type_in_expr(v: &Sym, x: &Type, b: &Expr) -> BExpr {
    box match b {
        // the expression is not _type_ variable, skip it
        e @ Expr::Var(_) => e.clone(),
        // substitute in both branches of application
        Expr::App(f, a) => Expr::App(subst_type_in_expr(v, x, f), subst_type_in_expr(v, x, a)),
        // and in both branches of lambda
        Expr::Lam(i, t, e) => {
            Expr::Lam(i.clone(), subst_type(v, x, t), subst_type_in_expr(v, x, e))
        }
        // and in both branches of type application
        Expr::TApp(e, t) => Expr::TApp(subst_type_in_expr(v, x, e), subst_type(v, x, t)),
        // do the same trick with renaming as in `subst`
        Expr::TLam(i, e) => {
            let mut fvs = type_free_vars(x);
            if v == i {
                Expr::TLam(i.clone(), e.clone())
            } else if fvs.contains(i) {
                fvs.extend(free_vars(e));
                let i_new = gen_fresh_name(i, fvs);
                let e_new = subst_type_in_expr(i, &Type::Var(i_new.clone()), e);
                Expr::TLam(i_new, subst_type_in_expr(v, x, &*e_new))
            } else {
                Expr::TLam(i.clone(), subst_type_in_expr(v, x, e))
            }
        }
    }
}

/// Compares expressions modulo α-conversions. For example, λx.x == λy.y.
///
/// Note: expression should be type-checked before calling the function.
fn alpha_eq(e1: &Expr, e2: &Expr) -> bool {
    match (e1, e2) {
        (Expr::Var(v1), Expr::Var(v2)) => v1 == v2,
        (Expr::App(f1, a1), Expr::App(f2, a2)) => alpha_eq(f1, f2) && alpha_eq(a1, a2),
        (Expr::Lam(s1, t1, e1), Expr::Lam(s2, t2, e2)) => {
            type_alpha_eq(t1, t2) && alpha_eq(e1, &*subst_var(s2, s1.clone(), &*e2))
        }
        (Expr::TApp(f1, a1), Expr::TApp(f2, a2)) => alpha_eq(f1, f2) && type_alpha_eq(a1, a2),
        (Expr::TLam(s1, e1), Expr::TLam(s2, e2)) => {
            alpha_eq(e1, &*subst_type_in_expr(s2, &Type::Var(s1.clone()), &*e2))
        }
        _ => false,
    }
}

/// Acts like `Cons` in Haskell on `Vec`.
fn cons<T>(e: T, mut es: Vec<T>) -> Vec<T> {
    es.insert(0, e);
    es
}

/// Represents applied arguments.
#[derive(Clone)]
enum Arg {
    Expr(BExpr),
    Type(BType),
}

impl Arg {
    fn into_app_expr(self, f: BExpr) -> Expr {
        match self {
            Arg::Expr(e) => Expr::App(f, e),
            Arg::Type(t) => Expr::TApp(f, t),
        }
    }

    fn as_expr(&self) -> &Expr {
        match self {
            Arg::Expr(e) => e,
            _ => panic!("unexpected argument kind. Expected expression, got type"),
        }
    }

    fn as_type(&self) -> &Type {
        match self {
            Arg::Type(t) => t,
            _ => panic!("unexpected argument kind. Expected type, got expression"),
        }
    }
}

impl From<BExpr> for Arg {
    fn from(e: BExpr) -> Self {
        Self::Expr(e)
    }
}

impl From<BType> for Arg {
    fn from(t: BType) -> Self {
        Self::Type(t)
    }
}

/// Evaluates the expression to Weak Head Normal Form. Will perform substitution for top-level
/// applications, without reducing their arguments.
///
/// Note: the expression should be type-checked before calling the function.
pub fn whnf(ee: Expr) -> BExpr {
    return spine(ee, Vec::new());
    fn spine(e: Expr, args: Vec<Arg>) -> BExpr {
        match e {
            Expr::App(f, a) => {
                // collect application arguments
                spine(*f, cons(a.into(), args))
            }
            Expr::Lam(s, _, e) if !args.is_empty() => {
                // substitute the last collected argument in the lambda, if had some (removing the abstraction)
                spine(*subst(&s, args[0].as_expr(), &e), args[1..].to_vec())
            }
            Expr::TApp(f, t) => {
                // collect type application arguments
                spine(*f, cons(t.into(), args))
            }
            Expr::TLam(i, b) if !args.is_empty() => {
                // same flow with type lambda as with basic lambda
                spine(
                    *subst_type_in_expr(&i, args[0].as_type(), &b),
                    args[1..].to_vec(),
                )
            }
            f => {
                // place all the unsubstituted arguments back (form applications from them)
                args.into_iter()
                    .fold(box f, |acc, a| box a.into_app_expr(acc))
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
        Expr::TLam(_, b) => free_vars(b),
        Expr::TApp(f, _) => free_vars(f),
    }
}

/// Reduces the given expression to normal form. Will perform all possible substitutions along
/// with reducing arguments of all applications.
///
/// Note: the expression should be type-checked before calling the function.
fn nf(e: Expr) -> BExpr {
    return spine(e, Vec::new());
    fn spine(e: Expr, args: Vec<Arg>) -> BExpr {
        let res = match e {
            Expr::App(f, a) => spine(*f, cons(a.into(), args)),
            Expr::Lam(s, t, e) => {
                if args.is_empty() {
                    box Expr::Lam(s, t, nf(*e))
                } else {
                    spine(*subst(&s, args[0].as_expr(), &e), args[1..].to_vec())
                }
            }
            Expr::TApp(f, t) => spine(*f, cons(t.into(), args)),
            Expr::TLam(i, b) => {
                if args.is_empty() {
                    box Expr::TLam(i, nf(*b))
                } else {
                    spine(
                        *subst_type_in_expr(&i, args[0].as_type(), &b),
                        args[1..].to_vec(),
                    )
                }
            }
            f => args
                .into_iter()
                .map(|x| match x {
                    Arg::Expr(x) => Arg::Expr(nf(*x)),
                    a => a,
                })
                .fold(box f, |acc, a| box a.into_app_expr(acc)),
        };
        res
    }
}

/// Compares expressions modulo β-conversions.
///
/// Note: expression should be type-checked before calling the function.
pub fn beta_eq(e1: Expr, e2: Expr) -> bool {
    alpha_eq(&nf(e1), &nf(e2))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::*;
    use crate::typeck::{arrow, forall, tvar};

    #[test]
    fn test_alpha_eq() {
        // \x:B. x α= \y:B. y
        assert!(alpha_eq(
            &lam("x", tvar("B"), "x"),
            &lam("y", tvar("B"), "y")
        ));
        // x α/= y
        assert!(!alpha_eq(&var("x"), &var("y")));

        // \x:B. x α/= \y:B. z
        assert!(!alpha_eq(
            &lam("x", tvar("B"), "x"),
            &lam("y", tvar("B"), var("z"))
        ));

        // \x:B. x α/= \x:B->B. x
        assert!(!alpha_eq(
            &lam("x", tvar("B"), "x"),
            &lam("x", arrow(tvar("B"), tvar("B")), "x")
        ));

        // (\x:B. x) z α= (\y:B->B. y) z
        assert!(alpha_eq(
            &app(lam("x", tvar("B"), "x"), var("z")),
            &app(lam("y", tvar("B"), "y"), var("z")),
        ));

        // (\x:B. x) z α/= (\y:B->B. y) w
        assert!(!alpha_eq(
            &app(lam("x", tvar("B"), "x"), var("z")),
            &app(lam("y", tvar("B"), "y"), var("w")),
        ));
    }

    #[test]
    fn test_normalization() {
        // x ~nf~> x
        let e = var("x");
        assert_eq!(*nf(e.clone()), e);

        // \x:B. x ~nf~> \x:B. x
        let e = lam("x", tvar("B"), "x");
        assert_eq!(*nf(e.clone()), e);

        // (\x:B. x) z ~nf~> z
        assert_eq!(*nf(app(lam("x", tvar("B"), "x"), var("z"))), var("z"));

        // variable substitution with renaming (type isn't checked)
        // (\x:B. \y:B. x y) y ~nf~> \y':B. y y'
        assert_eq!(
            *nf(app(
                lam("x", tvar("B"), lam("y", tvar("B"), app("x", "y"))),
                "y"
            )),
            lam("y'", tvar("B"), app("y", "y'")),
        );

        // arguments should not reduce
        // (\x:B. \y:B. x y) ((\x:B. x) z) ~whnf~> \y:B. z y
        assert_eq!(
            *nf(app(
                lam("x", tvar("B"), lam("y", tvar("B"), app("x", "y"))),
                app(lam("x", tvar("B"), "x"), "z")
            )),
            lam("y", tvar("B"), app("z", "y")),
        );

        // inner (deep) applications should reduce
        // (\x:B. \y:B. x ((\x:B. x) y)) z ~whnf~> \y:B. z y
        assert_eq!(
            *nf(app(
                lam(
                    "x",
                    tvar("B"),
                    lam("y", tvar("B"), app("x", app(lam("x", tvar("B"), "x"), "y")))
                ),
                "z"
            )),
            lam("y", tvar("B"), app("z", "y")),
        );

        // type functions should reduce
        // (Λ a. \x:a. x) z ~nf~> \x: z. x
        assert_eq!(
            *nf(tapp(tlam("a", lam("x", "a", "x")), "z")),
            lam("x", "z", "x"),
        );

        // inner (deep) type function applications should reduce
        // (\y:B. (Λ a. \x:a. x) z) ~whnf~> \y:B. \x: z. x
        assert_eq!(
            *nf(lam(
                "y",
                tvar("B"),
                tapp(tlam("a", lam("x", "a", "x")), "z")
            )),
            lam("y", tvar("B"), lam("x", "z", "x"),),
        );

        // type functions should reduce
        // (Λ a. \x:a. x) z ~nf~> \x: z. x
        assert_eq!(
            *nf(tapp(tlam("a", lam("x", "a", "x")), "z")),
            lam("x", "z", "x"),
        );

        // type function parameters renaming
        // (Λ a. Λb. \x:a. x) b ~nf~> Λb'. \x:b. x
        assert_eq!(
            *nf(tapp(tlam("a", tlam("b", lam("x", "a", "x"))), "b")),
            tlam("b'", lam("x", "b", "x")),
        );
    }

    #[test]
    fn test_whnf() {
        // x ~whnf~> x
        let e = var("x");
        assert_eq!(*whnf(e.clone()), e);

        // \x:B. x ~whnf~> \x:B. x
        let e = lam("x", tvar("B"), "x");
        assert_eq!(*whnf(e.clone()), e);

        // (\x:B. x) z ~whnf~> z
        assert_eq!(*whnf(app(lam("x", tvar("B"), "x"), var("z"))), var("z"));

        // variable substitution with renaming (type isn't checked)
        // (\x:B. \y:B. x y) y ~whnf~> \y':B. y y'
        assert_eq!(
            *whnf(app(
                lam("x", tvar("B"), lam("y", tvar("B"), app("x", "y"))),
                "y"
            )),
            lam("y'", tvar("B"), app("y", "y'")),
        );

        // arguments should *not* reduce
        // (\x:B. \y:B. x y) ((\x:B. x) z) ~whnf~> \y:B. z y
        let arg = app(lam("x", tvar("B"), "x"), "z");
        assert_eq!(
            *whnf(app(
                lam("x", tvar("B"), lam("y", tvar("B"), app("x", "y"))),
                arg.clone()
            )),
            lam("y", tvar("B"), app(arg, "y")),
        );

        // inner (deep) applications should *not* reduce
        // (\x:B. \y:B. x ((\x:B. x) y)) z ~whnf~> \y:B. z y
        let app_term = app(lam("x", tvar("B"), "x"), "y");
        assert_eq!(
            *whnf(app(
                lam(
                    "x",
                    tvar("B"),
                    lam("y", tvar("B"), app("x", app_term.clone()))
                ),
                "z"
            )),
            lam("y", tvar("B"), app("z", app_term)),
        );

        // type function applications should reduce
        // (Λ a. \x:a. x) z ~whnf~> \x: z. x
        assert_eq!(
            *whnf(tapp(tlam("a", lam("x", "a", "x")), "z")),
            lam("x", "z", "x"),
        );

        // inner (deep) type function applications should *not* reduce
        // \y:B. (Λ a. \x:a. x) z ~whnf~> \y:B. (Λ a. \x:a. x) z)
        assert_eq!(
            *whnf(lam(
                "y",
                tvar("B"),
                tapp(tlam("a", lam("x", "a", "x")), "z")
            )),
            lam("y", tvar("B"), tapp(tlam("a", lam("x", "a", "x")), "z")),
        );
    }
}
