use crate::expr::{gen_fresh_name, BExpr, Expr, Sym};
use crate::typeck::{
    alpha_eq as type_alpha_eq, free_vars as type_free_vars, subst as subst_type, tvar, BType, Type,
};
use std::collections::HashSet;

fn subst_var(s: &Sym, v: Sym, e: &Expr) -> BExpr {
    subst(s, &Expr::Var(v), e)
}

/// Replaces all *free* occurrences of `v` (`var`) by `x` (`to`) in `e` (`in_expr`), i.e. `e[v:=x]`.
///
/// Note: expression should be type-checked before calling the function.
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
                // if our new expression's (`to`) free variables contain the encountered
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
        // we don't substitute in types here, because the function is working on expression (term) level
        Expr::TApp(e, t) => Expr::TApp(subst(var, to, e), t.clone()),
        // since expression is type-checked, `s` won't clash with another variable
        Expr::TLam(s, e) => Expr::TLam(s.clone(), subst(var, to, e)),
    }
}

/// Replaces all *free* occurrences of type variable `v` by type `x` in expression `b`, i.e. `b[v:=x]`.
///
/// Note: expression should be type-checked before calling the function.
pub(crate) fn subst_type_in_expr(var: &Sym, to: &Type, in_expr: &Expr) -> BExpr {
    box match in_expr {
        // the expression is not _type_ variable, skip it
        e @ Expr::Var(_) => e.clone(),
        // substitute in both branches of application
        Expr::App(f, a) => Expr::App(
            subst_type_in_expr(var, to, f),
            subst_type_in_expr(var, to, a),
        ),
        // and in both branches of lambda
        Expr::Lam(i, t, e) => Expr::Lam(
            i.clone(),
            subst_type(var, to, t),
            subst_type_in_expr(var, to, e),
        ),
        // and in both branches of type application
        Expr::TApp(e, t) => Expr::TApp(subst_type_in_expr(var, to, e), subst_type(var, to, t)),
        // do the same trick with renaming as in `subst`
        Expr::TLam(p, b) => {
            let mut fvs = type_free_vars(to);
            if var == p {
                Expr::TLam(p.clone(), b.clone())
            } else if fvs.contains(p) {
                fvs.extend(free_vars(b));
                let p_new = gen_fresh_name(p, fvs);
                let b_new = subst_type_in_expr(p, &Type::Var(p_new.clone()), b);
                Expr::TLam(p_new, subst_type_in_expr(var, to, &*b_new))
            } else {
                Expr::TLam(p.clone(), subst_type_in_expr(var, to, b))
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
            Expr::TLam(p, b) if !args.is_empty() => {
                // same flow with type lambda as with basic lambda
                spine(
                    *subst_type_in_expr(&p, args[0].as_type(), &b),
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
            Expr::Lam(p, t, e) => {
                if args.is_empty() {
                    box Expr::Lam(p, t, nf(*e))
                } else {
                    spine(*subst(&p, args[0].as_expr(), &e), args[1..].to_vec())
                }
            }
            Expr::TApp(f, t) => spine(*f, cons(t.into(), args)),
            Expr::TLam(p, b) => {
                if args.is_empty() {
                    box Expr::TLam(p, nf(*b))
                } else {
                    spine(
                        *subst_type_in_expr(&p, args[0].as_type(), &b),
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
    use crate::e;
    use crate::expr::*;
    use crate::typeck::{arrow, forall, tvar};

    #[test]
    fn test_alpha_eq() {
        // \x:B. x α= \y:B. y
        assert!(alpha_eq(&e!(lam x:B. x), &e!(lam y:B. y)));
        // x α/= y
        assert!(!alpha_eq(&e!(x), &e!(y)));

        // \x:B. x α/= \y:B. z
        assert!(!alpha_eq(&e!(lam x:B. x), &e!(lam y:B. z)));

        // \x:B. x α/= \x:B->B. x
        assert!(!alpha_eq(&e!(lam x:B. x), &e!(lam x:(B->B). x)));

        // (\x:B. x) z α= (\y:B. y) z
        assert!(alpha_eq(&e!((lam x:B. x) z), &e!((lam y:B. y) z)));

        // (\x:B. x) z α/= (\y:B->B. y) w
        assert!(!alpha_eq(&e!((lam x:B. x) z), &e!((lam y:(B->B). y) w)));
    }

    #[test]
    fn test_normalization() {
        // x ~nf~> x
        let e = e!(x);
        assert_eq!(*nf(e.clone()), e);

        // \x:B. x ~nf~> \x:B. x
        let e = e!(lam x:B. x);
        assert_eq!(*nf(e.clone()), e);

        // (\x:B. x) z ~nf~> z
        assert_eq!(*nf(e!((lam x:B. x) z)), e!(z));

        // variable substitution with renaming (type isn't checked)
        // (\x:B. \y:B. x y) y ~nf~> \y':B. y y'
        assert_eq!(
            *nf(e!((lam x:B. lam y: B. x y) y)),
            lam("y'", tvar("B"), app("y", "y'")),
        );

        // arguments should not reduce
        // (\x:B. \y:B. x y) ((\x:B. x) z) ~whnf~> \y:B. z y
        assert_eq!(
            *nf(e!((lam x:B. lam y:B. x y) ((lam x:B. x) z))),
            e!(lam y:B. z y)
        );

        // inner (deep) applications should reduce
        // (\x:B. \y:B. x ((\x:B. x) y)) z ~whnf~> \y:B. z y
        assert_eq!(
            *nf(e!((lam x:B. lam y:B. x ((lam x:B. x) y)) z)),
            e!(lam y:B. z y)
        );

        // type functions should reduce
        // (Λ a. \x:a. x) z ~nf~> \x: z. x
        assert_eq!(*nf(e!((lam a. lam x:a. x)[z])), e!(lam x:z. x));

        // inner (deep) type function applications should reduce
        // (\y:B. (Λ a. \x:a. x) z) ~whnf~> \y:B. \x: z. x
        assert_eq!(
            *nf(e!(lam y:B. (lam a. lam x:a. x)[z])),
            e!(lam y:B. lam x:z. x)
        );

        // type functions should reduce
        // (Λ a. \x:a. x) z ~nf~> \x: z. x
        assert_eq!(*nf(e!((lam a. lam x:a. x)[z])), e!(lam x:z. x));

        // type function parameters renaming
        // (Λ a. Λb. \x:a. x) b ~nf~> Λb'. \x:b. x
        assert_eq!(
            *nf(e!((lam a. lam b. lam x:a. x)[b])),
            tlam("b'", lam("x", "b", "x")),
        );
    }

    #[test]
    fn test_whnf() {
        // x ~whnf~> x
        let e = e!(x);
        assert_eq!(*whnf(e.clone()), e);

        // \x:B. x ~whnf~> \x:B. x
        let e = e!(lam x:B. x);
        assert_eq!(*whnf(e.clone()), e);

        // (\x:B. x) z ~whnf~> z
        assert_eq!(*whnf(e!((lam x:B. x) z)), e!(z));

        // variable substitution with renaming (type isn't checked)
        // (\x:B. \y:B. x y) y ~whnf~> \y':B. y y'
        assert_eq!(
            *whnf(e!((lam x:B. lam y: B. x y) y)),
            lam("y'", tvar("B"), app("y", "y'")),
        );

        // arguments should *not* reduce
        // (\x:B. \y:B. x y) ((\x:B. x) z) ~whnf~> \y:B. z y
        let arg = e!((lam x:B. x) z);
        assert_eq!(
            *whnf(app(e!(lam x:B. lam y:B. x y), arg.clone())),
            lam("y", tvar("B"), app(arg, "y")),
        );

        // inner (deep) applications should *not* reduce
        // (\x:B. \y:B. x ((\x:B. x) y)) z ~whnf~> \y:B. z y
        let app_term = e!((lam x:B. x) y);
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
        assert_eq!(*whnf(e!((lam a. lam x:a. x)[z])), e!(lam x:z. x));

        // inner (deep) type function applications should *not* reduce
        // \y:B. (Λ a. \x:a. x) z ~whnf~> \y:B. (Λ a. \x:a. x) z)
        let e = e!(lam y:B. (lam a. lam x:a. x)[z]);
        assert_eq!(*whnf(e.clone()), e);
    }
}
