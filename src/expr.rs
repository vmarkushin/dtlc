use crate::expr::Type::Base;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};

type Sym = String;

type BExpr = Box<Expr>;
type BType = Box<Type>;
type Env = HashMap<Sym, Type>;

type TCError = String;
type Result<T> = std::result::Result<T, TCError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Base,
    Arrow(BType, BType),
}

#[derive(Clone, Debug)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum Expr {
    Var(Sym),
    App(BExpr, BExpr),
    Lam(Sym, BType, BExpr),
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Var(i) => f.write_str(i),
            Expr::App(ff, a) => {
                f.write_str(&format!("{} ", ff))?;
                match a.as_ref() {
                    app @ Expr::App(_, _) => f.write_str(&format!("({})", app)),
                    e => f.write_str(&format!("{}", e)),
                }
            }
            Expr::Lam(i, t, b) => f.write_str(&format!("(λ{}:{}. {})", i, t, b)),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Base => {
                write!(f, "B")
            }
            Type::Arrow(t0, t1) => {
                write!(f, "{}→{}", t0, t1)
            }
        }
    }
}

/// Checks and infers type of the given expression.
fn typeck(ctx: &mut Env, e: &Expr) -> Result<Type> {
    match e {
        // get type of a variable from the context
        Expr::Var(s) => ctx
            .get(s)
            .cloned()
            .ok_or_else(|| format!("Cannot find variable {}", s)),
        // type of a function should be arrow `α -> β`. Then, type of the argument should be `α`,
        // and, finally, type of the application will be `β`.
        Expr::App(f, a) => {
            let tf = typeck(ctx, f)?;
            match tf {
                Type::Arrow(at, rt) => {
                    let ta = typeck(ctx, a)?;
                    let string = format!("Argument type {} != {}", ta, at);
                    if ta != *at {
                        return Err(string);
                    }
                    return Ok(*rt);
                }
                _ => {
                    return Err(format!("'{}' is not a function", f));
                }
            }
        }
        // type of lambda argument (`α`) is always known by construction. If the body has type `β`,
        // then type of the lambda is `α -> β`.
        Expr::Lam(s, t, e) => {
            ctx.insert(s.clone(), *t.clone());
            let te = typeck(ctx, e)?;
            return Ok(Type::Arrow(t.clone(), box te));
        }
    }
}

/// Type-checks in an empty context.
fn typeck_empty(e: &Expr) -> Result<Type> {
    typeck(&mut Default::default(), e)
}

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
fn beta_eq(e1: BExpr, e2: BExpr) -> bool {
    alpha_eq(&nf(e1), &nf(e2))
}

pub fn app(f: impl Into<BExpr>, a: impl Into<BExpr>) -> BExpr {
    box Expr::App(f.into(), a.into())
}

pub fn lam(s: impl Into<String>, t: impl Into<BType>, e: impl Into<BExpr>) -> BExpr {
    box Expr::Lam(s.into(), t.into(), e.into())
}

pub fn var(s: impl Into<String>) -> BExpr {
    box Expr::Var(s.into())
}

pub fn arrow(t0: impl Into<BType>, t1: impl Into<BType>) -> Type {
    Type::Arrow(t0.into(), t1.into())
}

impl<T: Into<String>> From<T> for BExpr {
    fn from(s: T) -> Self {
        box Expr::Var(s.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nat() {
        use Type::*;

        fn nat_def(val: BExpr) -> BExpr {
            lam(
                "nat",
                Base,
                lam("s", arrow(Base, Base), lam("z", Base, val)),
            )
        }

        fn nat_data(n: u32) -> BExpr {
            let mut val = "z".into();
            for _ in 0..n {
                val = app("s", val);
            }
            val
        }

        fn church_nat(n: u32) -> BExpr {
            nat_def(nat_data(n))
        }

        let n = church_nat(11);
        assert_eq!(
            typeck(&mut Default::default(), &n).unwrap(),
            arrow(Base, arrow(arrow(Base, Base), arrow(Base, Base)))
        );

        fn plus(n: BExpr, m: BExpr) -> BExpr {
            nat_def(app(
                app(app(n, "nat"), "s"),
                app(app(app(m, "nat"), "s"), "z"),
            ))
        }

        assert!(beta_eq(plus(church_nat(5), church_nat(7)), church_nat(12)));

        fn mul(n: BExpr, m: BExpr) -> BExpr {
            nat_def(app(
                app(
                    app(n, "nat"),
                    app(app(plus(m.clone(), church_nat(0)), "nat"), "s"),
                ),
                nat_data(0),
            ))
        }

        assert!(beta_eq(mul(church_nat(5), church_nat(7)), church_nat(35)));
    }

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

    #[test]
    fn test_type_check() -> Result<()> {
        // lambda
        assert_eq!(typeck_empty(&lam("x", Base, "x"))?, arrow(Base, Base));

        // application
        assert_eq!(typeck_empty(&lam("x", Base, "x"))?, arrow(Base, Base));

        // var in context
        let mut ctx = HashMap::default();
        let arrow_t = arrow(Base, Base);
        ctx.insert("f".to_owned(), arrow_t.clone());
        assert_eq!(typeck(&mut ctx, &var("f"))?, arrow_t);

        Ok(())
    }

    #[test]
    fn test_type_check_fail() {
        assert_eq!(
            typeck_empty(&var("x")).unwrap_err(),
            "Cannot find variable x".to_owned()
        );

        let mut ctx = HashMap::default();
        ctx.insert("x".to_owned(), Base);
        assert_eq!(
            typeck(&mut ctx, &app("x", "x")).unwrap_err(),
            "'x' is not a function".to_owned()
        );
    }
}
