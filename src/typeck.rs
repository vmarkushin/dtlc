use crate::expr::{gen_fresh_name, Expr, Sym};
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

pub type BType = Box<Type>;
pub type Env = HashMap<Sym, Type>;
pub type TCError = String;
pub type Result<T> = std::result::Result<T, TCError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Var(Sym),
    Arrow(BType, BType),
    Forall(Sym, BType),
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Var(s) => {
                write!(f, "{s}")
            }
            Type::Arrow(t0, t1) => match t0.as_ref() {
                t @ Type::Arrow(_, _) => write!(f, "({t})→{t1}"),
                t => write!(f, "{t}->{t1}"),
            },
            Type::Forall(s, t) => {
                write!(f, "(∀{}. {})", s, t)
            }
        }
    }
}

/// Returns a set of all free variables (i.e. variables, that are not bound with a corresponding
/// lambda abstraction) in the type.
pub(crate) fn free_vars(e: &Type) -> HashSet<Sym> {
    match e {
        Type::Var(s) => vec![s.clone()].into_iter().collect(),
        Type::Arrow(f, a) => free_vars(&*f).union(&free_vars(&*a)).cloned().collect(),
        Type::Forall(i, e) => {
            let mut vs = free_vars(&*e);
            vs.remove(i);
            vs
        }
    }
}

/// Replaces all *free* occurrences of type variable `v` by type `x` in type `b`, i.e. `b[v:=x]`.
pub(crate) fn subst(v: &Sym, x: &Type, b: &Type) -> BType {
    box match b {
        // if the expression is variable `v`, replace it with `e` and we're done
        e @ Type::Var(i) => {
            if i == v {
                x.clone()
            } else {
                e.clone()
            }
        }
        // substitute in both branches of the →
        Type::Arrow(f, a) => Type::Arrow(subst(v, x, f), subst(v, x, a)),
        // rename the variable to avoid name clash (see `norm::subst` for more info)
        Type::Forall(i, t) => {
            let mut fvs = free_vars(x);
            if v == i {
                Type::Forall(i.clone(), t.clone())
            } else if fvs.contains(i) {
                fvs.extend(free_vars(t));
                let i_new = gen_fresh_name(i, fvs);
                let t_new = subst(i, &Type::Var(i_new.clone()), t);
                Type::Forall(i_new, subst(v, x, &*t_new))
            } else {
                Type::Forall(i.clone(), subst(v, x, t))
            }
        }
    }
}

/// Checks and infers type of the given expression, returns its type and expression with refined
/// (reduced) types.
pub fn typeck(ctx: &mut Env, e: &Expr) -> Result<Type> {
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
                Type::Arrow(t0, t1) => {
                    let ta = typeck(ctx, a)?;
                    let string = format!("Argument type {} != {}", ta, t0);
                    if ta != *t0 {
                        return Err(string);
                    }
                    Ok(*t1)
                }
                _ => {
                    return Err(format!("'{}' is not a function", f));
                }
            }
        }
        // type of lambda argument (`α`) is always known by construction. If the body has type `β`,
        // then type of the lambda is `α -> β`.
        Expr::Lam(s, t, e) => {
            let mut ctx_new = ctx.clone();
            ctx_new.insert(s.clone(), *t.clone());
            let te = typeck(&mut ctx_new, e)?;
            Ok(Type::Arrow(t.clone(), box te))
        }
        Expr::TApp(f, ta) => {
            let tf = typeck(ctx, f)?;
            match tf {
                Type::Forall(s, t) => Ok(*subst(&s, ta, &*t)),
                _ => Err(format!("'{}' is not a type function", f)),
            }
        }
        Expr::TLam(s, e) => {
            // `s` should not occur in the context
            if ctx.contains_key(s) {
                return Err(format!("`{s}` is already defined"));
            }
            let te = typeck(ctx, e)?;
            Ok(Type::Forall(s.clone(), box te))
        }
    }
}

/// Type-checks in an empty context.
fn typeck_empty(e: &Expr) -> Result<Type> {
    typeck(&mut Default::default(), e)
}

/// Compares types modulo α-conversions. For example, Λx.x == Λy.y.
pub fn alpha_eq(e1: &Type, e2: &Type) -> bool {
    match (e1, e2) {
        (Type::Var(v1), Type::Var(v2)) => v1 == v2,
        (Type::Arrow(f1, a1), Type::Arrow(f2, a2)) => alpha_eq(f1, f2) && alpha_eq(a1, a2),
        (Type::Forall(s1, t1), Type::Forall(s2, t2)) => {
            alpha_eq(t1, &*subst(s2, &Type::Var(s1.clone()), &*t2))
        }
        _ => false,
    }
}

pub fn arrow(t0: impl Into<BType>, t1: impl Into<BType>) -> Type {
    Type::Arrow(t0.into(), t1.into())
}

pub fn forall(s: impl Into<String>, t: impl Into<BType>) -> Type {
    Type::Forall(s.into(), t.into())
}

pub fn tvar(s: impl Into<String>) -> Type {
    Type::Var(s.into())
}

impl<T: Into<String>> From<T> for BType {
    fn from(s: T) -> Self {
        box Type::Var(s.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::*;

    #[test]
    fn test_type_check() -> Result<()> {
        // lambda `\x:B. x : B→B`
        assert_eq!(
            typeck_empty(&lam("x", tvar("B"), "x"))?,
            arrow(tvar("B"), tvar("B"))
        );

        // application `y:B`, `(\x:B. x) y : B`
        let mut ctx = HashMap::default();
        ctx.insert("y".to_owned(), tvar("B"));
        assert_eq!(
            typeck(&mut ctx, &app(lam("x", tvar("B"), "x"), "y"))?,
            tvar("B")
        );

        // var in context `f : B→B`
        let mut ctx = HashMap::default();
        let arrow_t = arrow(tvar("B"), tvar("B"));
        ctx.insert("f".to_owned(), arrow_t.clone());
        assert_eq!(typeck(&mut ctx, &var("f"))?, arrow_t);

        // type function
        assert_eq!(
            typeck_empty(&tlam("a", lam("x", tvar("a"), "x")))?,
            forall("a", arrow(tvar("a"), tvar("a")))
        );

        // type function application
        assert_eq!(
            typeck_empty(&tapp(tlam("a", lam("x", tvar("a"), "x")), tvar("T")))?,
            arrow(tvar("T"), tvar("T"))
        );

        // type parameter renaming
        assert_eq!(
            typeck_empty(&tapp(
                tlam("a", tlam("b", lam("y", "b", lam("x", tvar("a"), "x")))),
                tvar("b")
            ))?,
            forall("b'", arrow(tvar("b'"), arrow(tvar("b"), tvar("b"))))
        );

        Ok(())
    }

    #[test]
    fn test_type_check_fail() {
        assert_eq!(
            &typeck_empty(&var("x")).unwrap_err(),
            "Cannot find variable x"
        );

        let mut ctx = HashMap::default();
        ctx.insert("x".to_owned(), tvar("B"));
        assert_eq!(
            &typeck(&mut ctx, &app("x", "x")).unwrap_err(),
            "'x' is not a function"
        );

        assert_eq!(
            &typeck_empty(&lam("a", tvar("B"), tlam("a", lam("x", tvar("a"), "x")))).unwrap_err(),
            "`a` is already defined"
        );

        assert_eq!(
            &typeck_empty(&tapp(
                lam("a", tvar("B"), lam("x", tvar("a"), "x")),
                tvar("T")
            ))
            .unwrap_err(),
            "'(λa:B. (λx:a. x))' is not a type function"
        );
    }
}
