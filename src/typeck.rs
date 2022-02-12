use crate::expr::{Expr, Sym};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub type BType = Box<Type>;
pub type Env = HashMap<Sym, Type>;
pub type TCError = String;
pub type Result<T> = std::result::Result<T, TCError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Base(Sym),
    Arrow(BType, BType),
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Base(s) => {
                write!(f, "{s}")
            }
            Type::Arrow(t0, t1) => {
                if matches!(**t0, Self::Arrow(_, _)) {
                    write!(f, "({})→{}", t0, t1)
                } else {
                    write!(f, "{}→{}", t0, t1)
                }
            }
        }
    }
}

/// Checks and infers type of the given expression.
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
            let f_ty = typeck(ctx, f)?;
            match f_ty {
                Type::Arrow(from, to) => {
                    let a_ty = typeck(ctx, a)?;
                    let string = format!("Argument type {} != {}", a_ty, from);
                    if a_ty != *from {
                        return Err(string);
                    }
                    Ok(*to)
                }
                _ => {
                    return Err(format!("'{}' is not a function", f));
                }
            }
        }
        // type of lambda parameter (`α`) is always known by construction. If the body has type `β`,
        // then type of the lambda is `α -> β`.
        Expr::Lam(p, ty, b) => {
            let maybe_shadowed_var_ty = ctx.get(p).cloned();
            ctx.insert(p.clone(), *ty.clone());
            let b_ty = typeck(ctx, b)?;
            if let Some(shadowed_ty) = maybe_shadowed_var_ty {
                ctx.insert(p.clone(), shadowed_ty);
            } else {
                ctx.remove(p);
            }
            Ok(arrow(ty.clone(), b_ty))
        }
    }
}

/// Type-checks in an empty context.
fn typeck_empty(e: &Expr) -> Result<Type> {
    typeck(&mut Default::default(), e)
}

pub fn arrow(t0: impl Into<BType>, t1: impl Into<BType>) -> Type {
    Type::Arrow(t0.into(), t1.into())
}

pub fn base(s: impl Into<String>) -> Type {
    Type::Base(s.into())
}

impl<T: Into<String>> From<T> for BType {
    fn from(s: T) -> Self {
        box Type::Base(s.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::*;
    use crate::{e, ty};

    #[test]
    fn test_type_check() -> Result<()> {
        // lambda `\x:T. x : T→T`
        assert_eq!(typeck_empty(&e!(lam x:T. x))?, ty!(T->T));

        // application `y:T`, `(\x:T. x) y : T`
        let mut ctx = HashMap::default();
        ctx.insert("y".to_owned(), ty!(T));
        assert_eq!(typeck(&mut ctx, &e!((lam x:T. x) y))?, ty!(T));

        // var in context `f : T→T`
        let mut ctx = HashMap::default();
        let arrow_t = ty!(T->T);
        ctx.insert("f".to_owned(), arrow_t.clone());
        assert_eq!(typeck(&mut ctx, &e!(f))?, arrow_t);

        Ok(())
    }

    #[test]
    fn test_type_check_fail() {
        assert_eq!(&typeck_empty(&e!(x)).unwrap_err(), "Cannot find variable x");

        let mut ctx = HashMap::default();
        ctx.insert("x".to_owned(), ty!(T));
        assert_eq!(
            &typeck(&mut ctx, &e!(x x)).unwrap_err(),
            "'x' is not a function"
        );

        // application `y:A`, `(\x:B. x) y`
        let mut ctx = HashMap::default();
        ctx.insert("y".to_owned(), ty!(A));
        assert_eq!(
            &typeck(&mut ctx, &e!((lam x:B. x) y)).unwrap_err(),
            "Argument type A != B"
        );
    }
}
