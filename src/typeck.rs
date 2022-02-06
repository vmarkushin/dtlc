use crate::expr::{Expr, Sym};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub type BType = Box<Type>;
pub type Env = HashMap<Sym, Type>;
pub type TCError = String;
pub type Result<T> = std::result::Result<T, TCError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Base,
    Arrow(BType, BType),
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

pub fn arrow(t0: impl Into<BType>, t1: impl Into<BType>) -> Type {
    Type::Arrow(t0.into(), t1.into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::*;
    use crate::typeck::Type::Base;

    #[test]
    fn test_type_check() -> Result<()> {
        // lambda `\x:B. x : B→B`
        assert_eq!(typeck_empty(&lam("x", Base, "x"))?, arrow(Base, Base));

        // application `y:B`, `(\x:B. x) y : B`
        let mut ctx = HashMap::default();
        ctx.insert("y".to_owned(), Base);
        assert_eq!(typeck(&mut ctx, &app(lam("x", Base, "x"), "y"))?, Base);

        // var in context `f : B→B`
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
