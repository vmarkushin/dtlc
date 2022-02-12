#![feature(box_syntax)]
#![allow(unused)]

mod expr;
mod macros;
mod norm;
mod typeck;

fn main() {
    println!("Run tests to see that it works!");
}

#[cfg(test)]
mod tests {
    use crate::expr::*;
    use crate::norm::beta_eq;
    use crate::typeck::Type::*;
    use crate::typeck::{arrow, forall, tvar, typeck, Type};
    use std::collections::HashMap;

    #[test]
    fn test_nat() {
        fn nat_def(val: Expr) -> Expr {
            tlam("a", lam("s", arrow("a", "a"), lam("z", "a", val)))
        }

        // ∀a. (a → a) → a → a
        fn nat_type() -> Type {
            forall("a", arrow(arrow("a", "a"), arrow("a", "a")))
        }

        // Λa. λs:a→a. λz:a. z
        fn zero() -> Expr {
            nat_def(var("z"))
        }

        // λn:Nat. Λa. λs:a→a. λz:a. s (n a s z)
        fn succ() -> Expr {
            lam(
                "n",
                nat_type(),
                nat_def(app("s", app(app(tapp("n", "a"), "s"), "z"))),
            )
        }

        fn church_nat(n: u32) -> Expr {
            let mut val = zero();
            for _ in 0..n {
                val = app(succ(), val);
            }
            val
        }

        let n = church_nat(11);
        assert_eq!(
            typeck(&mut Default::default(), &n).unwrap(),
            forall(
                "a",
                arrow(arrow(tvar("a"), tvar("a")), arrow(tvar("a"), tvar("a")))
            )
        );

        fn plus(n: Expr, m: Expr) -> Expr {
            nat_def(app(
                app(tapp(n, nat_type()), "s"),
                app(app(tapp(m, nat_type()), "s"), "z"),
            ))
        }

        assert!(beta_eq(plus(church_nat(5), church_nat(7)), church_nat(12)));

        fn mul(n: Expr, m: Expr) -> Expr {
            nat_def(app(
                app(
                    tapp(n, nat_type()),
                    app(tapp(plus(m.clone(), church_nat(0)), nat_type()), "s"),
                ),
                "z",
            ))
        }

        assert!(beta_eq(mul(church_nat(5), church_nat(7)), church_nat(35)));
    }
}
