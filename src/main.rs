#![feature(box_syntax)]
#![allow(unused, clippy::boxed_local)]

mod expr;
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
    use crate::typeck::{arrow, typeck};

    #[test]
    fn test_nat() {
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
                "z",
            ))
        }

        assert!(beta_eq(mul(church_nat(5), church_nat(7)), church_nat(35)));
    }
}
