use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};

type Sym = String;

type BExpr = Box<Expr>;

#[derive(Clone, Debug)]
pub enum Expr {
    Var(Sym),
    App(BExpr, BExpr),
    Lam(Sym, BExpr),
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
            Expr::Lam(i, b) => f.write_str(&format!("(λ{}. {})", i, b)),
        }
    }
}

fn subst_var(s: &Sym, v: Sym, e: &Expr) -> BExpr {
    subst(s, &Expr::Var(v), e)
}

/// Replaces all *free* occurrences of `v` by `x` in `b`, i.e. `b[v:=x]`.
pub(crate) fn subst(v: &Sym, x: &Expr, b: &Expr) -> BExpr {
    let res = box match b {
        e @ Expr::Var(i) => {
            if i == v {
                x.clone()
            } else {
                e.clone()
            }
        }
        Expr::App(f, a) => Expr::App(subst(v, x, f), subst(v, x, a)),
        Expr::Lam(i, e) => {
            let fvx = free_vars(x);
            if v == i {
                Expr::Lam(i.clone(), e.clone())
            } else if fvx.contains(i) {
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
                Expr::Lam(i_new, subst(v, x, &*e_new))
            } else {
                Expr::Lam(i.clone(), subst(v, x, &e))
            }
        }
    };
    res
}

/// Compares expressions modulo α-conversions. That is, λx.x == λy.y.
fn alpha_eq(e1: &Expr, e2: &Expr) -> bool {
    match (e1, e2) {
        (Expr::Var(v1), Expr::Var(v2)) => v1 == v2,
        (Expr::App(f1, a1), Expr::App(f2, a2)) => alpha_eq(f1, f2) && alpha_eq(a1, a2),
        (Expr::Lam(s1, e1), Expr::Lam(s2, e2)) => alpha_eq(e1, &*subst_var(s2, s1.clone(), &*e2)),
        _ => false,
    }
}

/// Acts like `Cons` in Haskell on `Vec`.
fn cons<T>(e: T, mut es: Vec<T>) -> Vec<T> {
    es.insert(0, e);
    es
}

/// Evaluates the expression to Weak Head Normal Form.
pub fn whnf(ee: BExpr) -> BExpr {
    return spine(ee, Vec::new());
    fn spine(e: BExpr, args: Vec<Expr>) -> BExpr {
        match *e {
            Expr::App(f, a) => spine(f, cons(*a, args)),
            Expr::Lam(s, e) if !args.is_empty() => {
                spine(subst(&s, &args[0], &e), args.clone()[1..].to_vec())
            }
            f => args
                .into_iter()
                .fold(box f, |acc, e| box Expr::App(acc, box e)),
        }
    }
}

fn free_vars(e: &Expr) -> HashSet<Sym> {
    match e {
        Expr::Var(s) => vec![s.clone()].into_iter().collect(),
        Expr::App(f, a) => free_vars(&*f).union(&free_vars(&*a)).cloned().collect(),
        Expr::Lam(i, e) => {
            let mut vs = free_vars(&*e);
            vs.remove(i);
            vs
        }
    }
}

fn nf(e: BExpr) -> BExpr {
    return spine(e, Vec::new());
    fn spine(e: BExpr, args: Vec<Expr>) -> BExpr {
        let res = match *e {
            Expr::App(f, a) => spine(f, cons(*a, args)),
            Expr::Lam(s, e) => {
                if args.is_empty() {
                    box Expr::Lam(s, nf(e))
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

pub fn lam(s: impl Into<String>, e: impl Into<BExpr>) -> BExpr {
    box Expr::Lam(s.into(), e.into())
}

impl<T: Into<String>> From<T> for BExpr {
    fn from(s: T) -> Self {
        box Expr::Var(s.into())
    }
}

#[test]
fn test_beta_eq() {
    fn app2(f: impl Into<BExpr>, x: impl Into<BExpr>, y: impl Into<BExpr>) -> BExpr {
        app(app(f, x), y)
    }
    let _zero = lam('s', lam('z', 'z'));
    let one = lam('s', lam('z', app('s', 'z')));
    let two = lam('s', lam('z', app('s', app('s', 'z'))));
    let three = lam('s', lam('z', app('s', app('s', app('s', 'z')))));
    let plus = lam(
        'm',
        lam('n', lam('s', lam('z', app2('m', 's', app2('n', 's', 'z'))))),
    );
    assert!(beta_eq(app2(plus, one, two), three));
}
