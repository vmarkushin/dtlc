use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};

type Sym = String;
type BExpr = Box<Expr>;
type Type = Expr;
type BType = Box<Type>;
type Env = HashMap<Sym, Type>;

type TCError = String;
type Result<T> = std::result::Result<T, TCError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kinds {
    Star,
    Box,
}

impl Display for Kinds {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Kinds::Star => f.write_str("*"),
            Kinds::Box => f.write_str("[]"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expr {
    Var(Sym),
    App(BExpr, BExpr),
    Lam(Sym, BType, BExpr),
    Pi(Sym, BType, BType),
    Kind(Kinds),
}

impl From<Kinds> for Expr {
    fn from(k: Kinds) -> Self {
        Self::Kind(k)
    }
}

impl From<Kinds> for BExpr {
    fn from(k: Kinds) -> Self {
        box Expr::Kind(k)
    }
}

impl Expr {
    pub fn is_kind(&self) -> bool {
        match self {
            Expr::Kind(_) => true,
            _ => false,
        }
    }
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
            Expr::Pi(i, k, t) => f.write_str(&format!("(Π {}:{}, {})", i, k, t)),
            Expr::Kind(k) => f.write_str(&format!("{}", k)),
        }
    }
}

impl<T: Into<String>> From<T> for BExpr {
    fn from(s: T) -> Self {
        box Expr::Var(s.into())
    }
}

fn typeck_red(r: &mut Env, e: &Expr) -> Result<Type> {
    Ok(*whnf(box typeck(r, e)?))
}

fn typecheck(e: &Expr) -> Result<Type> {
    let mut r = Default::default();
    typeck(&mut r, e)
}

fn typeck(r: &mut Env, e: &Expr) -> Result<Type> {
    match e {
        Expr::Var(s) => r
            .get(s)
            .cloned()
            .ok_or_else(|| format!("Cannot find variable {}", s)),
        Expr::App(f, a) => {
            let tf = typeck_red(r, f)?;
            match tf {
                Expr::Pi(x, at, rt) => {
                    let ta = typeck(r, a)?;
                    let string = format!("Argument type {} != {}", ta, at);
                    if !beta_eq(box ta, at) {
                        return Err(string);
                    }
                    return Ok(*subst(&x, a, &rt));
                }
                _ => {
                    return Err(format!("'{}' is not a function", f));
                }
            }
        }
        Expr::Lam(s, t, e) => {
            let _ = typeck(r, t)?;
            r.insert(s.clone(), *t.clone());
            let te = typeck(r, e)?;
            let lt = Type::Pi(s.clone(), t.clone(), box te);
            typeck(r, &lt)?;
            return Ok(lt);
        }
        Expr::Pi(x, a, b) => {
            let s = typeck_red(r, a)?;
            r.insert(x.clone(), *a.clone());
            let t = typeck_red(r, b)?;
            if !s.is_kind() || !t.is_kind() {
                return Err("Bad abstraction".into());
            }
            return Ok(t);
        }
        Expr::Kind(k) => match k {
            Kinds::Star => Ok(Expr::Kind(Kinds::Box)),
            Kinds::Box => Err("Found a Box".into()),
        },
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
        Expr::Lam(i, t, e) => abstr(Expr::Lam, v, x, i, t, &e),
        Expr::Pi(i, t, e) => abstr(Expr::Pi, v, x, i, t, &e),
        k @ Expr::Kind(_) => k.clone(),
    };
    fn abstr(
        con: fn(Sym, BExpr, BExpr) -> Expr,
        v: &Sym,
        x: &Expr,
        i: &Sym,
        t: &BType,
        e: &BExpr,
    ) -> Expr {
        let fvx = free_vars(x);
        if v == i {
            con(i.clone(), subst(v, x, &*t), e.clone())
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
            let e_new = subst_var(i, i_new.clone(), e);
            con(i_new, subst(v, x, &*t), subst(v, x, &*e_new))
        } else {
            con(i.clone(), subst(v, x, &*t), subst(v, x, e))
        }
    }
    res
}

/// Compares expressions modulo α-conversions. That is, λx.x == λy.y.
fn alpha_eq(e1: &Expr, e2: &Expr) -> bool {
    let abstr = |t1, t2, e1, e2, s1: &Sym, s2| {
        alpha_eq(t1, t2) && alpha_eq(e1, &*subst_var(s2, s1.clone(), e2))
    };

    match (e1, e2) {
        (Expr::Var(v1), Expr::Var(v2)) => v1 == v2,
        (Expr::App(f1, a1), Expr::App(f2, a2)) => alpha_eq(f1, f2) && alpha_eq(a1, a2),
        (Expr::Lam(s1, t1, e1), Expr::Lam(s2, t2, e2)) => abstr(t1, t2, e1, e2, s1, s2),
        (Expr::Pi(s1, t1, e1), Expr::Pi(s2, t2, e2)) => abstr(t1, t2, e1, e2, s1, s2),
        (Expr::Kind(k1), Expr::Kind(k2)) => k1 == k2,
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
            Expr::Lam(s, _t, e) if !args.is_empty() => {
                spine(subst(&s, &args[0], &e), args.clone()[1..].to_vec())
            }
            pi @ Expr::Pi(..) => {
                return box pi;
            }
            f => args
                .into_iter()
                .fold(box f, |acc, e| box Expr::App(acc, box e)),
        }
    }
}

fn free_vars(e: &Expr) -> HashSet<Sym> {
    let abstr = |i, t, e| -> HashSet<Sym> {
        let mut set = free_vars(e);
        set.remove(i);
        free_vars(t).union(&set).cloned().collect()
    };
    match e {
        Expr::Var(s) => vec![s.clone()].into_iter().collect(),
        Expr::App(f, a) => free_vars(&*f).union(&free_vars(&*a)).cloned().collect(),
        Expr::Lam(i, t, e) => abstr(i, t, e),
        Expr::Pi(i, k, t) => abstr(i, k, t),
        Expr::Kind(_) => Default::default(),
    }
}

fn nf(e: BExpr) -> BExpr {
    return spine(e, Vec::new());
    fn spine(e: BExpr, args: Vec<Expr>) -> BExpr {
        let res = match *e {
            Expr::App(f, a) => spine(f, cons(*a, args)),
            Expr::Lam(s, t, e) => {
                if args.is_empty() {
                    box Expr::Lam(s, nf(t), nf(e))
                } else {
                    spine(subst(&s, &args[0], &e), args.clone()[1..].to_vec())
                }
            }
            Expr::Pi(s, k, t) => app(Expr::Pi(s, nf(k), nf(t)), args),
            f => app(f, args),
        };
        res
    }

    fn app(f: Expr, args: Vec<Expr>) -> Box<Expr> {
        args.into_iter()
            .map(|x| nf(box x))
            .fold(box f, |acc, e| box Expr::App(acc, e))
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

fn pi(s: impl Into<String>, t: impl Into<BType>, e: impl Into<BExpr>) -> BExpr {
    box Expr::Pi(s.into(), t.into(), e.into())
}

fn arrow(f: impl Into<BType>, t: impl Into<BExpr>) -> BExpr {
    pi("_", f, t)
}

#[test]
fn test_id() {
    use Kinds::*;
    let id = lam("a", Star, lam("x", "a", "x"));
    println!("{} : {}", id, typecheck(&id).unwrap());
    let zero = lam('s', arrow("Nat", "Nat"), lam('z', "Nat", 'z'));
    let z = nf(app(app(app(app(id, "Nat"), zero), ">0"), "0"));
    println!("{}", z);
}
