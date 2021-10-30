#![allow(clippy::ptr_arg)]

#[cfg(test)]
use quickcheck::quickcheck;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display, Formatter};
use std::str::FromStr;

use crate::ensure;
use crate::item::Item;

pub type Sym = String;
pub type BExpr = Box<Expr>;
pub type Type = Expr;
pub type BType = Box<Type>;

#[derive(Clone, Default, Debug)]
pub struct Env {
    types: HashMap<Sym, Type>,
    defs: HashMap<Sym, Expr>,
}

impl Env {
    pub(crate) fn get_item(&self, sym: &Sym) -> Option<&Expr> {
        self.defs.get(sym)
    }
}

impl Env {
    pub(crate) fn get_type(&self, p0: &Sym) -> Option<&Type> {
        self.types.get(p0)
    }
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }

    pub fn add_type(&mut self, sym: Sym, ty: Type) {
        self.types.insert(sym, ty);
    }

    pub fn add_item(&mut self, item: Item) {
        match item {
            Item::Fn { name, ty, body } => {
                if let Some(ty) = ty {
                    self.add_type(name.clone(), ty);
                }
                self.defs.insert(name, body);
            }
            Item::Data { name, cons } => {
                self.add_type(name, Kinds::Star.into());
                for (con_name, con) in cons {
                    self.add_type(con_name, con);
                }
            }
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum TCError {
    #[error("Unknown variable: `{0}`")]
    UnknownVar(String),

    #[error("Wrong type. Expected `{expected}`, but got `{got}`")]
    WrongType { expected: Type, got: Type },
    #[error("Wrong argument type. Expected `{expected}`, but got `{got}`")]
    WrongArgumentType { expected: Type, got: Type },

    #[error("Expected function, but got item of type `{0}`")]
    ExpectedFunc(Type),
    #[error("Expected kind but got type `{0}`")]
    ExpectedKind(Type),
    #[error("Expected kind at return type, but got `{0}`")]
    ExpectedKindReturn(Type),
    #[error("Expected var, lam or pi, but got item of type `{0}`")]
    ExpectedVarLamPi(Type),

    #[error("Kinds higher than [] are not supported")]
    KindTooHigh,
}

type Result<T, E = TCError> = std::result::Result<T, E>;

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

#[derive(Clone, Debug, PartialEq, Eq)]
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
        matches!(self, Expr::Kind(_))
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
            Expr::Lam(i, t, b) => f.write_str(&format!("(λ {}:{}. {})", i, t, b)),
            Expr::Pi(i, k, t) => f.write_str(&format!("(Π {}:{}, {})", i, k, t)),
            Expr::Kind(k) => f.write_str(&format!("{}", k)),
        }
    }
}

#[derive(Debug, thiserror::Error)]
#[error("Invalid identifier: `{0}`")]
pub struct ParseExprError(pub String);

impl FromStr for BExpr {
    type Err = ParseExprError;

    #[track_caller]
    fn from_str(s: &str) -> Result<Self, ParseExprError> {
        let s = s.to_owned();
        ensure!(
            s.chars().all(|c| char::is_alphanumeric(c) || c == '_'),
            ParseExprError(s),
        );
        Ok(box Expr::Var(s))
    }
}

impl Expr {
    fn typeck_whnf(&self, r: Env) -> Result<Type> {
        Ok(*(box self.typeck(r)?).whnf())
    }

    #[allow(unused)]
    pub(crate) fn typecheck(&self) -> Result<Type> {
        let r = Default::default();
        self.typeck(r)
    }

    pub fn typeck(&self, r: Env) -> Result<Type> {
        // dbg!(&self);
        match self {
            Expr::Var(s) => r
                .get_type(s)
                .cloned()
                .ok_or_else(|| TCError::UnknownVar(s.clone())),
            Expr::App(f, a) => {
                let tf = f.typeck_whnf(r.clone())?;
                match tf {
                    Expr::Pi(x, at, rt) => {
                        let ta = a.typeck(r)?;
                        let at = *at;
                        if !(box ta.clone()).beta_eq(at.clone()) {
                            return Err(TCError::WrongArgumentType {
                                expected: at,
                                got: ta,
                            });
                        }
                        Ok(*rt.subst(&x, a))
                    }
                    _ => Err(TCError::ExpectedFunc(tf)),
                }
            }
            Expr::Lam(s, t, e) => {
                let _ = t.typeck(r.clone())?;
                let mut r_new = r;
                r_new.add_type(s.clone(), *t.clone());
                let te = e.typeck(r_new.clone())?;
                let lt = Type::Pi(s.clone(), t.clone(), box te);
                lt.typeck(r_new)?;
                Ok(lt)
            }
            Expr::Pi(x, a, b) => {
                let s = a.typeck_whnf(r.clone())?;
                if !s.is_kind() {
                    return Err(TCError::ExpectedKind(s));
                }
                let mut r_new = r;
                r_new.add_type(x.clone(), *a.clone());
                let t = b.typeck_whnf(r_new)?;
                if !t.is_kind() {
                    return Err(TCError::ExpectedKindReturn(t));
                }
                Ok(t)
            }
            Expr::Kind(Kinds::Star) => Ok(Expr::Kind(Kinds::Box)),
            Expr::Kind(Kinds::Box) => Err(TCError::KindTooHigh),
        }
    }

    pub fn normalize_in(self, env: &Env) -> Expr {
        let norm = *(box self).nf();
        match norm {
            Expr::Var(v) => env
                .get_item(&v)
                .map(|e| e.clone().normalize_in(env))
                .unwrap_or(Expr::Var(v)),
            Expr::App(f, arg) => match *f {
                Expr::Var(v) => env
                    .get_item(&v)
                    .map(|e| Expr::App(box e.clone().normalize_in(env), arg.clone()))
                    .unwrap_or(Expr::App(box Expr::Var(v), arg)),
                _ => Expr::App(f, arg),
            },
            x => x,
        }
    }

    fn subst_var(self, s: &Sym, v: Sym) -> BExpr {
        self.subst(s, &Expr::Var(v))
    }

    /// Replaces all *free* occurrences of `v` by `x` in `b`, i.e. `b[v:=x]`.
    pub(crate) fn subst(self, v: &Sym, x: &Expr) -> BExpr {
        let res = box match self {
            Expr::Var(i) => {
                if &i == v {
                    x.clone()
                } else {
                    Expr::Var(i)
                }
            }
            Expr::App(f, a) => Expr::App(f.subst(v, x), a.subst(v, x)),
            Expr::Lam(i, t, e) => abstr(Expr::Lam, v, x, &i, *t, e),
            Expr::Pi(i, t, e) => abstr(Expr::Pi, v, x, &i, *t, e),
            k @ Expr::Kind(_) => k.clone(),
        };
        fn abstr(
            con: fn(Sym, BExpr, BExpr) -> Expr,
            v: &Sym,
            x: &Expr,
            i: &Sym,
            t: Type,
            e: BExpr,
        ) -> Expr {
            let fvx = x.free_vars();
            if v == i {
                con(i.clone(), t.subst(v, x), e.clone())
            } else if fvx.contains(i) {
                let vars = {
                    let mut set = fvx;
                    set.extend(e.free_vars());
                    set
                };
                let mut i_new = i.clone();
                while vars.contains(&i_new) {
                    i_new.push('\'');
                }
                let e_new = e.subst_var(i, i_new.clone());
                con(i_new, t.subst(v, x), e_new.subst(v, x))
            } else {
                con(i.clone(), t.subst(v, x), e.subst(v, x))
            }
        }
        res
    }

    /// Compares expressions modulo α-conversions. That is, λx.x == λy.y.
    pub(crate) fn alpha_eq(&self, e2: &Expr) -> bool {
        let e1 = self;
        let abstr = |t1: &Expr, t2, e1: &Expr, e2: Expr, s1: &Sym, s2| {
            t1.alpha_eq(t2) && e1.alpha_eq(&e2.subst_var(s2, s1.clone()))
        };

        match (e1, e2) {
            (Expr::Var(v1), Expr::Var(v2)) => v1 == v2,
            (Expr::App(f1, a1), Expr::App(f2, a2)) => f1.alpha_eq(f2) && a1.alpha_eq(a2),
            (Expr::Lam(s1, t1, e1), Expr::Lam(s2, t2, e2)) => {
                abstr(t1, t2, e1, *e2.clone(), s1, s2)
            }
            (Expr::Pi(s1, t1, e1), Expr::Pi(s2, t2, e2)) => abstr(t1, t2, e1, *e2.clone(), s1, s2),
            (Expr::Kind(k1), Expr::Kind(k2)) => k1 == k2,
            _ => false,
        }
    }

    /// Evaluates the expression to Weak Head Normal Form.
    pub fn whnf(self) -> BExpr {
        return spine(self, &[]);

        fn spine(e: Expr, args: &[Expr]) -> BExpr {
            match (e, args) {
                (Expr::App(f, a), _) => {
                    let mut args_new = args.to_owned();
                    args_new.push(*a);
                    spine(*f, &args_new)
                }
                (Expr::Lam(s, _t, e), [xs @ .., x]) => spine(*e.subst(&s, x), xs),
                (pi @ Expr::Pi(..), _) => box pi,
                (f, _) => args
                    .to_owned()
                    .into_iter()
                    .fold(box f, |acc, e| box Expr::App(acc, box e)),
            }
        }
    }

    fn free_vars(&self) -> HashSet<Sym> {
        let abstr = |i, t: &Expr, e: &Expr| -> HashSet<Sym> {
            let mut set = e.free_vars();
            set.remove(i);
            t.free_vars().union(&set).cloned().collect()
        };
        match self {
            Expr::Var(s) => vec![s.clone()].into_iter().collect(),
            Expr::App(f, a) => f.free_vars().union(&a.free_vars()).cloned().collect(),
            Expr::Lam(i, t, e) => abstr(i, t, e),
            Expr::Pi(i, k, t) => abstr(i, k, t),
            Expr::Kind(_) => Default::default(),
        }
    }

    pub fn nf(self) -> BExpr {
        return spine(self, &[]);

        fn spine(e: Expr, args: &[Expr]) -> BExpr {
            match (e, args) {
                // Nat O
                // Nat -> * -> Vector
                (Expr::App(f, a), _) => {
                    let mut args_new = args.to_owned();
                    args_new.push(*a);
                    spine(*f, &args_new)
                }
                (Expr::Lam(s, t, e), []) => box Expr::Lam(s, t.nf(), e.nf()),
                (Expr::Lam(s, _, e), [xs @ .., x]) => spine(*e.subst(&s, x), xs),
                (Expr::Pi(s, k, t), _) => {
                    // let mut xs = args.to_owned();
                    // xs.reverse();
                    app(Expr::Pi(s, k.nf(), t.nf()), args)
                }
                (f, _) => {
                    let mut xs = args.to_owned();
                    xs.reverse();
                    app(f, &xs)
                }
            }
        }

        fn app(f: Expr, args: &[Expr]) -> Box<Expr> {
            args.to_owned()
                .into_iter()
                .map(|x| (box x).nf())
                .fold(box f, |acc, e| box Expr::App(acc, e))
        }
    }

    /// Compares expressions modulo β-conversions.
    fn beta_eq(self, e2: Expr) -> bool {
        self.nf().alpha_eq(&e2.nf())
    }

    /*
    data Vect
     */
    /// Example: `ensure_ret_type_eq(A -> B -> app (app Vec Nat) Nat), (fun a b : * => Vec a b)) == Ok
    pub fn ensure_ret_type_eq(&self, ty_name: &Sym) -> Result<()> {
        let norm = *self.clone().whnf();
        match norm {
            Expr::Var(v) if v == *ty_name => Ok(()),
            Expr::Pi(_, _, b) | Expr::Lam(_, _, b) => b.ensure_ret_type_eq(ty_name),
            e => Err(TCError::ExpectedVarLamPi(e)),
        }
    }
}

#[allow(unused)]
pub fn app(f: impl Into<BExpr>, a: impl Into<BExpr>) -> BExpr {
    box Expr::App(f.into(), a.into())
}

pub fn app_many(f: impl Into<BExpr>, aa: impl IntoIterator<Item = impl Into<BExpr>>) -> BExpr {
    aa.into_iter()
        .map(Into::into)
        .fold(f.into(), |acc, e| box Expr::App(acc, e))
}

#[allow(unused)]
pub fn lam(s: impl Into<String>, t: impl Into<BType>, e: impl Into<BExpr>) -> BExpr {
    box Expr::Lam(s.into(), t.into(), e.into())
}

#[allow(unused)]
fn pi(s: impl Into<String>, t: impl Into<BType>, e: impl Into<BExpr>) -> BExpr {
    box Expr::Pi(s.into(), t.into(), e.into())
}

pub fn arrow(f: impl Into<BType>, t: impl Into<BExpr>) -> BExpr {
    pi("_", f, t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;
    use crate::{expr, t};

    #[track_caller]
    pub fn assert_beta_eq(e1: BExpr, e2: BExpr) {
        let nf1 = e1.nf();
        let nf2 = e2.nf();
        let eq = nf1.alpha_eq(&nf2);
        if !eq {
            panic!(
                r#"assertion failed: `(left != right)`
left: `{:?}`,
right: `{:?}`"#,
                nf1, nf2,
            )
        }
    }

    #[test]
    fn test_id() {
        use Kinds::*;
        let id = lam("a", Star, t! { fun x: a => x });
        assert_eq!(id.typecheck().unwrap(), *t! { forall a : * => x : a => a });
        let zero = t! { fun s: (Nat -> Nat) => fun z: Nat => z };
        let z = app_many(id, [t! { Nat }, zero, t! { s }, t! { "0" }]).nf();
        assert_eq!(z.to_string(), "0");
    }

    fn nat_def(val: BExpr) -> BExpr {
        t! {
            fun nat: * => fun s: (nat -> nat) => fun z: nat => @val
        }
    }

    fn mul(n: BExpr, m: BExpr) -> BExpr {
        let plus_f = plus(m, nat(0));
        dbg!(nat_def(t! {
            @n nat (@plus_f nat s) {nat_data(0)}
        }))
    }

    fn nat_data(n: u32) -> BExpr {
        let mut val = t!(z);
        for _ in 0..n {
            val = t!(s (@val));
        }
        val
    }

    /// Church's nats.
    fn nat(n: u32) -> BExpr {
        nat_def(nat_data(n))
    }

    fn plus(n: BExpr, m: BExpr) -> BExpr {
        nat_def(t! { @n nat s (@m nat s z) })
    }

    #[test]
    fn test_nat() {
        let n = nat(4);
        assert_beta_eq(
            box n.typecheck().unwrap(),
            t!(forall t : *, (t -> t) -> (t -> t)),
        );
        assert_beta_eq(
            n,
            t!(fun nat:* => (fun s:(forall _:nat, nat) => fun z:nat => s (s (s (s z))))),
        );

        assert_beta_eq(plus(nat(5), nat(7)), nat(12));

        assert_beta_eq(mul(nat(5), nat(7)), nat(35));
    }

    #[quickcheck_macros::quickcheck]
    fn prop(x: u8, y: u8) -> bool {
        let x = x as u32 % 10;
        let y = y as u32 % 10;
        eprintln!("{} * {}", x, y);
        mul(nat(x), nat(y)).beta_eq(*nat(x * y))
    }

    // #[test]
    // fn test_reduction() {
    //     let parser = Parser::new(grammar::ExprParser::new(), grammar::ItemParser::new());
    //     let mut env = expr::Env::new();
    //
    //     env.add_item(
    //         parser
    //             .parse_item("data Nat | O : Nat | S : Nat -> Nat")
    //             .unwrap(),
    //     );
    //
    //     env.add_item(
    //         parser
    //             .parse_item("data Vector | Vec : Nat -> * -> Vector")
    //             .unwrap(),
    //     );
    //     let replicate = parser
    //         .parse_expr("(forall a : * , forall x : Nat , Vec x a) Nat O")
    //         .unwrap();
    //     let e = app_many("Vec", ["O", "Nat"]);
    //     e.typeck(env.clone()).unwrap();
    //     let e = e.normalize_in(&env);
    //     println!("{}", e);
    //     println!("{:?}", e);
    // }
}
