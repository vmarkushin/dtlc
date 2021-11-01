#![allow(clippy::ptr_arg)]

use crate::env::Env;
use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};
use std::str::FromStr;

use crate::ensure;

pub type Sym = String;
pub type BExpr = Box<Expr>;
pub type Type = Expr;
pub type BType = Box<Type>;

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
pub enum Expr {
    Var(Sym),
    App(BExpr, BExpr),
    Lam(Sym, BType, BExpr),
    Pi(Sym, BType, BType),
    Universe(u32),
}

impl Expr {
    pub(crate) fn ensure_well_formed_type(&self, env: Env) -> Result<Type> {
        let norm = self.clone().whnf_in(&env);
        let t = norm.typeck(env)?;
        ensure!(t.is_kind(), TCError::ExpectedKind(t));
        Ok(t)
    }

    pub fn pi(param: Sym, param_ty: impl Into<BType>, ret_ty: impl Into<BType>) -> Self {
        Self::Pi(param, param_ty.into(), ret_ty.into())
    }

    pub fn pi_many(params: Vec<(Sym, BType)>, ret_ty: BType) -> Self {
        *params
            .into_iter()
            .rev()
            .fold(ret_ty, |acc, (s, t)| box Expr::Pi(s, t, acc))
    }

    pub fn lam_many(params: Vec<(Sym, BType)>, body: BExpr) -> Self {
        *params
            .into_iter()
            .rev()
            .fold(body, |acc, (s, t)| box Expr::Lam(s, t, acc))
    }
}

impl Expr {
    pub fn is_kind(&self) -> bool {
        matches!(self, Expr::Universe(_))
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Var(i) => f.write_str(i),
            Expr::App(ff, a) => {
                write!(f, "{} ", ff)?;
                match a.as_ref() {
                    app @ Expr::App(_, _) => write!(f, "({})", app),
                    e => write!(f, "{}", e),
                }
            }
            Expr::Lam(i, t, b) => write!(f, "(λ {}:{}. {})", i, t, b),
            Expr::Pi(i, k, t) => write!(f, "(Π {}:{}, {})", i, k, t),
            Expr::Universe(k) => write!(f, "Type{}", k),
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
        match self {
            Expr::Var(s) => r
                .get_type(s)
                .cloned()
                .ok_or_else(|| TCError::UnknownVar(s.clone())),
            Expr::App(f, a) => {
                let tf = f.typeck_whnf(r.clone())?;
                match tf {
                    Expr::Pi(x, at, rt) => {
                        let ta = a.typeck(r.clone())?;
                        let at = *at;
                        if !(box ta.clone()).beta_eq(at.clone(), &r) {
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
            Expr::Universe(n) => Ok(Expr::Universe(n + 1)),
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
            k @ Expr::Universe(_) => k.clone(),
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
            (Expr::Universe(k1), Expr::Universe(k2)) => k1 == k2,
            _ => false,
        }
    }

    /// Evaluates the expression to Weak Head Normal Form.
    pub fn whnf(self) -> BExpr {
        self.whnf_in(&Default::default())
    }

    pub fn whnf_in(self, r: &Env) -> BExpr {
        self.normalize(r, false, false)
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
            Expr::Universe(_) => Default::default(),
        }
    }

    pub fn nf(self, env: &Env) -> BExpr {
        self.normalize(env, true, true)
    }

    pub fn normalize(self, env: &Env, is_deep: bool, is_strict: bool) -> BExpr {
        return spine(self, env, &[], is_deep, is_strict);

        fn spine(e: Expr, env: &Env, args: &[Expr], is_deep: bool, is_strict: bool) -> BExpr {
            match (e, args) {
                (Expr::App(f, a), _) => {
                    let mut args_new = args.to_owned();
                    args_new.push(*a);
                    spine(*f, env, &args_new, is_deep, is_strict)
                }
                (Expr::Lam(s, t, e), []) => box Expr::Lam(
                    s,
                    t.normalize(env, is_deep, is_strict),
                    if is_deep {
                        e.normalize(env, is_deep, is_strict)
                    } else {
                        e
                    },
                ),
                (Expr::Lam(s, _, e), [xs @ .., x]) => {
                    let arg = if is_strict {
                        *x.clone().normalize(env, is_deep, is_strict)
                    } else {
                        x.to_owned()
                    };
                    let ee = *e.subst(&s, &arg);
                    let expr = if is_deep {
                        *ee.normalize(env, is_deep, is_strict)
                    } else {
                        ee
                    };
                    spine(expr, env, xs, is_deep, is_strict)
                }
                (Expr::Pi(s, k, t), _) => {
                    // TODO: should we reverse args?
                    app(
                        Expr::Pi(
                            s,
                            k.normalize(env, false, false),
                            t.normalize(env, false, false),
                        ),
                        args,
                        env,
                    )
                }
                (Expr::Var(v), args) => env
                    .get_item(&v)
                    .map(|e| spine(e.clone(), env, args, is_deep, is_strict))
                    .unwrap_or_else(|| {
                        let mut xs = args.to_owned();
                        xs.reverse();
                        app(Expr::Var(v), &xs, env)
                    }),
                (f, _) => {
                    let mut xs = args.to_owned();
                    xs.reverse();
                    app(f, &xs, env)
                }
            }
        }

        fn app(f: Expr, args: &[Expr], env: &Env) -> Box<Expr> {
            args.to_owned()
                .into_iter()
                .map(|x| (box x).nf(env))
                .fold(box f, |acc, e| box Expr::App(acc, e))
        }
    }

    /// Compares expressions modulo β-conversions.
    fn beta_eq(self, e2: Expr, env: &Env) -> bool {
        self.nf(env).alpha_eq(&e2.nf(env))
    }

    /// Example: `ensure_ret_type_eq(A -> B -> app (app Vec Nat) Nat), (lam a b : * => Vec a b)) == Ok
    pub fn ensure_ret_type_eq(
        &self,
        ty_name: &Sym,
        ty_args: &Vec<(Option<Sym>, Type)>,
        env: &Env,
    ) -> Result<()> {
        let norm = *self.clone().whnf_in(env);
        match norm {
            Expr::Var(v) if v == *ty_name => Ok(()),
            Expr::Pi(_, _, b) | Expr::Lam(_, _, b) => b.ensure_ret_type_eq(ty_name, ty_args, env),
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
    use crate::t;
    use quickcheck::quickcheck;

    #[track_caller]
    pub fn assert_beta_eq(e1: BExpr, e2: BExpr, env: &Env) {
        let nf1 = e1.nf(env);
        let nf2 = e2.nf(env);
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
    #[ignore]
    fn test_id() {
        let mut env = Env::default();
        env.add_type("Nat".into(), Expr::Universe(0));
        let parser = Parser::default();
        let prog = parser
            .parse_prog(
                r#"
        data Nat
            | O : Nat
            | S : Nat -> Nat
        let id => lam (A : Type) (x : A) => x
        let zero => lam (s : Nat -> Nat) (z : Nat) => z
        let main => id Nat (zero S O)
        "#,
            )
            .unwrap();
        prog.iter().for_each(|x| println!("{}", x));
        assert_eq!(env.run(prog).to_string(), "O");
    }

    fn nat_def(val: BExpr) -> BExpr {
        t! {
            lam nat: * => lam s: (nat -> nat) => lam z: nat => @val
        }
    }

    fn mul(n: BExpr, m: BExpr) -> BExpr {
        let plus_f = plus(m, nat(0));
        nat_def(t! {
            @n nat (@plus_f nat s) {nat_data(0)}
        })
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
    #[ignore]
    fn test_nat() {
        let n = nat(4);
        let env = Env::default();
        assert_beta_eq(
            box n.typecheck().unwrap(),
            t!(forall t : *, (t -> t) -> (t -> t)),
            &env,
        );
        assert_beta_eq(
            n,
            t!(lam nat:* => (lam s:(forall _:nat, nat) => lam z:nat => s (s (s (s z))))),
            &env,
        );

        let e1 = plus(nat(5), nat(7));
        println!("{}", e1);
        assert_beta_eq(e1, nat(12), &env);

        assert_beta_eq(mul(nat(5), nat(7)), nat(35), &env);
    }

    #[ignore]
    #[quickcheck_macros::quickcheck]
    fn prop(x: u8, y: u8) -> bool {
        let env = Default::default();

        let x = x as u32 % 10;
        let y = y as u32 % 10;
        eprintln!("{} * {}", x, y);
        mul(nat(x), nat(y)).beta_eq(*nat(x * y), &env)
    }

    #[test]
    fn test_type_check() {
        let parser = Parser::default();
        assert!(parser.parse_expr("x").unwrap().typecheck().is_err());
    }
}
