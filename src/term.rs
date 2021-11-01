#![allow(clippy::ptr_arg)]

use crate::env::{Env, Enved};
use std::borrow::Cow;
use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};
use std::str::FromStr;

use crate::ensure;

pub type Sym = String;
pub type BTerm = Box<Term>;
pub type Type = Term;
pub type BType = Box<Type>;

#[derive(Debug, thiserror::Error)]
pub enum TCError {
    #[error("Unknown variable: `{0}`")]
    UnknownVar(String),

    #[error("Wrong type. Expected `{expected}`, but got `{got}`")]
    WrongType { expected: Type, got: Type },
    #[error("Wrong argument type. Expected `{expected}`, but got `{got}`")]
    WrongArgumentType { expected: Type, got: Type },

    #[error("Expected function, but got decl of type `{0}`")]
    ExpectedFunc(Type),
    #[error("Expected kind but got type `{0}`")]
    ExpectedKind(Type),
    #[error("Expected kind at return type, but got `{0}`")]
    ExpectedKindReturn(Type),
    #[error("Expected var, lam or pi, but got decl of type `{0}`")]
    ExpectedVarLamPi(Type),

    #[error("Kinds higher than [] are not supported")]
    KindTooHigh,
}

type Result<T, E = TCError> = std::result::Result<T, E>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(Sym),
    App(BTerm, BTerm),
    Lam(Sym, BType, BTerm),
    Pi(Sym, BType, BType),
    Universe(u32),
}

impl Term {
    pub(crate) fn ensure_well_formed_type(&self, env: &mut Cow<Env>) -> Result<Type> {
        let norm = Enved::from((self.clone(), &**env)).whnf_in();
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
            .fold(ret_ty, |acc, (s, t)| box Term::Pi(s, t, acc))
    }

    pub fn lam_many(params: Vec<(Sym, BType)>, body: BTerm) -> Self {
        *params
            .into_iter()
            .rev()
            .fold(body, |acc, (s, t)| box Term::Lam(s, t, acc))
    }
}

impl Term {
    pub fn is_kind(&self) -> bool {
        matches!(self, Term::Universe(_))
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(i) => f.write_str(i),
            Term::App(ff, a) => {
                write!(f, "{} ", ff)?;
                match a.as_ref() {
                    app @ Term::App(_, _) => write!(f, "({})", app),
                    e => write!(f, "{}", e),
                }
            }
            Term::Lam(i, t, b) => write!(f, "(λ {}:{}. {})", i, t, b),
            Term::Pi(i, k, t) => write!(f, "(Π {}:{}, {})", i, k, t),
            Term::Universe(k) => write!(f, "Type{}", k),
        }
    }
}

#[derive(Debug, thiserror::Error)]
#[error("Invalid identifier: `{0}`")]
pub struct ParseExprError(pub String);

impl FromStr for Term {
    type Err = ParseExprError;

    #[track_caller]
    fn from_str(s: &str) -> Result<Self, ParseExprError> {
        let s = s.to_owned();
        ensure!(
            s.chars().all(|c| char::is_alphanumeric(c) || c == '_'),
            ParseExprError(s),
        );
        Ok(Term::Var(s))
    }
}

impl FromStr for BTerm {
    type Err = ParseExprError;

    #[track_caller]
    fn from_str(s: &str) -> Result<Self, ParseExprError> {
        s.parse::<Term>().map(Box::new)
    }
}

impl Term {
    fn typeck_whnf(&self, r: &mut Cow<Env>) -> Result<Type> {
        Ok(self.typeck(r)?.whnf())
    }

    #[allow(unused)]
    pub(crate) fn typecheck(&self) -> Result<Type> {
        self.typeck(&mut Cow::Owned(Default::default()))
    }

    pub fn typeck(&self, r: &mut Cow<Env>) -> Result<Type> {
        match self {
            Term::Var(s) => r
                .get_type(s)
                .cloned()
                .ok_or_else(|| TCError::UnknownVar(s.clone())),
            Term::App(f, a) => match f.typeck_whnf(r)? {
                Term::Pi(x, box at, box rt) => {
                    let ta = a.typeck(r)?;
                    if !Enved::from((ta.clone(), &**r)).beta_eq(Enved::from((at.clone(), &**r))) {
                        return Err(TCError::WrongArgumentType {
                            expected: at,
                            got: ta,
                        });
                    }
                    Ok(rt.subst(&x, a))
                }
                other => Err(TCError::ExpectedFunc(other)),
            },
            Term::Lam(s, t, e) => {
                t.typeck(r)?;
                r.to_mut().add_type(s.clone(), *t.clone());
                let te = e.typeck(r)?;
                let lt = Type::Pi(s.clone(), t.clone(), box te);
                lt.typeck(r)?;
                Ok(lt)
            }
            Term::Pi(x, a, b) => {
                let s = a.typeck_whnf(r)?;
                if !s.is_kind() {
                    return Err(TCError::ExpectedKind(s));
                }
                r.to_mut().add_type(x.clone(), *a.clone());
                let t = b.typeck_whnf(r)?;
                if !t.is_kind() {
                    return Err(TCError::ExpectedKindReturn(t));
                }
                Ok(t)
            }
            Term::Universe(n) => Ok(Term::Universe(n + 1)),
        }
    }

    fn subst_var(self, s: &Sym, v: Sym) -> Term {
        self.subst(s, &Term::Var(v))
    }

    /// Replaces all *free* occurrences of `v` by `x` in `b`, i.e. `b[v:=x]`.
    pub(crate) fn subst(self, v: &Sym, x: &Term) -> Term {
        fn abstr(
            con: fn(Sym, BTerm, BTerm) -> Term,
            v: &Sym,
            x: &Term,
            i: &Sym,
            t: Type,
            e: BTerm,
        ) -> Term {
            let fvx = x.free_vars();
            if v == i {
                con(i.clone(), box t.subst(v, x), e.clone())
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
                con(i_new, box t.subst(v, x), box e_new.subst(v, x))
            } else {
                con(i.clone(), box t.subst(v, x), box e.subst(v, x))
            }
        }

        match self {
            Term::Var(i) => {
                if &i == v {
                    x.clone()
                } else {
                    Term::Var(i)
                }
            }
            Term::App(f, a) => Term::App(box f.subst(v, x), box a.subst(v, x)),
            Term::Lam(i, t, e) => abstr(Term::Lam, v, x, &i, *t, e),
            Term::Pi(i, t, e) => abstr(Term::Pi, v, x, &i, *t, e),
            k @ Term::Universe(_) => k,
        }
    }

    /// Compares expressions modulo α-conversions. That is, λx.x == λy.y.
    pub(crate) fn alpha_eq(&self, e2: &Term) -> bool {
        let e1 = self;
        let abstr = |t1: &Term, t2, e1: &Term, e2: Term, s1: &Sym, s2| {
            t1.alpha_eq(t2) && e1.alpha_eq(&e2.subst_var(s2, s1.clone()))
        };

        match (e1, e2) {
            (Term::Var(v1), Term::Var(v2)) => v1 == v2,
            (Term::App(f1, a1), Term::App(f2, a2)) => f1.alpha_eq(f2) && a1.alpha_eq(a2),
            (Term::Lam(s1, t1, e1), Term::Lam(s2, t2, e2)) => {
                abstr(t1, t2, e1, *e2.clone(), s1, s2)
            }
            (Term::Pi(s1, t1, e1), Term::Pi(s2, t2, e2)) => abstr(t1, t2, e1, *e2.clone(), s1, s2),
            (Term::Universe(k1), Term::Universe(k2)) => k1 == k2,
            _ => false,
        }
    }

    /// Evaluates the expression to Weak Head Normal Form.
    pub fn whnf(self) -> Term {
        Enved::from((self, &Default::default())).whnf_in()
    }

    fn free_vars(&self) -> HashSet<Sym> {
        let abstr = |i, t: &Term, e: &Term| -> HashSet<Sym> {
            let mut set = e.free_vars();
            set.remove(i);
            t.free_vars().union(&set).cloned().collect()
        };
        match self {
            Term::Var(s) => vec![s.clone()].into_iter().collect(),
            Term::App(f, a) => f.free_vars().union(&a.free_vars()).cloned().collect(),
            Term::Lam(i, t, e) => abstr(i, t, e),
            Term::Pi(i, k, t) => abstr(i, k, t),
            Term::Universe(_) => Default::default(),
        }
    }
}

impl<'a> Enved<'a, Term> {
    pub fn whnf_in(self) -> Term {
        self.normalize(false, false)
    }

    pub fn nf(self) -> Term {
        self.normalize(true, true)
    }

    fn spine(self, args: &[Term], is_deep: bool, is_strict: bool) -> Term {
        use Term::*;

        let Self { inner, env } = self;

        match (inner, args) {
            (App(box f, a), _) => {
                let mut args_new = args.to_owned();
                args_new.push(*a);
                Self::from((f, env)).spine(&args_new, is_deep, is_strict)
            }
            (Lam(s, box t, box e), []) => Lam(
                s,
                box Self::from((t, env)).normalize(is_deep, is_strict),
                box Self::from((e, env)).normalize_if_deep(is_deep, is_strict),
            ),
            (Lam(s, _, box e), [xs @ .., x]) => {
                let x = x.to_owned();
                let arg = Self::from((x, env)).normalize_if_strict(is_deep, is_strict);
                let ee = e.subst(&s, &arg);
                let term = Self::from((ee, env)).normalize_if_deep(is_deep, is_strict);
                Self::from((term, env)).spine(xs, is_deep, is_strict)
            }
            (Pi(s, box k, box t), _) => {
                // TODO: should we reverse args?
                let pi = Pi(
                    s,
                    box Self::from((k, env)).normalize(false, false),
                    box Self::from((t, env)).normalize(false, false),
                );
                Self::from((pi, env)).app(args)
            }
            (Var(v), args) => env
                .get_decl(&v)
                .cloned()
                .map(|e| Self::from((e, env)).spine(args, is_deep, is_strict))
                .unwrap_or_else(|| {
                    let mut xs = args.to_owned();
                    xs.reverse();
                    Self::from((Var(v), env)).app(&xs)
                }),
            (f, _) => {
                let mut xs = args.to_owned();
                xs.reverse();
                Self::from((f, env)).app(&xs)
            }
        }
    }

    fn normalize_if_deep(self, is_deep: bool, is_strict: bool) -> Term {
        if is_deep {
            self.normalize(is_deep, is_strict)
        } else {
            self.inner
        }
    }

    fn normalize_if_strict(self, is_deep: bool, is_strict: bool) -> Term {
        if is_strict {
            self.normalize(is_deep, is_strict)
        } else {
            self.inner
        }
    }

    fn app(self, args: &[Term]) -> Term {
        let Self { inner: f, env } = self;
        args.iter()
            .cloned()
            .map(|x| Self::from((x, env)).nf())
            .fold(f, |acc, e| Term::App(box acc, box e))
    }

    pub fn normalize(self, is_deep: bool, is_strict: bool) -> Term {
        self.spine(&[], is_deep, is_strict)
    }

    /// Compares expressions modulo β-conversions.
    fn beta_eq(self, e2: Self) -> bool {
        self.nf().alpha_eq(&e2.nf())
    }

    /// Example: `ensure_ret_type_eq(A -> B -> app (app Vec Nat) Nat), (lam a b : * => Vec a b)) == Ok
    pub fn ensure_ret_type_eq(
        self,
        ty_name: &Sym,
        ty_args: &Vec<(Option<Sym>, Type)>,
    ) -> Result<()> {
        let env = self.env;
        match self.whnf_in() {
            Term::Var(v) if v == *ty_name => Ok(()),
            Term::Pi(_, _, box b) | Term::Lam(_, _, box b) => {
                Self::from((b, env)).ensure_ret_type_eq(ty_name, ty_args)
            }
            e => Err(TCError::ExpectedVarLamPi(e)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: Option<Sym>,
    pub ty: Type,
}

impl Param {
    pub fn new(name: Option<Sym>, ty: Type) -> Self {
        Param { name, ty }
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = &self.name {
            write!(f, "({} : {})", name, self.ty)
        } else {
            write!(f, "{}", self.ty)
        }
    }
}

pub fn app(f: impl Into<BTerm>, a: impl Into<BTerm>) -> Term {
    Term::App(f.into(), a.into())
}

pub fn app_many(f: impl Into<BTerm>, aa: impl IntoIterator<Item = impl Into<BTerm>>) -> Term {
    aa.into_iter()
        .map(Into::into)
        .fold(*f.into(), |acc, e| Term::App(box acc, e))
}

#[allow(unused)]
pub fn lam(s: impl Into<String>, t: impl Into<BType>, e: impl Into<BTerm>) -> BTerm {
    box Term::Lam(s.into(), t.into(), e.into())
}

pub fn pi(s: impl Into<String>, t: impl Into<BType>, e: impl Into<BTerm>) -> Term {
    Term::Pi(s.into(), t.into(), e.into())
}

pub fn arrow(f: impl Into<BType>, t: impl Into<BTerm>) -> Term {
    pi("_", f, t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::EnvedMut;
    use crate::parser::Parser;
    use crate::t;
    use quickcheck::quickcheck;

    fn run_prog(s: impl AsRef<str>) -> Term {
        let prog = Parser::default().parse_prog(s.as_ref()).unwrap();
        EnvedMut::from((prog, &mut Default::default())).run()
    }

    #[track_caller]
    pub fn assert_beta_eq(e1: Term, e2: Term, env: &Env) {
        let e1 = Enved::from((e1, env));
        let e2 = Enved::from((e2, env));
        if !e1.clone().beta_eq(e2.clone()) {
            panic!(
                r#"assertion failed: `(left != right)`
left: `{:?}`,
right: `{:?}`"#,
                e1.nf(),
                e2.nf(),
            )
        }
    }

    #[test]
    #[ignore]
    fn test_id() {
        let res = run_prog(
            r#"
        data Nat
            | O : Nat
            | S : Nat -> Nat
        let id => lam (A : Type) (x : A) => x
        let zero => lam (s : Nat -> Nat) (z : Nat) => z
        let main => id Nat (zero S O)
        "#,
        );
        assert_eq!(res.to_string(), "O");
    }

    fn nat_def(val: Term) -> Term {
        t! {
            lam nat: * => lam s: (nat -> nat) => lam z: nat => @val
        }
    }

    fn mul(n: Term, m: Term) -> Term {
        let plus_f = plus(m, nat(0));
        nat_def(t! {
            @n nat (@plus_f nat s) {nat_data(0)}
        })
    }

    fn nat_data(n: u32) -> Term {
        let mut val = t!(z);
        for _ in 0..n {
            val = t!(s (@val));
        }
        val
    }

    /// Church's nats.
    fn nat(n: u32) -> Term {
        nat_def(nat_data(n))
    }

    fn plus(n: Term, m: Term) -> Term {
        nat_def(t! { @n nat s (@m nat s z) })
    }

    #[test]
    #[ignore]
    fn test_nat() {
        let n = nat(4);
        let env = Env::default();
        assert_beta_eq(
            n.typecheck().unwrap(),
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
        let a = Enved::from((mul(nat(x), nat(y)), &env));
        let b = Enved::from((nat(x * y), &env));
        a.beta_eq(b)
    }

    #[test]
    fn test_type_check() {
        let parser = Parser::default();
        assert!(parser.parse_term("x").unwrap().typecheck().is_err());
    }
}
