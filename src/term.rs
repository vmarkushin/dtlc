#![allow(clippy::ptr_arg)]

use crate::env::{Env, Enved};
use std::borrow::Cow;
use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};
use std::marker::PhantomData;
use std::str::FromStr;

use derive_more::{Add, Deref, DerefMut, Display, From};

use crate::ensure;

pub type Sym = String;
pub type BTerm = Box<Term>;
pub type Type = Term;
pub type BType = Box<Type>;

#[derive(Debug, thiserror::Error)]
pub enum TCError {
    #[error("Unknown variable: `{0}`")]
    UnknownVar(Var),

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

#[derive(Deref, DerefMut, Clone, Debug, PartialEq, Eq)]
pub struct ReducesTo<T> {
    #[deref]
    #[deref_mut]
    term: Term,
    _t: PhantomData<T>,
}

impl<T> ReducesTo<T> {
    fn into_inner(self) -> Term {
        self.term
    }
}

impl<T> ReducesTo<T> {
    pub fn unchecked(term: impl Into<Term>) -> Self {
        Self {
            term: term.into(),
            _t: PhantomData,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Display, Deref, DerefMut, From)]
pub struct Var(pub Sym);

impl From<&str> for Var {
    fn from(v: &str) -> Self {
        Self(v.to_owned())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct App {
    pub f: Box<ReducesTo<Lam>>,
    pub arg: BTerm,
}

impl App {
    pub fn new(f: impl Into<Term>, arg: impl Into<Term>) -> Self {
        let f = box ReducesTo::unchecked(f.into());
        let arg = box arg.into();
        Self { f, arg }
    }

    pub fn new_many(f: impl Into<Term>, args: impl IntoIterator<Item = impl Into<Term>>) -> Term {
        args.into_iter()
            .map(Into::into)
            .fold(f.into(), |f, arg| App::new(f, arg).into())
    }

    pub fn alpha_eq(&self, other: &Self) -> bool {
        self.f.alpha_eq(&*other.f) && self.arg.alpha_eq(&*other.arg)
    }

    pub fn free_vars(&self) -> HashSet<Var> {
        let Self { box f, box arg } = self;
        f.free_vars().into_iter().chain(arg.free_vars()).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lam {
    pub arg_name: Var,
    pub arg_ty: BType,
    pub body: BTerm,
}

impl Lam {
    pub fn new(arg_name: Var, arg_ty: BType, body: BTerm) -> Self {
        Self {
            arg_name,
            arg_ty,
            body,
        }
    }

    pub fn new_many(
        term: Term,
        params: impl Sized + DoubleEndedIterator<Item = (Var, Type)>,
    ) -> Term {
        params.into_iter().rev().fold(term, |acc, (arg, arg_ty)| {
            Self::new(arg, box arg_ty, box acc).into()
        })
    }

    pub fn alpha_eq(&self, other: &Self) -> bool {
        let Self {
            arg_name: s1,
            arg_ty: t1,
            body: e1,
        } = self;
        let Self {
            arg_name: s2,
            arg_ty: t2,
            body: e2,
        } = other;
        t1.alpha_eq(t2) && e1.alpha_eq(&e2.clone().subst_var(s2, s1.clone()))
    }

    pub fn free_vars(&self) -> HashSet<Var> {
        let Self {
            arg_name,
            arg_ty,
            body,
        } = self;
        let mut set = body.free_vars();
        set.remove(arg_name);
        arg_ty.free_vars().into_iter().chain(set).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pi {
    pub argty_name: Var,
    pub argty_ty: BType,
    pub ty: BTerm,
}

impl Pi {
    pub fn new(argty_name: Var, argty_ty: BType, ty: BTerm) -> Self {
        Self {
            argty_name,
            argty_ty,
            ty,
        }
    }

    pub fn new_many(
        term: Term,
        params: impl Sized + DoubleEndedIterator<Item = (Var, Type)>,
    ) -> Term {
        params
            .into_iter()
            .rev()
            .fold(term, |acc, (argty_name, argty_ty)| {
                Self::new(argty_name, box argty_ty, box acc).into()
            })
    }

    pub fn arrow(argty_ty: impl Into<Type>, ty: impl Into<Type>) -> Self {
        Self::new(Var("_".to_owned()), box argty_ty.into(), box ty.into())
    }

    pub fn alpha_eq(&self, other: &Self) -> bool {
        let Self {
            argty_name: s1,
            argty_ty: t1,
            ty: e1,
        } = self;
        let Self {
            argty_name: s2,
            argty_ty: t2,
            ty: e2,
        } = other;
        t1.alpha_eq(t2) && e1.alpha_eq(&e2.clone().subst_var(s2, s1.clone()))
    }

    pub fn free_vars(&self) -> HashSet<Var> {
        let Self {
            argty_name,
            argty_ty,
            ty,
        } = self;
        let mut set = ty.free_vars();
        set.remove(argty_name);
        argty_ty.free_vars().into_iter().chain(set).collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Display, Default, From, Add)]
pub struct Universe(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, From)]
pub enum Term {
    Variable(Var),

    Application(App),
    Lambda(Lam),

    Pi(Pi),
    Universe(Universe),
}

impl Term {
    pub(crate) fn ensure_well_formed_type(&self, env: &mut Cow<Env>) -> Result<Type> {
        let norm = Enved::from((self.clone(), &**env)).whnf_in();
        let t = norm.typeck(env)?;
        ensure!(t.is_kind(), TCError::ExpectedKind(t));
        Ok(t)
    }

    pub fn is_kind(&self) -> bool {
        matches!(self, Term::Universe(_))
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Variable(Var(i)) => f.write_str(i),
            Term::Application(App { f: ff, arg }) => {
                write!(f, "{} ", &***ff)?;
                match arg.as_ref() {
                    app @ Term::Application(_) => write!(f, "({})", app),
                    e => write!(f, "{}", e),
                }
            }
            Term::Lambda(Lam {
                arg_name,
                arg_ty,
                body,
            }) => write!(f, "(λ {}:{}. {})", arg_name, arg_ty, body),
            Term::Pi(Pi {
                argty_name,
                argty_ty,
                ty,
            }) => write!(f, "(Π {}:{}, {})", argty_name, argty_ty, ty),
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
        Ok(Term::Variable(s.into()))
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

    pub fn typeck(&self, env: &mut Cow<Env>) -> Result<Type> {
        match self {
            Term::Variable(s) => env
                .get_type(s)
                .cloned()
                .ok_or_else(|| TCError::UnknownVar(s.clone())),
            Term::Application(App { f, arg }) => match f.typeck_whnf(env)? {
                Term::Pi(Pi {
                    argty_name,
                    box argty_ty,
                    box ty,
                }) => {
                    let arg_ty = arg.typeck(env)?;
                    if !Enved::from((arg_ty.clone(), &**env))
                        .beta_eq(Enved::from((argty_ty.clone(), &**env)))
                    {
                        return Err(TCError::WrongArgumentType {
                            expected: argty_ty,
                            got: arg_ty,
                        });
                    }
                    Ok(ty.subst(&argty_name, arg))
                }
                other => Err(TCError::ExpectedFunc(other)),
            },
            Term::Lambda(Lam {
                arg_name,
                box arg_ty,
                box body,
            }) => {
                arg_ty.typeck(env)?;
                env.to_mut().add_type(arg_name.clone(), arg_ty.clone());
                let body_ty = body.typeck(env)?;
                let body_pi = Pi::new(arg_name.clone(), box arg_ty.clone(), box body_ty);
                let body_pi = Term::from(body_pi);
                body_pi.typeck(env)?;
                Ok(body_pi)
            }
            Term::Pi(Pi {
                argty_name,
                box argty_ty,
                box ty,
            }) => {
                let s = argty_ty.typeck_whnf(env)?;
                if !s.is_kind() {
                    return Err(TCError::ExpectedKind(s));
                }
                env.to_mut().add_type(argty_name.clone(), argty_ty.clone());
                let t = ty.typeck_whnf(env)?;
                if !t.is_kind() {
                    return Err(TCError::ExpectedKindReturn(t));
                }
                Ok(t)
            }
            Term::Universe(Universe(n)) => Ok(Universe(n + 1).into()),
        }
    }

    fn subst_var(self, s: &Var, v: Var) -> Term {
        self.subst(s, &Term::Variable(v))
    }

    /// Replaces all *free* occurrences of `v` by `x` in `b`, i.e. `b[v:=x]`.
    pub(crate) fn subst(self, v: &Var, x: &Term) -> Term {
        fn abstr<T: Into<Term>, F: Fn(Var, BTerm, BTerm) -> T>(
            con: F,
            v: &Var,
            x: &Term,
            i: &Var,
            t: Type,
            e: BTerm,
        ) -> Term {
            let fvx = x.free_vars();
            if v == i {
                con(i.clone(), box t.subst(v, x), e.clone()).into()
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
                con(i_new, box t.subst(v, x), box e_new.subst(v, x)).into()
            } else {
                con(i.clone(), box t.subst(v, x), box e.subst(v, x)).into()
            }
        }

        match self {
            Term::Variable(i) if &i == v => x.clone(),
            v @ Term::Variable(_) => v,
            Term::Application(App { box f, box arg }) => {
                App::new(f.into_inner().subst(v, x), arg.subst(v, x)).into()
            }
            Term::Lambda(Lam {
                arg_name,
                box arg_ty,
                body,
            }) => abstr(Lam::new, v, x, &arg_name, arg_ty, body),
            Term::Pi(Pi {
                argty_name,
                box argty_ty,
                ty,
            }) => abstr(Pi::new, v, x, &argty_name, argty_ty, ty),
            k @ Term::Universe(_) => k,
        }
    }

    /// Compares expressions modulo α-conversions. That is, λx.x == λy.y.
    pub(crate) fn alpha_eq(&self, other: &Term) -> bool {
        use Term as T;

        match (self, other) {
            (T::Variable(v1), T::Variable(v2)) if v1 == v2 => true,
            (T::Application(a1), T::Application(a2)) if a1.alpha_eq(a2) => true,
            (T::Lambda(l1), T::Lambda(l2)) if l1.alpha_eq(l2) => true,
            (T::Pi(p1), T::Pi(p2)) if p1.alpha_eq(p2) => true,
            (T::Universe(k1), T::Universe(k2)) if k1 == k2 => true,
            _ => false,
        }
    }

    /// Evaluates the expression to Weak Head Normal Form.
    pub fn whnf(self) -> Term {
        Enved::from((self, &Default::default())).whnf_in()
    }

    fn free_vars(&self) -> HashSet<Var> {
        match self {
            Term::Variable(s) => std::iter::once(s.clone()).collect(),
            Term::Application(a1) => a1.free_vars(),
            Term::Lambda(l1) => l1.free_vars(),
            Term::Pi(p1) => p1.free_vars(),
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
        use Term as T;

        let Self { inner, env } = self;

        match (inner, args) {
            (T::Application(App { box f, box arg }), _) => {
                let mut args_new = args.to_owned();
                args_new.push(arg);
                Self::from((f.into_inner(), env)).spine(&args_new, is_deep, is_strict)
            }
            (
                T::Lambda(Lam {
                    arg_name,
                    box arg_ty,
                    box body,
                }),
                [],
            ) => Lam {
                arg_name,
                arg_ty: Self::from((arg_ty, env))
                    .normalize(is_deep, is_strict)
                    .into(),
                body: Self::from((body, env))
                    .normalize_if_deep(is_deep, is_strict)
                    .into(),
            }
            .into(),
            (
                T::Lambda(Lam {
                    arg_name, box body, ..
                }),
                [xs @ .., x],
            ) => {
                let x = x.to_owned();
                let arg = Self::from((x, env)).normalize_if_strict(is_deep, is_strict);
                let ee = body.subst(&arg_name, &arg);
                let term = Self::from((ee, env)).normalize_if_deep(is_deep, is_strict);
                Self::from((term, env)).spine(xs, is_deep, is_strict)
            }
            (
                T::Pi(Pi {
                    argty_name,
                    box argty_ty,
                    box ty,
                }),
                _,
            ) => {
                // TODO: should we reverse args?
                let pi = Pi {
                    argty_name,
                    argty_ty: Self::from((argty_ty, env)).normalize(false, false).into(),
                    ty: Self::from((ty, env)).normalize(false, false).into(),
                };
                Self::from((pi.into(), env)).app(args)
            }
            (T::Variable(v), args) => env
                .get_decl(&v)
                .cloned()
                .map(|e| Self::from((e, env)).spine(args, is_deep, is_strict))
                .unwrap_or_else(|| {
                    let mut xs = args.to_owned();
                    xs.reverse();
                    Self::from((v.into(), env)).app(&xs)
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
            .fold(f, |f, arg| {
                App {
                    f: box ReducesTo::unchecked(f),
                    arg: box arg,
                }
                .into()
            })
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
        ty_name: &Var,
        ty_args: &Vec<(Option<Sym>, Type)>,
    ) -> Result<()> {
        let env = self.env;
        match self.whnf_in() {
            Term::Variable(v) if v == *ty_name => Ok(()),
            Term::Pi(Pi { ty: box body, .. }) | Term::Lambda(Lam { box body, .. }) => {
                Self::from((body, env)).ensure_ret_type_eq(ty_name, ty_args)
            }
            e => Err(TCError::ExpectedVarLamPi(e)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: Option<Var>,
    pub ty: Type,
}

impl Param {
    pub fn new(name: Option<Var>, ty: Type) -> Self {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::EnvedMut;
    use crate::parser::Parser;
    use crate::t;

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

    fn nat_def(_val: Term) -> Term {
        t! {
            lam nat: * => lam s: (nat -> nat) => lam z: nat => @val
        }
    }

    fn mul(_n: Term, m: Term) -> Term {
        let _plus_f = plus(m, nat(0));
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

    fn plus(_n: Term, _m: Term) -> Term {
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
