#![allow(clippy::ptr_arg)]

use crate::env::{Env, Enved, EnvedMut};
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
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum TCError {
    #[error("Unknown variable: `{0}`")]
    UnknownVar(Var),

    #[error("Wrong type. Expected `{expected}`, but got `{got}`")]
    WrongType { expected: Type, got: Type },
    #[error("Wrong argument type. Expected `{expected}`, but got `{got}`")]
    WrongArgumentType { expected: Type, got: Type },

    #[error("Expected function type, but got `{0}`")]
    ExpectedFunction(Type),
    #[error("Expected kind but got type `{0}`")]
    ExpectedKind(Type),
    #[error("Expected kind at return type, but got `{0}`")]
    ExpectedKindReturn(Type),
    #[error("Expected var, lam or pi, but got `{0}`")]
    ExpectedVarLamPi(Type),

    #[error("Kinds higher than [] are not supported")]
    KindTooHigh,

    #[error("Can't infer type for `{0}`")]
    CantInferType(Term),
    #[error("Function `{0}` takes `{1}` arguments, but got `{2}`")]
    TooManyArgs(Term, usize, usize),
    #[error("Cannot unify `{0}` and `{1}`")]
    CantUnify(Term, Term),
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
    pub fn into_inner(self) -> Term {
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
    pub param_name: Var,
    pub param_ty: BType,
    pub body: BTerm,
}

impl Lam {
    pub fn new(param_name: Var, param_ty: impl Into<BType>, body: impl Into<BType>) -> Self {
        Self {
            param_name,
            param_ty: param_ty.into(),
            body: body.into(),
        }
    }

    pub fn new_many(
        term: Term,
        params: impl Sized + DoubleEndedIterator<Item = (Var, Type)>,
    ) -> Term {
        params.into_iter().rev().fold(term, |acc, (arg, param_ty)| {
            Self::new(arg, box param_ty, box acc).into()
        })
    }

    pub fn alpha_eq(&self, other: &Self) -> bool {
        let Self {
            param_name: s1,
            param_ty: t1,
            body: e1,
        } = self;
        let Self {
            param_name: s2,
            param_ty: t2,
            body: e2,
        } = other;
        t1.alpha_eq(t2) && e1.alpha_eq(&e2.clone().subst_var(s2, s1.clone()))
    }

    pub fn free_vars(&self) -> HashSet<Var> {
        let Self {
            param_name,
            param_ty,
            body,
        } = self;
        let mut set = body.free_vars();
        set.remove(param_name);
        param_ty.free_vars().into_iter().chain(set).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pi {
    pub param_name: Var,
    pub param_ty: BType,
    pub ty: BTerm,
}

impl Pi {
    pub fn new(
        param_name: impl Into<Var>,
        param_ty: impl Into<BType>,
        ty: impl Into<BTerm>,
    ) -> Self {
        Self {
            param_name: param_name.into(),
            param_ty: param_ty.into(),
            ty: ty.into(),
        }
    }

    pub fn new_many(
        term: Term,
        params: impl Sized + DoubleEndedIterator<Item = (Var, Type)>,
    ) -> Term {
        params
            .into_iter()
            .rev()
            .fold(term, |acc, (param_name, param_ty)| {
                Self::new(param_name, box param_ty, box acc).into()
            })
    }

    pub fn arrow(param_ty: impl Into<Type>, ty: impl Into<Type>) -> Self {
        Self::new(Var("_".to_owned()), box param_ty.into(), box ty.into())
    }

    pub fn alpha_eq(&self, other: &Self) -> bool {
        let Self {
            param_name: s1,
            param_ty: t1,
            ty: e1,
        } = self;
        let Self {
            param_name: s2,
            param_ty: t2,
            ty: e2,
        } = other;
        t1.alpha_eq(t2) && e1.alpha_eq(&e2.clone().subst_var(s2, s1.clone()))
    }

    pub fn free_vars(&self) -> HashSet<Var> {
        let Self {
            param_name,
            param_ty,
            ty,
        } = self;
        let mut set = ty.free_vars();
        set.remove(param_name);
        param_ty.free_vars().into_iter().chain(set).collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Display, Default, From, Add)]
pub struct Universe(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, From)]
pub enum Term {
    Var(Var),
    App(App),
    Lam(Lam),
    Pi(Pi),
    Universe(Universe),
    Hole,
}

impl Term {
    pub(crate) fn ensure_well_formed_type(&self, env: &mut Cow<Env>) -> Result<Type> {
        let norm = Enved::from((self.clone(), &**env)).whnf_in();
        let t = env.to_mut().infer_type(norm)?;
        ensure!(t.is_kind(), TCError::ExpectedKind(t));
        Ok(t)
    }

    pub fn is_hole(&self) -> bool {
        matches!(self, Term::Hole)
    }

    pub fn is_kind(&self) -> bool {
        matches!(self, Term::Universe(_))
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Var(Var(i)) => f.write_str(i),
            Term::App(App { f: ff, arg }) => {
                write!(f, "{} ", &***ff)?;
                match arg.as_ref() {
                    app @ Term::App(_) => write!(f, "({})", app),
                    e => write!(f, "{}", e),
                }
            }
            Term::Lam(Lam {
                param_name,
                param_ty,
                body,
            }) => write!(f, "(λ {}:{}. {})", param_name, param_ty, body),
            Term::Pi(Pi {
                param_name,
                param_ty,
                ty,
            }) => write!(f, "(Π {}:{}, {})", param_name, param_ty, ty),
            Term::Universe(k) => write!(f, "Type{}", k),
            Term::Hole => write!(f, "_"),
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
        if s == "_" {
            return Ok(Term::Hole);
        }
        ensure!(
            s.chars().all(|c| char::is_alphanumeric(c) || c == '_'),
            ParseExprError(s),
        );
        Ok(Term::Var(s.into()))
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
    pub(crate) fn typeck_whnf(&self, r: &mut Cow<Env>, exp_ty: Type) -> Result<Type> {
        Ok(self.typeck(r, exp_ty)?.whnf())
    }

    #[allow(unused)]
    pub(crate) fn typecheck(&self, exp_ty: Type) -> Result<Type> {
        self.typeck(&mut Cow::Owned(Default::default()), exp_ty)
    }

    pub fn typeck(&self, env: &mut Cow<Env>, exp_ty: Type) -> Result<Type> {
        match self {
            Term::Lam(Lam {
                param_name: s,
                param_ty: t,
                body: e,
            }) => {
                let exp_ty = exp_ty.whnf();
                match exp_ty {
                    Term::Pi(Pi {
                        param_name: x,
                        param_ty: box at,
                        ty: box rt,
                    }) => {
                        // TODO: ensure t == at ?
                        env.to_mut().add_type(s.clone(), *t.clone());
                        // env.to_mut().add_type(x.clone(), at.clone());
                        Ok(e.typeck(env, rt)?)
                    }
                    other => Err(TCError::ExpectedFunction(other)),
                }
            }
            Term::Pi(Pi {
                param_name: x,
                param_ty: a,
                ty: b,
            }) => {
                let exp_ty = exp_ty.whnf();
                match exp_ty {
                    uni @ Term::Universe(_) => {
                        a.typeck_whnf(env, uni.clone())?;
                        env.to_mut().add_type(x.clone(), *a.clone());
                        let t = b.typeck_whnf(env, uni)?;
                        Ok(t)
                    }
                    _ => Err(TCError::ExpectedKind(exp_ty)),
                }
            }
            Term::Hole => Ok(exp_ty),
            other => {
                let term_ty = EnvedMut::from((other.clone(), env.to_mut())).infer_type()?;
                if exp_ty.is_hole() {
                    return Ok(term_ty);
                } else if term_ty.is_hole() {
                    return Ok(exp_ty);
                }
                ensure!(
                    Enved::from((term_ty.clone(), env.as_ref()))
                        .beta_eq(Enved::from((exp_ty.clone(), env.as_ref()))),
                    TCError::WrongType {
                        expected: exp_ty,
                        got: term_ty
                    }
                );
                Ok(term_ty)
            }
        }
    }

    fn subst_var(self, s: &Var, v: impl Into<Var>) -> Term {
        self.subst(s, &Term::Var(v.into()))
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
            Term::Var(i) if &i == v => x.clone(),
            v @ Term::Var(_) => v,
            Term::App(App { box f, box arg }) => {
                App::new(f.into_inner().subst(v, x), arg.subst(v, x)).into()
            }
            Term::Lam(Lam {
                param_name,
                box param_ty,
                body,
            }) => abstr(Lam::new, v, x, &param_name, param_ty, body),
            Term::Pi(Pi {
                param_name,
                box param_ty,
                ty,
            }) => abstr(Pi::new, v, x, &param_name, param_ty, ty),
            k @ Term::Universe(_) => k,
            h @ Term::Hole => h,
        }
    }

    /// Compares expressions modulo α-conversions. That is, λx.x == λy.y.
    pub(crate) fn alpha_eq(&self, other: &Term) -> bool {
        use Term as T;

        match (self, other) {
            (T::Var(v1), T::Var(v2)) if v1 == v2 => true,
            (T::App(a1), T::App(a2)) if a1.alpha_eq(a2) => true,
            (T::Lam(l1), T::Lam(l2)) if l1.alpha_eq(l2) => true,
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
            Term::Var(s) => std::iter::once(s.clone()).collect(),
            Term::App(a1) => a1.free_vars(),
            Term::Lam(l1) => l1.free_vars(),
            Term::Pi(p1) => p1.free_vars(),
            Term::Universe(_) => Default::default(),
            Term::Hole => Default::default(),
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
            (T::App(App { box f, box arg }), _) => {
                let mut args_new = args.to_owned();
                args_new.push(arg);
                Self::from((f.into_inner(), env)).spine(&args_new, is_deep, is_strict)
            }
            (
                T::Lam(Lam {
                    param_name,
                    box param_ty,
                    box body,
                }),
                [],
            ) => Lam {
                param_name,
                param_ty: Self::from((param_ty, env))
                    .normalize(is_deep, is_strict)
                    .into(),
                body: Self::from((body, env))
                    .normalize_if_deep(is_deep, is_strict)
                    .into(),
            }
            .into(),
            (
                T::Lam(Lam {
                    param_name,
                    box body,
                    ..
                }),
                [xs @ .., x],
            ) => {
                let x = x.to_owned();
                let arg = Self::from((x, env)).normalize_if_strict(is_deep, is_strict);
                let ee = body.subst(&param_name, &arg);
                let term = Self::from((ee, env)).normalize_if_deep(is_deep, is_strict);
                Self::from((term, env)).spine(xs, is_deep, is_strict)
            }
            (
                T::Pi(Pi {
                    param_name,
                    box param_ty,
                    box ty,
                }),
                _,
            ) => {
                // TODO: should we reverse args?
                let pi = Pi {
                    param_name,
                    param_ty: Self::from((param_ty, env)).normalize(false, false).into(),
                    ty: Self::from((ty, env)).normalize(false, false).into(),
                };
                Self::from((pi.into(), env)).app(args)
            }
            (T::Var(v), args) => env
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
    #[allow(unused)]
    pub fn ensure_ret_type_eq(
        self,
        ty_name: &Var,
        ty_args: &Vec<(Option<Sym>, Type)>,
    ) -> Result<()> {
        let env = self.env;
        match self.whnf_in() {
            Term::Var(v) if v == *ty_name => Ok(()),
            Term::Pi(Pi { ty: box body, .. }) | Term::Lam(Lam { box body, .. }) => {
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
    // use quickcheck::quickcheck;

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
    fn test_substitution() -> eyre::Result<()> {
        let p = Parser::default();
        let t = p.parse_term("lam (A : Type) (x : A) => x").unwrap();
        match t {
            Term::Lam(Lam {
                param_name: n,
                param_ty: t,
                body: b,
            }) => {
                assert_beta_eq(
                    b.subst_var(&n, "x".to_owned()),
                    p.parse_term("lam (x' : x) => x'")?,
                    &Default::default(),
                );
            }
            _ => unreachable!(),
        };

        let t = p.parse_term("forall (A : Type) (a : A), A").unwrap();
        match t {
            Term::Pi(Pi {
                param_name: n,
                param_ty: a,
                ty: b,
            }) => {
                assert_beta_eq(
                    b.subst_var(&n, "Bool"),
                    p.parse_term("forall (a : Bool), Bool")?,
                    &Default::default(),
                );
            }
            _ => unreachable!(),
        };
        Ok(())
    }

    #[test]
    #[ignore]
    fn test_id() {
        let res = run_prog(
            r#"
        data Nat
            | O : Nat
            | S : Nat -> Nat
        fn id => lam (A : Type) (x : A) => x
        fn zero => lam (s : Nat -> Nat) (z : Nat) => z
        fn main => id Nat (zero S O)
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
        n.typecheck(t!(forall t : *, (t -> t) -> (t -> t))).unwrap();
        assert_beta_eq(
            n,
            t!(lam nat:* => (lam s:(forall _:nat, nat) => lam z:nat => s (s (s (s z))))),
            &env,
        );

        let e1 = plus(nat(5), nat(7));
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
        let env = Env::new();
        assert!(env.infer_type(parser.parse_term("x").unwrap()).is_err());
    }
}
