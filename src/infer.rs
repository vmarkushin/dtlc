use crate::decl::Params;
use crate::ensure;
use crate::env::{Env, EnvedMut};
use crate::term::{App, Lam, Param, Pi, TCError, Term, Type, Var};
use derive_more::From;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::HashMap;

impl Term {
    pub fn infer_type(self, env: &mut Env) -> Result<Type, TCError> {
        EnvedMut::new(self, env).infer_type()
    }
}

#[derive(Debug, From)]
pub struct Arguments {
    inner: Vec<Term>,
}

impl Arguments {
    pub fn app_to(self, f: Term) -> Term {
        self.inner
            .into_iter()
            .rev()
            .fold(f, |acc, t| App::new(acc, t).into())
    }
}

#[derive(Debug)]
struct AppView {
    f: Term,
    args: Arguments,
}

impl AppView {
    pub fn infer_holes(
        self,
        tele_view: TeleView,
        env: &mut Env,
    ) -> Result<(AppView, TeleView), TCError> {
        EnvedMut::new(self, env).infer_holes(tele_view)
    }

    pub(crate) fn to_app(mut self) -> Term {
        self.args.inner.reverse();
        self.args.app_to(self.f)
    }

    pub fn new(f: Term, args: impl Into<Arguments>) -> Self {
        AppView {
            f,
            args: args.into(),
        }
    }

    fn from_app(mut app: Term) -> Self {
        let mut args = Vec::new();
        loop {
            match app {
                Term::App(App { f, arg }) => {
                    args.insert(0, *arg);
                    app = (*f).into_inner().into();
                }
                t => {
                    app = t;
                    break;
                }
            }
        }
        Self::new(app, args)
    }
}

/// Telescope view.
struct TeleView {
    params: Params,
    ret: Term,
}

impl TeleView {
    pub fn new(params: Params, ret: Term) -> Self {
        TeleView { params, ret }
    }

    pub(crate) fn to_pi(mut self) -> Term {
        self.params.0.reverse();
        self.params.to_pi_with(self.ret)
    }

    fn from_pi(mut pi: Term) -> Self {
        let mut params = Vec::new();
        loop {
            match pi {
                Term::Pi(Pi {
                    param_name: x,
                    param_ty: a,
                    ty: b,
                }) => {
                    params.push(Param::new(Some(x), *a));
                    pi = *b;
                }
                t => {
                    pi = t;
                    break;
                }
            }
        }
        Self {
            params: params.into(),
            ret: pi,
        }
    }
}

impl<'a> EnvedMut<'a, AppView> {
    fn infer_holes(self, tele_view: TeleView) -> Result<(AppView, TeleView), TCError> {
        let mut ctx: HashMap<Var, Term> = Default::default();
        // ident => expected type
        let mut need_to_infer: HashMap<Var, Term> = Default::default();

        // TODO: the algorithm below only performs type inference, but not type-checking. Consider doing type-check too.
        let zs = self
            .inner
            .args
            .inner
            .into_iter()
            .zip(tele_view.params.0)
            .rev()
            .map(|(a, p)| match (a, p) {
                (
                    t,
                    Param {
                        name: Some(p_name),
                        ty: mut p_ty,
                    },
                ) if t.is_hole() => {
                    let t_ty = ctx.get(&p_name).unwrap_or(&p_ty).to_owned();
                    if p_ty.is_hole() {
                        p_ty = self.env.infer_type(t_ty.clone())?;
                    }
                    Ok((t_ty, Param::new(Some(p_name), p_ty)))
                }
                (t, Param { name, ty: mut p_ty }) => {
                    let t_ty = self.env.infer_type(t.clone())?;
                    if t_ty.is_hole() {
                        if let Term::Var(n) = &t {
                            need_to_infer.insert(n.clone(), p_ty.clone());
                        } else {
                            panic!("Unexpected value: {}", t);
                        }
                    }
                    if p_ty.is_hole() {
                        p_ty = self.env.infer_type(t_ty.clone())?;
                    } else if let Term::Var(n) = &p_ty {
                        if self.env.get_def(n).is_none()
                            && self.env.types.get(n).is_none()
                            && !t_ty.is_hole()
                        {
                            // Given t = `x : T`, p = `x : A`, `A` is unknown in the env,
                            // and T is not Hole, memorize `A = T`.
                            if let Some(v) = ctx.get(n) {
                                ensure!(
                                    *v == t_ty,
                                    TCError::WrongType {
                                        expected: t_ty,
                                        got: v.clone(),
                                    }
                                );
                            } else {
                                ctx.insert(n.clone(), t_ty);
                            }
                        }
                    }

                    Ok((t, Param::new(name, p_ty)))
                }
            })
            .collect::<Result<Vec<_>, TCError>>()?;
        for (n, exp_ty) in need_to_infer {
            if let Term::Var(nn) = exp_ty {
                let inf_ty = ctx
                    .get(&nn)
                    .ok_or(TCError::CantInferType(Term::Var(n.clone())))?;
                self.env.add_type(n, inf_ty.clone());
            }
        }
        let (xs, ys): (Vec<_>, Vec<_>) = zs.into_iter().unzip();
        Ok((
            AppView::new(self.inner.f, xs),
            TeleView::new(ys.into(), tele_view.ret),
        ))
    }
}

impl<'a> EnvedMut<'a, Term> {
    pub fn infer_type(&mut self) -> Result<Type, TCError> {
        match &self.inner {
            Term::Var(n) => self
                .env
                .get_type(n)
                .cloned()
                .ok_or_else(|| TCError::UnknownVar(n.clone())),
            app @ Term::App(..) => {
                let app_view = AppView::from_app(app.clone());
                let f_ty = app_view.f.clone().infer_type(&mut self.env.clone())?;
                let f_ty_whnf = f_ty.whnf(&*self.env);
                match f_ty_whnf {
                    pi @ Term::Pi(..) => {
                        let pi_view = TeleView::from_pi(pi);
                        let (app_view_new, pi_view_new) =
                            app_view.infer_holes(pi_view, &mut self.env.clone())?;
                        let mut app = app_view_new.to_app();
                        let mut pi = pi_view_new.to_pi();
                        loop {
                            match app {
                                Term::App(App { f: y, arg: box a }) => match pi {
                                    Term::Pi(Pi {
                                        param_name: x,
                                        param_ty: box at,
                                        ty: rt,
                                    }) => {
                                        let upd_ty = a.typeck(&mut Cow::Borrowed(&self.env), at)?;
                                        if let Term::Var(n) = &a {
                                            debug!("Updated type for {}: {}", n, upd_ty);
                                            self.env.add_type(n.clone(), upd_ty);
                                        }
                                        pi = rt.subst(&x, &a);
                                        app = (*y).into_inner();
                                    }
                                    other => return Err(TCError::ExpectedFunction(other)),
                                },
                                _ => return Ok(pi),
                            }
                        }
                    }
                    other => Err(TCError::ExpectedFunction(other)),
                }
            }
            Term::Lam(Lam {
                param_name: s,
                param_ty: t,
                body: e,
            }) => {
                let mut env_new = self.env.clone();
                env_new.add_type(s.clone(), *t.clone());
                let te = e.clone().infer_type(&mut env_new)?;

                // If we had something like `lam (x : _) => e`, then we may have infer x's type in the
                // `new_env` and should use it in the construction of a Pi.
                let param_ty = if t.is_hole() {
                    box env_new
                        .get_type(s)
                        .cloned()
                        .ok_or(TCError::CantInferType(Term::Var(s.clone())))?
                } else {
                    t.clone()
                };
                let lt = Term::Pi(Pi::new(s.clone(), param_ty, box te));
                lt.clone().infer_type(&mut self.env.clone())?;
                Ok(lt)
            }
            Term::Pi(Pi {
                param_name: x,
                param_ty: a,
                ty: b,
            }) => {
                let s = a.clone().infer_type(&mut self.env.clone())?;
                if !s.is_kind() {
                    return Err(TCError::ExpectedKind(s));
                }
                let mut env_new = self.env.clone();
                env_new.add_type(x.clone(), *a.clone());
                let t = b.clone().infer_type(&mut env_new)?;
                if !t.is_kind() {
                    return Err(TCError::ExpectedKindReturn(t));
                }
                // TODO: choose max level?
                Ok(t)
            }
            Term::Universe(n) => Ok(Term::Universe((n.0 + 1).into())),
            Term::Hole => Ok(Term::Hole),
        }
    }
}

impl Env {
    pub fn infer_type(&self, term: Term) -> Result<Type, TCError> {
        EnvedMut::from((term, &mut self.clone())).infer_type()
    }

    pub fn check_type(&self, term: Term, exp_ty: Type) -> Result<(), TCError> {
        term.typeck(&mut Cow::Borrowed(self), exp_ty).map(|_| ())
    }
}

impl Term {
    pub fn cmp_infer(&self, other: &Self) -> Ordering {
        match (self, other) {
            (_, Term::Hole) => Ordering::Greater,
            (Term::Hole, _) => Ordering::Less,
            _ => Ordering::Equal,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    macro_rules! pt {
        ($p:ident, $s:literal) => {
            $p.parse_term($s)?
        };
    }

    #[test]
    fn test_infer_type_basic() -> eyre::Result<()> {
        let mut env = Env::default();
        let p = Parser::default();
        env.add_type("T".into(), Term::Universe(0.into()));
        env.check_type(pt!(p, "T"), pt!(p, "Type"))?;
        assert_eq!(env.infer_type(pt!(p, "T"))?, pt!(p, "Type"));

        env.check_type(pt!(p, "lam (y : T) => y"), pt!(p, "forall (x : T), T"))?;
        assert_eq!(
            env.infer_type(pt!(p, "lam (y : T) => y"))?,
            pt!(p, "forall (y : T), T")
        );
        env.check_type(
            pt!(p, "lam (f : T -> T) (y : T) => f y"),
            pt!(p, "forall (ff : T -> T) (x : T), T"),
        )?;
        assert_eq!(
            env.infer_type(pt!(p, "lam (f : T -> T) (x : T) => f x"))?,
            pt!(p, "forall (f : T -> T) (x : T), T")
        );
        env.check_type(pt!(p, "forall (ff : T -> T) (x : T), T"), pt!(p, "Type"))?;
        assert_eq!(
            env.infer_type(pt!(p, "forall (ff : T -> T) (x : T), T"))?,
            pt!(p, "Type")
        );
        env.check_type(pt!(p, "Type0"), pt!(p, "Type1"))?;
        assert_eq!(env.infer_type(pt!(p, "Type0"))?, pt!(p, "Type1"));
        assert_eq!(
            env.check_type(pt!(p, "forall (ff : T -> T) (x : T), x"), pt!(p, "T"))
                .unwrap_err(),
            TCError::ExpectedKind(pt!(p, "T"))
        );
        assert_eq!(
            env.infer_type(pt!(p, "forall (ff : T -> T) (x : T), x"))
                .unwrap_err(),
            TCError::ExpectedKindReturn(pt!(p, "T"))
        );
        Ok(())
    }

    #[test]
    fn test_infer_type() -> eyre::Result<()> {
        env_logger::try_init()?;
        let mut env = Env::default();
        let p = Parser::default();
        let prog = p.parse_prog(
            r#"
    data Bool
        | true
        | false

    fn id (A : Type) (a : A) := a
    fn bool := true
    fn idb := id _ bool
    fn deep (f : forall (A : Type), A -> A -> A) (x : Bool) := (lam (y : _) => f _ y x) x
    fn deep' (f : forall (A : Type), A -> A -> A) (x : Bool) := (lam (y : _) => f _ x y) x
    "#,
        )?;
        for decl in prog {
            env.add_decl(decl);
        }
        assert_eq!(*env.get_type(&"bool".into()).unwrap(), pt!(p, "Bool"));
        assert_eq!(*env.get_type(&"Bool".into()).unwrap(), pt!(p, "Type"));

        assert_eq!(
            *env.get_type(&"id".into()).unwrap(),
            pt!(p, "forall (A : Type) (a : A), A")
        );
        assert_eq!(*env.get_type(&"idb".into()).unwrap(), pt!(p, "Bool"));
        assert_eq!(
            *env.get_type(&"deep".into()).unwrap(),
            pt!(
                p,
                "forall (f : forall (A : Type), A -> A -> A) (x : Bool), Bool"
            )
        );
        Ok(())
    }
}
