use crate::decl::{Decl, FnDecl};
use crate::term::{Pi, Term, Type, Var};
use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt::Formatter;

use derive_more::{Deref, DerefMut, From};

#[derive(DerefMut, Deref, From)]
pub struct Enved<'a, T> {
    #[deref]
    #[deref_mut]
    pub inner: T,
    pub env: &'a Env,
}

impl<'a, T> Enved<'a, T> {
    pub fn new(inner: T, env: &'a Env) -> Self {
        Enved { inner, env }
    }
}

impl<'a, T: Clone> Clone for Enved<'a, T> {
    fn clone(&self) -> Self {
        let inner = self.inner.clone();
        let env = self.env;
        Self { inner, env }
    }
}

#[derive(DerefMut, Deref, From)]
pub struct EnvedMut<'a, T> {
    #[deref]
    #[deref_mut]
    pub inner: T,
    pub env: &'a mut Env,
}

impl<'a, T> EnvedMut<'a, T> {
    pub fn new(inner: T, env: &'a mut Env) -> Self {
        EnvedMut { inner, env }
    }
}

#[derive(Clone, Default, Debug)]
pub struct Env {
    pub(crate) types: HashMap<Var, Type>,
    defs: HashMap<Var, Term>,
}

impl std::fmt::Display for Env {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (name, def) in &self.defs {
            writeln!(f, "{} := {}", name, def)?;
        }
        for (name, t) in &self.types {
            writeln!(f, "{} : {}", name, t)?;
        }
        Ok(())
    }
}

impl Env {
    pub(crate) fn get_decl(&self, sym: &Var) -> Option<&Term> {
        self.defs.get(sym)
    }

    pub(crate) fn get_type(&self, p0: &Var) -> Option<&Type> {
        self.types.get(p0)
    }

    pub fn new() -> Self {
        Env::default()
    }

    pub fn run(&mut self, prog: Prog) -> Term {
        EnvedMut::from((prog, self)).run()
    }

    pub fn add_type(&mut self, sym: Var, ty: Type) {
        if sym.0 == "_" {
            return;
        }
        let maybe_ty = self.types.get(&sym);
        assert!(
            maybe_ty.is_none() || maybe_ty == Some(&Term::Hole) || maybe_ty == Some(&ty),
            "{} is already defined",
            sym
        );
        // TODO: whnf in env?
        self.types.insert(sym, ty.whnf(&*self));
    }

    pub fn get_def(&self, name: &Var) -> Option<&Term> {
        self.defs.get(name)
    }

    pub fn add_def(&mut self, name: Var, term: Term) {
        debug!("Inferring type for decl `{}`", name);
        let term_ty = if let Some(ty) = self.get_type(&name) {
            term.typeck(&mut Cow::Borrowed(&self), ty.clone()).unwrap()
        } else {
            term.clone().infer_type(&mut self.clone()).unwrap()
        };
        self.add_type(name.clone(), term_ty);
        self.defs.insert(name, term);
    }

    pub fn add_decl(&mut self, decl: Decl) {
        match decl {
            Decl::Fn(FnDecl {
                name,
                params,
                ret_ty,
                body,
            }) => {
                if let Some(ty) = ret_ty {
                    let gen_ty = params.clone().to_pi_with(ty);
                    self.add_type(name.clone(), gen_ty);
                }
                let gen_body = params.to_lam(body);
                self.add_def(name, gen_body.whnf(&*self));
            }
            Decl::Data {
                name,
                universe,
                ty_params,
                cons,
            } => {
                let ty = if let Some(ty) = universe {
                    ty
                } else {
                    Term::Universe(Default::default())
                };

                let params_pi = ty_params.clone().to_pi();
                let data_ty = match params_pi {
                    Some(pi) => Pi::arrow(pi, ty).into(),
                    None => ty,
                };

                let data_ident = name.parse::<Term>().unwrap();

                self.add_type(name, data_ty);
                for con in cons {
                    let data_app_ty = ty_params.clone().app(data_ident.clone());
                    let con_ty = ty_params
                        .clone()
                        .to_pi_with(con.params.clone().to_pi_with(data_app_ty));
                    self.add_type(con.name, con_ty);
                }
            }
        }
    }
}

impl<'a> EnvedMut<'a, Prog> {
    pub fn run(self) -> Term {
        for mut decl in self.inner {
            decl.infer_or_check_type_in(&mut Cow::Borrowed(self.env))
                .unwrap();
            self.env.add_decl(decl);
        }
        let main = self
            .env
            .get_decl(&Var("main".to_owned()))
            .expect("function 'main' not found")
            .to_owned();
        self.env.infer_type(main.clone()).unwrap();
        main.nf(&*self.env)
    }
}

pub type Prog = Vec<Decl>;
