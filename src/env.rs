use crate::decl::{merge_pis, params_to_app, params_to_pi, Decl};
use crate::term::{arrow, BTerm, Sym, Term, Type};
use std::borrow::Cow;
use std::collections::HashMap;

use derive_more::{Deref, DerefMut, From};

#[derive(DerefMut, Deref, From)]
pub struct Enved<'a, T> {
    #[deref]
    #[deref_mut]
    pub inner: T,
    pub env: &'a Env,
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

#[derive(Clone, Default, Debug)]
pub struct Env {
    types: HashMap<Sym, Type>,
    defs: HashMap<Sym, Term>,
}

impl Env {
    pub(crate) fn get_decl(&self, sym: &Sym) -> Option<&Term> {
        self.defs.get(sym)
    }
}

impl Env {
    pub(crate) fn get_type(&self, p0: &str) -> Option<&Type> {
        self.types.get(p0)
    }
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }

    pub fn run(&mut self, prog: Prog) -> Term {
        EnvedMut::from((prog, self)).run()
    }

    pub fn add_type(&mut self, sym: Sym, ty: Type) {
        self.types.insert(sym, ty);
    }

    pub fn add_decl(&mut self, decl: Decl) {
        use crate::dsp;

        match decl {
            Decl::Fn { name, ty, body } => {
                if let Some(ty) = ty {
                    self.add_type(name.clone(), ty);
                }
                self.defs.insert(name, body);
            }
            Decl::Data {
                name,
                ty,
                ty_params,
                cons,
            } => {
                let ty = if let Some(ty) = ty {
                    ty
                } else {
                    Term::Universe(0)
                };
                let params_pi = params_to_pi(ty_params.clone());
                let data_ty = match params_pi.clone() {
                    Some(pi) => arrow(pi, ty),
                    None => ty,
                };

                let data_ident = name.parse::<Term>().unwrap();

                self.add_type(name, data_ty);

                for con in cons {
                    let data_app_ty = params_to_app(data_ident.clone(), ty_params.clone());
                    let con_ty = if !con.params.is_empty() {
                        merge_pis(con.params.clone(), data_app_ty)
                    } else {
                        data_app_ty
                    };
                    let con_ty = if !ty_params.is_empty() {
                        merge_pis(ty_params.clone(), con_ty)
                    } else {
                        con_ty
                    };
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
            .get_decl(&"main".to_owned())
            .expect("function 'main' not found");
        main.typeck(&mut Cow::Borrowed(self.env)).unwrap();
        Enved::from((main.clone(), &*self.env)).nf()
    }
}

pub type Prog = Vec<Decl>;
