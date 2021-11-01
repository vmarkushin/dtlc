use crate::expr::{arrow, BExpr, Expr, Sym, Type};
use crate::item::{params_to_app, params_to_pi, Item};
use std::borrow::Cow;
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

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
            Item::Data {
                name,
                ty,
                ty_params,
                cons,
            } => {
                let ty = if let Some(ty) = ty {
                    ty
                } else {
                    Expr::Universe(0)
                };
                let params_pi = params_to_pi(ty_params.clone());
                let data_ty = match params_pi.clone() {
                    Some(pi) => arrow(pi, ty),
                    None => ty,
                };

                let data_ident = name.parse::<Expr>().unwrap();

                self.add_type(name, data_ty);

                for con in cons {
                    let data_app_ty = params_to_app(data_ident.clone(), ty_params.clone());
                    let con_ty = match params_to_pi(con.params) {
                        Some(pi) => arrow(pi, data_app_ty),
                        None => data_app_ty,
                    };
                    if let Some(pi) = &params_pi {
                        todo!("merge pis")
                        // merge_pis()
                    }
                    self.add_type(con.name, con_ty);
                }
            }
        }
    }

    pub fn run(&mut self, prog: Prog) -> BExpr {
        for mut item in prog {
            item.infer_or_check_type_in(self.clone()).unwrap();
            self.add_item(item);
        }
        let main = self
            .get_item(&"main".to_owned())
            .expect("function 'main' not found");
        main.typeck(self.clone()).unwrap();
        main.clone().nf(self)
    }
}

pub type Prog = Vec<Item>;

pub(crate) struct Enved<'a, T> {
    env: &'a Env,
    inner: T,
}

impl<'a, T> Enved<'a, T> {
    pub fn new(env: &'a Env, inner: T) -> Self {
        Enved { env, inner }
    }
}

impl<'a, T> EnvedMut<'a, T> {
    pub fn new(env: Cow<'a, Env>, inner: T) -> Self {
        Self { env, inner }
    }
}

pub(crate) struct EnvedMut<'a, T> {
    env: Cow<'a, Env>,
    inner: T,
}

impl<T> DerefMut for Enved<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T> Enved<'_, T> {
    pub fn into_inner(self) -> T {
        self.inner
    }
}

impl<T> Deref for Enved<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> EnvedMut<'_, T> {
    pub fn into_inner(self) -> T {
        self.inner
    }
}
