use crate::expr::{Expr, Sym, Type};
use crate::item::Item;
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
                ty_params: ty_args,
                cons,
            } => {
                let ty = if let Some(ty) = ty {
                    ty
                } else {
                    Expr::Universe(0)
                };
                self.add_type(name, ty.clone());
                for (con_name, con) in cons {
                    if let Some(con) = con {
                        self.add_type(con_name, con);
                    } else {
                        self.add_type(con_name, ty.clone());
                    }
                }
            }
        }
    }
}

impl<'a> EnvedMut<'a, Prog> {
    pub fn run(self) -> Expr {
        for mut item in self.inner {
            item.infer_or_check_type_in(&mut Cow::Borrowed(self.env))
                .unwrap();
            self.env.add_item(item);
        }
        let main = self
            .env
            .get_item(&"main".to_owned())
            .expect("function 'main' not found");
        main.typeck(&mut Cow::Borrowed(self.env)).unwrap();
        Enved::from((main.clone(), &*self.env)).nf()
    }
}

pub type Prog = Vec<Item>;
