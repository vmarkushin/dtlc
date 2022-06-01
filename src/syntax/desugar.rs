use crate::syntax::abs::{
    Bind, ConsInfo as ConsInfoA, DataInfo as DataInfoA, Decl as DeclA, Expr as ExprA,
    Func as FuncA, Tele as TeleA,
};
use crate::syntax::surf::{Data, Decl, Expr, Func, NamedTele, Param};
use crate::syntax::{Ident, Plicitness, GI, MI, UID};
use std::cell::Cell;
use std::collections::BTreeMap;

#[derive(Debug, Clone, Default)]
pub struct DesugarState {
    /// Current meta ID for the definition.
    pub(crate) cur_meta_id: Vec<MI>,
    cur_local_id: Cell<UID>,
    /// Map Global Index -> DeclA.
    pub(crate) decls: Vec<DeclA>,
    /// Map from declaration name to its Global Index.
    pub(crate) decls_map: BTreeMap<String, GI>,
    local: Vec<BTreeMap<String, UID>>,
    local_count: Vec<usize>,
}

impl DesugarState {
    pub fn lookup_by_name(&self, name: &str) -> Option<(&DeclA, GI)> {
        let gi = *self
            .decls_map
            .get(name)
            .unwrap_or_else(|| panic!("{} not found", name));
        self.decls.get(gi).map(|decl| (decl, gi))
    }

    pub fn enter_local_scope(&mut self) {
        self.local.push(Default::default());
        self.local_count.push(Default::default());
    }

    pub fn exit_local_scope(&mut self) {
        self.local.pop().unwrap();
        let count = self.local_count.pop().unwrap();
        self.cur_local_id.update(|mut id| {
            id -= count;
            id
        });
    }

    pub fn insert_local(&mut self, name: String, uid: UID) {
        self.local.last_mut().unwrap().insert(name, uid);
    }

    pub fn clear_local(&mut self) {
        self.local.last_mut().unwrap().clear();
    }

    pub fn ensure_no_local_scopes(&self) {
        assert_eq!(self.local.len(), 1);
    }

    pub fn insert_decl(&mut self, decl: DeclA) -> Result<GI, DesugarError> {
        let string = &decl.ident().text;
        if self.decls_map.contains_key(string) {
            return Err(DesugarError::DuplicatedDecl(string.clone()));
        }
        self.cur_meta_id.push(Default::default());
        let gi = self.decls.len();
        self.decls_map.insert(string.clone(), gi);
        self.decls.push(decl);
        Ok(gi)
    }

    /// Removes last added declaration.
    pub fn remove_last_decl(&mut self) -> DeclA {
        self.cur_meta_id.pop();
        let decl = self.decls.pop().unwrap();
        self.decls_map.remove(&decl.ident().text);
        decl
    }

    pub fn lookup_local(&self, ident: &Ident) -> Option<UID> {
        self.local
            .iter()
            .rev()
            .find_map(|m| m.get(&ident.text).copied())
    }

    /// Note: this function will not clear the local scope.
    pub fn desugar_params(&mut self, params: Vec<Param>) -> Result<TeleA> {
        let mut tele = TeleA::with_capacity(params.len() + 1);
        // TODO: track locals changes?
        for param in params {
            let ty = param.ty.clone().map(|t| self.desugar_expr(t)).transpose()?;
            let mut intros = |name: Ident, licit: Plicitness, ty: Option<ExprA>| {
                let uid = self.next_uid();
                self.insert_local(name.text, uid);
                tele.push(Bind::new(licit, uid, ty, name.loc));
            };
            let licit = param.plic;
            let loc = ty
                .as_ref()
                .expect("type should be known by construction")
                .loc();
            match param.name {
                None => tele.push(Bind::new(licit, self.next_uid(), ty, loc)),
                Some(name) => intros(name, licit, ty),
            }
        }
        Ok(tele)
    }

    fn next_uid(&mut self) -> UID {
        *self.local_count.last_mut().unwrap() += 1;
        let x = self.cur_local_id.get();
        self.cur_local_id.set(x + 1);
        x
    }

    pub fn next_meta(&mut self) -> MI {
        let mi = self.cur_meta_id.last_mut().unwrap();
        let x = *mi;
        *mi += 1;
        x
    }
}

#[derive(Debug, thiserror::Error)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum DesugarError {
    #[error("Unresolved reference: `{0}`")]
    UnresolvedReference(String),
    #[error("Duplicated decl: `{0}`")]
    DuplicatedDecl(String),
}

pub type Result<T, E = DesugarError> = std::result::Result<T, E>;

pub fn desugar_prog(decls: Vec<Decl>) -> Result<DesugarState> {
    let mut s = DesugarState::default();
    s.enter_local_scope();
    s.cur_meta_id.push(Default::default());
    for decl in decls {
        s.desugar_decl(decl)?;
    }
    Ok(s)
}

impl DesugarState {
    /// Note: this function will not clear the local scope.
    pub fn desugar_telescope(&mut self, signature: NamedTele) -> Result<(TeleA, Ident)> {
        let ident = signature.name;
        let tele = self.desugar_params(signature.tele.0)?;
        Ok((tele, ident))
    }

    pub fn desugar_expr(&mut self, expr: Expr) -> Result<ExprA> {
        match expr {
            Expr::Var(v) => {
                if let Some(uid) = self.lookup_local(&v) {
                    Ok(ExprA::Var(v, uid))
                } else if let Some((decl, ix)) = self.lookup_by_name(&v) {
                    use DeclA::*;
                    match decl {
                        Data(_) => Ok(ExprA::Def(v, ix)),
                        Fn(_) => Ok(ExprA::Fn(v, ix)),
                        Cons(_) => Ok(ExprA::Cons(v, ix)),
                    }
                } else {
                    Err(DesugarError::UnresolvedReference(v.text.clone()))
                }
            }
            Expr::Lam(params, body) => {
                self.enter_local_scope();
                let res: Result<_> = try {
                    let tele = self.desugar_params(params.into_vec())?;
                    let ret = self.desugar_expr(*body)?;
                    (tele, ret)
                };
                self.exit_local_scope();
                let (tele, ret) = res?;
                let lam = tele.into_iter().rfold(ret, |ret, bind| {
                    let loc = bind.loc + ret.loc();
                    ExprA::Lam(loc, bind.boxed(), Box::new(ret))
                });
                Ok(lam)
            }
            Expr::App(f, args) => {
                let f = box self.desugar_expr(*f)?;
                let args = args.try_mapped(|e| self.desugar_expr(e))?;
                Ok(ExprA::App(f, args))
            }
            Expr::Universe(loc, u) => Ok(ExprA::Universe(loc, u)),
            Expr::Pi(params, ret) => {
                self.enter_local_scope();
                let res: Result<_> = try {
                    let tele = self.desugar_params(params.into_vec())?;
                    let ret = self.desugar_expr(*ret)?;
                    (tele, ret)
                };
                self.exit_local_scope();
                let (tele, ret) = res?;
                let pi = tele.into_iter().rfold(ret, |ret, bind| {
                    let loc = bind
                        .ty
                        .as_ref()
                        .expect("type in Π should be known by construction")
                        .loc()
                        + ret.loc();
                    ExprA::Pi(loc, bind.boxed(), Box::new(ret))
                });
                Ok(pi)
            }
            Expr::Hole(loc) => {
                let i = self.next_meta();
                Ok(ExprA::Meta(Ident::new(format!("hole{}", i), loc), i))
            }
        }
    }

    pub fn desugar_cons(&mut self, data_ix: GI, mut cons: Vec<NamedTele>) -> Result<()> {
        if let Some(con) = cons.pop() {
            self.enter_local_scope();
            let res = self.desugar_con(data_ix, con);
            self.exit_local_scope();
            res?;
            let res = self.desugar_cons(data_ix, cons);
            if res.is_err() {
                self.remove_last_decl();
            }
            res
        } else {
            Ok(())
        }
    }

    pub fn desugar_con(&mut self, data_ix: GI, con: NamedTele) -> Result<()> {
        let (tele, ident) = self.desugar_telescope(con)?;
        self.insert_decl(DeclA::Cons(ConsInfoA::new(ident.loc, ident, tele, data_ix)))?;
        Ok(())
    }

    pub fn desugar_decl(&mut self, decl: Decl) -> Result<DeclA> {
        match decl {
            Decl::Data(Data {
                sig,
                mut cons,
                universe,
            }) => {
                self.decls.reserve(cons.len() + 1);
                self.ensure_no_local_scopes();
                self.enter_local_scope();
                let res = self.desugar_telescope(sig);
                if res.is_err() {
                    self.exit_local_scope();
                }
                let (tele, ident) = res?;

                let global_id = self.curr_gi() + 1;
                let data_decl = DeclA::Data(DataInfoA::new(
                    ident.loc,
                    ident,
                    universe,
                    tele,
                    (global_id..global_id + cons.len()).collect(),
                ));
                let res = self.insert_decl(data_decl.clone());
                if res.is_err() {
                    self.exit_local_scope();
                }
                res?;

                cons.reverse();
                let res = self.desugar_cons(global_id - 1, cons);
                if res.is_err() {
                    self.remove_last_decl();
                }
                self.exit_local_scope();
                res?;

                Ok(data_decl)
            }
            Decl::Fn(Func {
                name,
                params,
                ret_ty,
                body,
            }) => {
                let body_new = params.clone().to_lam(body);
                let ty_new = if let Some(rt) = ret_ty {
                    params.to_pi_with(rt)
                } else {
                    params.to_pi_with(Expr::Hole(name.loc))
                };
                self.ensure_no_local_scopes();
                let res: Result<_> = try {
                    let expr = self.desugar_expr(body_new)?;
                    let ty = self.desugar_expr(ty_new)?;
                    (expr, ty)
                };
                self.clear_local();
                let (expr, ty) = res?;
                let decl = DeclA::Fn(FuncA::new(name, expr, Some(ty))); // TODO: get rid of Option?
                self.insert_decl(decl.clone())?;
                Ok(decl)
            }
        }
    }

    fn curr_gi(&self) -> GI {
        self.decls.len() as GI
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;
    use crate::syntax::abs::Expr::{Def, Meta, Pi};
    use crate::syntax::desugar::desugar_prog;
    use crate::syntax::Plicitness::Explicit;
    use crate::syntax::{Ident, Loc, Universe};
    use itertools::Itertools;
    use vec1::Vec1;

    #[test]
    fn test_desugar() {
        let mut parser = Parser::default();
        let state = desugar_prog(
            parser
                .parse_prog(
                    r#"
data Nat : Type
    | Z
    | S Nat

fn foo (p : Nat) := (lam (f : Nat -> Nat) => f p) (lam (n : Nat) => n)
"#,
                )
                .unwrap(),
        )
        .unwrap();
        assert_eq!(
            state
                .decls_map
                .into_iter()
                .sorted_by_key(|x| x.1)
                .map(|(x, y)| (x, state.decls[y].clone()))
                .collect::<Vec<_>>(),
            vec![
                (
                    "Nat".to_owned(),
                    DeclA::Data(DataInfoA::new(
                        (6..9).into(),
                        Ident::new("Nat", 6..9),
                        Some(Universe(0)),
                        vec![],
                        vec![1, 2]
                    ))
                ),
                (
                    "Z".to_owned(),
                    DeclA::Cons(ConsInfoA::new(
                        (23..24).into(),
                        Ident::new("Z", 23..24),
                        vec![],
                        0
                    )),
                ),
                (
                    "S".to_owned(),
                    DeclA::Cons(ConsInfoA::new(
                        (31..32).into(),
                        Ident::new("S", 31..32),
                        vec![Bind::new(
                            Explicit,
                            0,
                            Some(ExprA::Def(Ident::new("Nat", 33..36), 0)),
                            Loc::new(33, 36)
                        )],
                        0
                    )),
                ),
                (
                    "foo".to_owned(),
                    DeclA::Fn(FuncA::new(
                        Ident::new("foo", Loc::new(41, 44),),
                        ExprA::Lam(
                            Loc {
                                start: 46,
                                end: 107
                            },
                            Bind {
                                licit: Explicit,
                                name: 0,
                                ty: box Some(Def(
                                    Ident {
                                        loc: Loc::new(50, 53),
                                        text: "Nat".to_owned()
                                    },
                                    0
                                )),
                                loc: Loc::new(46, 47)
                            },
                            box ExprA::App(
                                box ExprA::Lam(
                                    Loc::new(64, 86),
                                    Bind {
                                        licit: Explicit,
                                        name: 1,
                                        ty: box Some(ExprA::Pi(
                                            Loc::new(68, 78),
                                            Bind {
                                                licit: Explicit,
                                                name: 1,
                                                ty: box Some(Def(
                                                    Ident {
                                                        loc: Loc::new(68, 71),
                                                        text: "Nat".to_owned()
                                                    },
                                                    0
                                                )),
                                                loc: Loc::new(68, 71)
                                            },
                                            box Def(
                                                Ident {
                                                    loc: Loc::new(75, 78),
                                                    text: "Nat".to_owned()
                                                },
                                                0
                                            )
                                        )),
                                        loc: Loc::new(64, 65)
                                    },
                                    box ExprA::App(
                                        box ExprA::Var(
                                            Ident {
                                                loc: Loc::new(83, 84),
                                                text: "f".to_owned()
                                            },
                                            1
                                        ),
                                        Vec1::new(ExprA::Var(
                                            Ident {
                                                loc: Loc::new(85, 86),
                                                text: "p".to_owned()
                                            },
                                            0
                                        ))
                                    )
                                ),
                                Vec1::new(ExprA::Lam(
                                    Loc {
                                        start: 94,
                                        end: 107
                                    },
                                    Bind {
                                        licit: Explicit,
                                        name: 1,
                                        ty: box Some(Def(
                                            Ident {
                                                loc: Loc {
                                                    start: 98,
                                                    end: 101
                                                },
                                                text: "Nat".to_owned()
                                            },
                                            0
                                        )),
                                        loc: Loc::new(94, 95)
                                    },
                                    box ExprA::Var(
                                        Ident {
                                            loc: Loc {
                                                start: 106,
                                                end: 107
                                            },
                                            text: "n".to_owned()
                                        },
                                        1
                                    )
                                ))
                            )
                        ),
                        Some(Pi(
                            Loc::new(50, 44),
                            Bind::new(
                                Explicit,
                                0,
                                box Some(Def(Ident::new("Nat", Loc::new(50, 53)), 0)),
                                Loc::new(46, 47)
                            ),
                            box Meta(Ident::new("hole0", Loc::new(41, 44)), 0)
                        )),
                    )),
                )
            ]
        );
    }
}
