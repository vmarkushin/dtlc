use crate::ensure;
use crate::syntax::abs::{
    Bind, Case as CaseA, ConsInfo as ConsInfoA, DataInfo as DataInfoA, Decl as DeclA,
    Expr as ExprA, Func as FuncA, Id, Match, Pat as PatA, Tele as TeleA,
};
use crate::syntax::core::Boxed;
use crate::syntax::surf::{Case, Data, Decl, Expr, Func, MetaAttr, NamedTele, Param, Pat, Prog};
use crate::syntax::{ConHead, Ident, LangItem, Plicitness, GI, MI, UID};
use itertools::Either;
use itertools::Either::{Left, Right};
use std::cell::Cell;
use std::collections::{BTreeMap, HashMap};
use std::str::FromStr;
use vec1::Vec1;

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
    pub lang_items: HashMap<LangItem, GI>,
    pub lang_items_rev: HashMap<GI, LangItem>,
}

struct LocalScope {
    state: *mut DesugarState,
}

impl LocalScope {
    pub fn enter(state: &mut DesugarState) -> Self {
        state.enter_local_scope();
        LocalScope { state }
    }
}

impl Drop for LocalScope {
    fn drop(&mut self) {
        unsafe {
            (*self.state).exit_local_scope();
        }
    }
}

impl DesugarState {
    pub fn lookup_by_name(&self, name: &str) -> Option<(&DeclA, GI)> {
        self.decls_map
            .get(name)
            .and_then(|gi| self.decls.get(*gi).map(|decl| (decl, *gi)))
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
                self.insert_local(name.text.clone(), uid);
                tele.push(Bind::identified(licit, uid, ty, name));
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
    #[error("Wrong number of arguments in Id")]
    IdWrongArity,
    #[error("Expected tuple in Id")]
    IdNoTuple,
}

pub type Result<T, E = DesugarError> = std::result::Result<T, E>;

pub fn desugar_prog(decls: Prog) -> Result<DesugarState> {
    let mut s = DesugarState::default();
    s.enter_local_scope();
    s.cur_meta_id.push(Default::default());
    for decl in decls.0 {
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

    pub fn desugar_pat(&mut self, pat: Pat) -> Result<PatA> {
        let pat = match pat {
            Pat::Var(name) => {
                if let Some((DeclA::Cons(..), ix)) = self.lookup_by_name(&name.text) {
                    PatA::Cons(false, ConHead::new(name, ix), Vec::new())
                } else {
                    let uid = self.next_uid();
                    self.insert_local(name.text, uid);
                    PatA::Var(uid)
                }
            }
            Pat::Wildcard => {
                let uid = self.next_uid();
                PatA::Var(uid)
            }
            Pat::Absurd => PatA::Absurd,
            Pat::Cons(forced, head, args) => {
                let head_ix =
                    if let Some((DeclA::Cons(..), ix)) = self.lookup_by_name(&head.name.text) {
                        ix
                    } else {
                        debug!(target: "desugar", "context: {:?}", self.local);
                        panic!("{} not found", head.name.text)
                    };
                let head = ConHead::new(head.name, head_ix);
                let args = args
                    .into_iter()
                    .map(|pat| self.desugar_pat(pat))
                    .collect::<Result<Vec<_>>>()?;
                PatA::Cons(forced, head, args)
            }
            Pat::Forced(term) => PatA::Forced(self.desugar_expr(term)?),
        };
        Ok(pat)
    }

    pub fn desugar_case(&mut self, case: Case) -> Result<CaseA> {
        let _scope = LocalScope::enter(self);
        let pattern = case
            .patterns
            .into_iter()
            .map(|p| self.desugar_pat(p))
            .collect::<Result<Vec<_>>>()?;
        let body = case.body.map(|body| self.desugar_expr(body)).transpose()?;
        Ok(CaseA::new(Default::default(), pattern, body))
    }

    /// Desugars expression of kind:
    /// `pair x (pair y ...)`
    fn desugar_tuple(&self, expr: ExprA) -> Result<Vec<ExprA>> {
        if let ExprA::Tuple(_, args) = expr {
            Ok(args)
        } else {
            Err(DesugarError::IdNoTuple)
        }
    }

    /// Desugars an expression of kind:
    /// `Id (lam (x1 : A1) ... (xn : An) => (B, a1, a2)) p1 ... pn`
    fn maybe_desugar_id(
        &mut self,
        f: ExprA,
        args: Vec1<ExprA>,
    ) -> Result<Either<ExprA, (ExprA, Vec1<ExprA>)>, DesugarError> {
        match f {
            ExprA::Data(v, gi) => match self.lang_items_rev.get(&gi) {
                Some(LangItem::Id) => {
                    let mut args = args.to_vec();
                    let (tele, triple) = args.remove(0).into_tele_view();
                    let paths = args;
                    ensure!(tele.len() == paths.len(), DesugarError::IdWrongArity);
                    let [ty, a1, a2]: [ExprA; 3] = self
                        .desugar_tuple(triple)?
                        .try_into()
                        .map_err(|_| DesugarError::IdNoTuple)?;
                    let id = Id::new(tele, ty.boxed(), paths, a1.boxed(), a2.boxed());
                    Ok(Left(ExprA::Id(v.loc, id)))
                }
                _ => Ok(Right((ExprA::Data(v, gi), args))),
            },
            expr => Ok(Right((expr, args))),
        }
    }

    /// Desugars an expression of kind:
    /// `ap (lam (x1 : A1) ... (xn : An) => a) p1 ... pn`
    fn maybe_desugar_ap(
        &mut self,
        f: ExprA,
        args: Vec1<ExprA>,
    ) -> Result<Either<ExprA, (ExprA, Vec1<ExprA>)>, DesugarError> {
        match f {
            ExprA::Fn(v, gi) => match self.lang_items_rev.get(&gi) {
                Some(LangItem::Ap) => {
                    let mut args = args.to_vec();
                    let (tele, a) = args.remove(0).into_tele_view();
                    let paths = args;
                    ensure!(tele.len() == paths.len(), DesugarError::IdWrongArity);
                    Ok(Left(ExprA::Ap(v.loc, tele, paths, a.boxed())))
                }
                _ => Ok(Right((ExprA::Fn(v, gi), args))),
            },
            expr => Ok(Right((expr, args))),
        }
    }

    pub fn desugar_expr(&mut self, expr: Expr) -> Result<ExprA> {
        match expr {
            Expr::Var(v) => {
                if let Some(uid) = self.lookup_local(&v) {
                    Ok(ExprA::Var(v, uid))
                } else if let Some((decl, ix)) = self.lookup_by_name(&v) {
                    use DeclA::*;
                    match decl {
                        Data(_data) => Ok(ExprA::Data(v, ix)),
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
                    let loc = bind.loc() + ret.loc();
                    ExprA::Lam(loc, bind.boxed(), Box::new(ret))
                });
                Ok(lam)
            }
            Expr::App(f, args) => {
                let f = self.desugar_expr(*f)?;
                let args = args.try_mapped(|e| self.desugar_expr(e))?;
                match self.maybe_desugar_id(f, args)? {
                    Left(id) => Ok(id),
                    Right((f, args)) => match self.maybe_desugar_ap(f, args)? {
                        Left(id) => Ok(id),
                        Right((f, args)) => Ok(ExprA::App(box f, args)),
                    },
                }
                // Ok(ExprA::App(box f, args))
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
            Expr::Match(exprs, cases) => {
                let exprs = exprs
                    .into_iter()
                    .map(|expr| self.desugar_expr(expr))
                    .collect::<Result<Vec<_>>>()?;
                let cases = cases
                    .into_iter()
                    .map(|case| self.desugar_case(case))
                    .collect::<Result<Vec<_>>>()?;
                Ok(ExprA::Match(Match::new(
                    Vec1::try_from_vec(exprs).unwrap(),
                    cases,
                )))
            }
            // literals are passed directly and replaced with a term in "check" stage
            Expr::Lit(loc, lit) => Ok(ExprA::Lit(loc, lit)),
            Expr::Tuple(loc, es) => {
                let es = es
                    .into_iter()
                    .map(|e| self.desugar_expr(e))
                    .collect::<Result<Vec<_>>>()?;
                Ok(ExprA::Tuple(loc, es))
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

        // TODO:
        // let args = Vec1::try_from_vec(
        //     tele.iter()
        //         .map(|bind| ExprA::Var(bind.ident(), bind.name))
        //         .collect::<Vec<_>>(),
        // )
        // .unwrap();
        // Here we represent each construction as a function declaration with the result of
        // fully applied constructor: `fn C x y := C' x y`
        // self.insert_decl(DeclA::Fn(FuncA {
        //     id: con.name.clone(),
        //     ty: None,
        //     expr: ExprA::lam_tele(
        //         tele,
        //         ExprA::App(box ExprA::Cons(con.name.clone(), data_ix), args),
        //     ),
        // }))?;
        self.insert_decl(DeclA::Cons(ConsInfoA::new(ident.loc, ident, tele, data_ix)))?;
        Ok(())
    }

    fn collect_lang_items(&mut self, meta_attrs: Vec<MetaAttr>, gi: GI) {
        for ma in meta_attrs {
            if let MetaAttr::Struct(ms) = ma {
                for (name, value) in ms {
                    let item = LangItem::from_str(&value)
                        .expect(&format!("unknown lang item '{}'", value));
                    if name.text == "lang" {
                        self.lang_items
                            .entry(item)
                            .and_modify(|gi_old| {
                                panic!("duplicated lang item: {}, previous: {}", gi, gi_old)
                            })
                            .or_insert(gi);
                        self.lang_items_rev.insert(gi, item);
                    }
                }
            }
        }
    }

    pub fn desugar_decl(&mut self, decl: Decl) -> Result<DeclA> {
        debug!(target: "desugar", "Desugaring decl: {}\n{:?}", decl.name(), &decl);
        match decl {
            Decl::Data(Data {
                sig,
                mut cons,
                universe,
                meta_attrs,
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
                let gi = res?;

                cons.reverse();
                let res = self.desugar_cons(global_id - 1, cons);
                if res.is_err() {
                    self.remove_last_decl();
                }
                self.exit_local_scope();
                res?;
                self.collect_lang_items(meta_attrs, gi);
                Ok(data_decl)
            }
            Decl::Fn(Func {
                name,
                params,
                ret_ty,
                body,
                meta_attrs,
            }) => {
                let body_new = params.clone().to_lam(body);
                let ty_new = if let Some(rt) = ret_ty {
                    params.to_pi_with(rt)
                } else {
                    params.to_pi_with(Expr::Hole(name.loc))
                };
                self.ensure_no_local_scopes();
                let res: Result<_> = try {
                    let ty = self.desugar_expr(ty_new)?;
                    let partial_decl = DeclA::Fn(FuncA::new(name, None, Some(ty))); // TODO: get rid of Option?
                    let gi = self.insert_decl(partial_decl)?;
                    // The `insert_decl` call committed information about metas to the state,
                    // but since we haven't parsed the body yet, there can be more metas potentially.
                    // So, we're postponing the commit after the definition is fully desugared.
                    self.cur_meta_id.pop();
                    let expr = self.desugar_expr(body_new)?;
                    (expr, gi)
                };
                let (expr, gi) = res?;
                let decl = self.decls.last_mut().unwrap().as_func_mut();
                decl.expr = Some(expr);
                let func = decl.clone();
                self.cur_meta_id.push(Default::default());
                self.clear_local();
                self.collect_lang_items(meta_attrs, gi);
                Ok(DeclA::Fn(func))
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
    use crate::syntax::abs::Expr::Data;
    use crate::syntax::desugar::desugar_prog;
    use crate::syntax::parser::Parser;
    use crate::syntax::Plicitness::Explicit;
    use crate::syntax::{abs, Ident, Loc, Universe};
    use itertools::Itertools;
    use vec1::{vec1, Vec1};

    #[test]
    fn test_desugar() {
        use ExprA::{App, Match, Meta, Pi, Var};
        let mut parser = Parser::default();
        let state = desugar_prog(
            parser
                .parse_prog(
                    r#"
data Nat : Type
    | Z
    | S Nat

fn foo (p : Nat) := match p {
    | Z => (lam f : Nat -> Nat => f p) (lam n : Nat => n)
    | S n => n
}
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
                            Some(ExprA::Data(Ident::new("Nat", 33..36), 0)),
                            Loc::new(33, 36)
                        )],
                        0
                    )),
                ),
                (
                    "foo".to_owned(),
                    DeclA::Fn(FuncA::new(
                        Ident::new("foo", Loc::new(41, 44),),
                        Some(ExprA::Lam(
                            Loc::default(),
                            Bind {
                                licit: Explicit,
                                name: 0,
                                ty: box Some(Data(
                                    Ident {
                                        loc: Loc::new(50, 53),
                                        text: "Nat".to_owned()
                                    },
                                    0
                                )),
                                ident: Ident::new("p", Loc::new(46, 47))
                            },
                            box Match(abs::Match::new(
                                vec1![Var(
                                    Ident {
                                        text: "p".to_owned(),
                                        loc: Loc::default()
                                    },
                                    0
                                )],
                                vec![
                                    CaseA {
                                        tele: Default::default(),
                                        patterns: vec![PatA::Cons(
                                            false,
                                            ConHead {
                                                name: Ident {
                                                    text: "Z".to_owned(),
                                                    loc: Loc::default()
                                                },
                                                cons_gi: 1
                                            },
                                            vec![]
                                        )],
                                        body: Some(App(
                                            box ExprA::Lam(
                                                Loc::new(89, 111),
                                                Bind {
                                                    licit: Explicit,
                                                    name: 1,
                                                    ty: box Some(ExprA::Pi(
                                                        Loc::new(93, 103),
                                                        Bind {
                                                            licit: Explicit,
                                                            name: 1,
                                                            ty: box Some(Data(
                                                                Ident {
                                                                    loc: Loc::new(93, 96),
                                                                    text: "Nat".to_owned()
                                                                },
                                                                0
                                                            )),
                                                            ident: Ident::new("1", Loc::default())
                                                        },
                                                        box Data(
                                                            Ident {
                                                                loc: Loc::default(),
                                                                text: "Nat".to_owned()
                                                            },
                                                            0
                                                        )
                                                    )),
                                                    ident: Ident::new("f", Loc::default())
                                                },
                                                box ExprA::App(
                                                    box ExprA::Var(
                                                        Ident {
                                                            loc: Loc::default(),
                                                            text: "f".to_owned()
                                                        },
                                                        1
                                                    ),
                                                    Vec1::new(ExprA::Var(
                                                        Ident {
                                                            loc: Loc::default(),
                                                            text: "p".to_owned()
                                                        },
                                                        0
                                                    ))
                                                )
                                            ),
                                            Vec1::new(ExprA::Lam(
                                                Loc::default(),
                                                Bind {
                                                    licit: Explicit,
                                                    name: 1,
                                                    ty: box Some(Data(
                                                        Ident {
                                                            loc: Loc::default(),
                                                            text: "Nat".to_owned()
                                                        },
                                                        0
                                                    )),
                                                    ident: Ident::new("n", Loc::default())
                                                },
                                                box ExprA::Var(
                                                    Ident {
                                                        loc: Loc::default(),
                                                        text: "n".to_owned()
                                                    },
                                                    1
                                                )
                                            ))
                                        ))
                                    },
                                    CaseA {
                                        tele: Default::default(),
                                        patterns: vec![PatA::Cons(
                                            false,
                                            ConHead {
                                                name: Ident {
                                                    text: "S".to_owned(),
                                                    loc: Loc::default()
                                                },
                                                cons_gi: 2
                                            },
                                            vec![PatA::Var(1)]
                                        )],
                                        body: Some(Var(
                                            Ident {
                                                text: "n".to_owned(),
                                                loc: Loc::default()
                                            },
                                            1
                                        ))
                                    }
                                ]
                            ))
                        )),
                        Some(Pi(
                            Loc::new(50, 44),
                            Bind::identified(
                                Explicit,
                                0,
                                box Some(Data(Ident::new("Nat", Loc::new(50, 53)), 0)),
                                Ident::new("p", Loc::new(46, 47))
                            ),
                            box Meta(Ident::new("hole0", Loc::new(41, 44)), 0)
                        )),
                    )),
                )
            ]
        );
    }
}
