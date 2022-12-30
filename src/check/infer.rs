use crate::check::state::TypeCheckState;
use crate::check::{Clause, Error, LshProblem, Result};
use crate::ensure;
use crate::syntax::abs::{AppView, Expr, Match};
use crate::syntax::core::{self, Boxed, Closure, Tele};
use crate::syntax::core::{Bind, DataInfo, Decl, Elim, Term, TermInfo, ValData, Var};
use crate::syntax::surf::{nat_to_term, Literal};
use crate::syntax::{abs, ConHead, Ident, LangItem, Loc, Universe, GI};

impl TypeCheckState {
    /// Infer the type of the expression. Returns evaluated term and its type.
    pub fn infer(&mut self, input_term: &Expr) -> Result<(TermInfo, Term)> {
        if !self.trace_tc {
            return self.infer_impl(input_term);
        }
        let depth_ws = self.tc_depth_ws();
        self.tc_deeper();
        debug!("{}⊢ {} ↓", depth_ws, input_term);
        let (evaluated, inferred_ty) = self.infer_impl(input_term).map_err(|e| {
            debug!("{}Error inferring {}", depth_ws, input_term);
            e
        })?;
        debug!(
            "{}⊢ {} ↓ {} ⇝ {}",
            depth_ws, input_term, inferred_ty, evaluated.ast
        );
        self.tc_shallower();
        Ok((evaluated, inferred_ty))
    }

    fn infer_impl(&mut self, abs: &Expr) -> Result<(TermInfo, Term)> {
        let abs = match abs {
            Expr::Pi(loc, bind, body) => {
                let (bind_ty_ch, bind_ty_ty) = self.infer((*bind.ty).as_ref().unwrap())?;
                let bind_ch = bind.clone().map_term(|_| bind_ty_ch.ast);
                let bind_ty_ty = bind_ty_ty;
                self.gamma.push(bind_ch);
                let (body_ch, body_ty) = self.infer(body)?;
                let body_ty = body_ty;
                let bind_ch = self.gamma.pop().expect("Γ is empty");
                let pi_ty = match (bind_ty_ty, body_ty) {
                    (Term::Universe(a), Term::Universe(b)) => Term::Universe(a.max(b)),
                    (a, b) => return Err(Error::InvalidPi(box a, box b)),
                };
                return Ok((
                    Term::Pi(bind_ch.map_term(|x| box x), Closure::Plain(box body_ch.ast)).at(*loc),
                    pi_ty.into(),
                ));
            }
            Expr::Universe(loc, level) => {
                let me = Term::universe(*level).at(*loc);
                return Ok((me, Term::universe(Universe(level.0 + 1))));
            }
            // TODO: infer match
            abs => abs.clone(),
        };
        let view = abs.into_app_view();
        let (head, mut ty) = self.infer_head(&view.fun)?;

        match &head.ast {
            Term::Data(ValData { def, args }) => {
                debug_assert!(args.is_empty());
                let info = match &self.sigma[*def] {
                    Decl::Data(data) => data,
                    _ => {
                        unreachable!()
                    }
                };
                self.infer_decl(
                    view,
                    &head,
                    *def,
                    Ident::new("<data>"),
                    info.signature.clone(),
                    |_, gi, args| Term::data(ValData::new(gi, args)),
                )
            }
            Term::Cons(ConHead { name, cons_gi: def }, args) => {
                // debug_assert!(args.is_empty());
                if !args.is_empty() {
                    return Ok((head, ty));
                }
                let info = match &self.sigma[*def] {
                    Decl::Cons(cons) => cons,
                    _ => {
                        unreachable!()
                    }
                };
                self.infer_decl(
                    view,
                    &head,
                    *def,
                    name.clone(),
                    info.signature.clone(),
                    |name, gi, args| Term::cons(ConHead::new(name, gi), args),
                )
            }
            _ => {
                let mut elims = Vec::with_capacity(view.args.len());
                for arg in view.args {
                    let ty_val = ty;
                    let res: Result<_> = ty_val
                        .into_pi()
                        .map_left(|e| Error::NotPi(e, arg.loc()))
                        .into();
                    let (param, clos) = res?;
                    let param_ty = *param.ty;
                    let arg = self.check(&arg, &param_ty)?;
                    ty = clos.instantiate_with(arg.ast.clone(), self);
                    elims.push(Elim::app(arg.ast));
                }
                Ok((head.map_ast(|t| t.apply_elim(elims)), ty))
            }
        }
    }

    fn infer_decl(
        &mut self,
        view: AppView,
        head: &TermInfo,
        def: GI,
        ident: Ident,
        decl_signature: Term,
        decl_cons: impl FnOnce(Ident, GI, Vec<Term>) -> Term,
    ) -> Result<(TermInfo, Term)> {
        let params_len = decl_signature.tele_len();
        let mut ty = decl_signature;

        let args_len = view.args.len();

        let mut args = vec![];
        for arg in view.args {
            let ty_val = ty;
            let res: Result<_> = ty_val
                .into_pi()
                .map_left(|e| Error::NotPi(e, arg.loc()))
                .into();
            let (param, clos) = res?;
            let param_ty = *param.ty;
            let arg = self.check(&arg, &param_ty)?;
            ty = clos.instantiate_with(arg.ast.clone(), self);
            args.push(arg.ast);
        }

        if params_len == args_len {
            Ok((head.clone().map_ast(|_| decl_cons(ident, def, args)), ty))
        } else {
            Ok((
                head.clone()
                    .map_ast(|_| Term::def(def, ident, args.into_iter().map(Elim::app).collect())),
                ty,
            ))
        }
    }

    pub fn type_of_decl(&self, decl: GI) -> Result<TermInfo> {
        let decl = self.def(decl);
        match decl {
            Decl::Data(DataInfo {
                loc,
                params,
                universe: level,
                ..
            }) => Ok(Term::pi_from_tele(params.clone(), Term::universe(*level)).at(*loc)),
            Decl::Cons(cons) => {
                Ok(cons.signature.clone().at(cons.loc()))
                // let params = &cons.params;
                // let data = cons.data;
                // let data_tele = match self.def(data) {
                //     Decl::Data(i) => &i.params,
                //     _ => unreachable!(),
                // };
                // let params_len = params.len();
                // let range = params_len..params_len + data_tele.len();
                // let tele = data_tele
                //     .iter()
                //     .cloned()
                //     // .map(Bind::into_implicit)
                //     .chain(params.iter().cloned())
                //     .collect();
                // let _ident = self.def(data).def_name().clone();
                // let elims = range.rev().map(Term::from_dbi).collect();
                // let ret = Term::data(ValData::new(data, elims));
                // Ok(Term::pi_from_tele(tele, ret).at(cons.loc()))
            }
            Decl::Proj(_proj) => {
                unimplemented!()
            }
            Decl::Func(func) => Ok(func.signature.clone().at(func.loc)),
        }
    }

    fn infer_head(&mut self, input_term: &Expr) -> Result<(TermInfo, Term)> {
        if !self.trace_tc {
            return self.infer_head_impl(input_term);
        }
        let depth_ws = self.tc_depth_ws();
        self.tc_deeper();
        let (evaluated, inferred_ty) = self.infer_head_impl(input_term).map_err(|e| {
            debug!("{} Error while head-inferring {}", depth_ws, input_term);
            e
        })?;
        debug!(
            "{}⊢ {} : {} → {}",
            depth_ws, input_term, inferred_ty, evaluated.ast
        );
        self.tc_shallower();
        Ok((evaluated, inferred_ty))
    }

    fn check_bind(&mut self, abs_bind: abs::Bind) -> Result<Bind> {
        Ok(Bind::identified(
            abs_bind.licit,
            abs_bind.name,
            self.infer(abs_bind.ty.as_ref().unwrap())?.0.ast,
            abs_bind.ident,
        ))
    }

    fn infer_head_impl(&mut self, abs: &Expr) -> Result<(TermInfo, Term)> {
        use Expr::*;
        match abs {
            Proj(_id, _def) => unimplemented!("projections"),
            Fn(id, def) => self
                .type_of_decl(*def)
                .map(|ty| (Term::simple_def(*def, id.clone()).at(id.loc), ty.ast)),
            Cons(id, def) => self.type_of_decl(*def).map(|ty| {
                (
                    Term::cons(ConHead::new(id.clone(), *def), vec![]).at(id.loc),
                    ty.ast,
                )
            }),
            Data(id, def) => self
                .type_of_decl(*def)
                .map(|ty| (Term::data(ValData::new(*def, vec![])).at(id.loc), ty.ast)),
            Lam(loc, bind, body) => {
                let bind_checked = Bind::identified(
                    bind.licit,
                    bind.name,
                    self.infer((*bind.ty).as_ref().unwrap())?.0.ast,
                    bind.ident.clone(),
                );
                self.gamma.push(bind_checked.clone());
                let (body_term, body_ty) = self.infer(body)?;
                self.gamma.pop();
                let ty = Term::pi_from_tele(Tele(vec![bind_checked.clone()]), body_ty);
                let lam_checked =
                    Term::lam(bind_checked.map_term(Box::new), body_term.ast).at(*loc);
                Ok((lam_checked, ty))
            }
            Var(loc, var) => {
                let lb = self.local_by_id(*var);
                Ok((lb.val.at(loc.loc), lb.bind.ty))
            }
            Meta(ident, mi) => {
                let ty = Term::meta(*mi, vec![]);
                let tyty = self.fresh_meta();
                Ok((ty.at(ident.loc), tyty))
            }
            Id(loc, id) => {
                // ap (lam (x : A) (y : B) (z : C) => f) (refl a, refl b, refl c) : Id (A -> B -> C) d1 d2
                // Id (A -> B -> C) d1 d2 (refl a, refl b, refl c) : Type
                ensure!(
                    id.tele.len() == id.paths.len(),
                    Error::IdTelePathsLenMismatch
                );
                let mut ps_checked = Vec::with_capacity(id.paths.len());
                for (x, p) in id.tele.iter().zip(id.paths.iter()) {
                    let (p, p_ty) = self.infer(p)?;
                    let id = p_ty
                        .as_id()
                        .ok_or_else(|| Error::NotId(p_ty.clone().boxed(), p.loc()))?;
                    ensure!(
                        id.tele.is_empty() && id.paths.is_empty(),
                        Error::IdTeleOrSubstsNotEmpty
                    );
                    let x_checked = self.check_bind(x.clone())?;
                    let x_ty = &x_checked.ty;
                    let id_ty = &id.ty;
                    let val = x_ty.clone();
                    let val1 = *id_ty.clone();
                    self.subtype(&val, &val1)?;
                    // self.lets.0.push(Let::new(p));
                    ps_checked.push(p.ast);
                    self.gamma.push(x_checked);
                }
                let (id_checked, id_ty) = self.infer(&id.ty)?;
                let id_checked_val = id_checked.ast.clone();
                let a1 = self.check(&id.a1, &id_checked_val)?.ast;
                let a2 = self.check(&id.a2, &id_checked_val)?.ast;
                let tele = self.gamma.popn(id.tele.len()).into_tele();
                Ok((
                    Term::from(core::Id::new(tele, id_checked.ast, ps_checked, a1, a2)).at(*loc),
                    id_ty,
                ))
            }
            Ap(loc, tele, paths, t) => {
                let mut ps_checked = Vec::with_capacity(paths.len());
                for (x, p) in tele.iter().zip(paths.iter()) {
                    let (p, p_ty) = self.infer(p)?;
                    let id = p_ty
                        .as_id()
                        .ok_or_else(|| Error::NotId(p_ty.clone().boxed(), p.loc()))?;
                    ensure!(
                        id.tele.is_empty() && id.paths.is_empty(),
                        Error::IdTeleOrSubstsNotEmpty
                    );
                    let x_checked = self.check_bind(x.clone())?;
                    let x_ty = &x_checked.ty;
                    let id_ty = &id.ty;
                    let val = x_ty.clone();
                    let val1 = *id_ty.clone();
                    self.subtype(&val, &val1)?;
                    ps_checked.push(p.ast);
                    self.gamma.push(x_checked);
                }

                let (t_checked, t_ty) = self.infer(t)?;
                let tele_checked = self.gamma.popn(tele.len()).into_tele();

                Ok((
                    Term::ap(
                        tele_checked.clone(),
                        ps_checked.clone(),
                        t_checked.ast.clone(),
                    )
                    .at(*loc),
                    Term::from(core::Id::new(
                        tele_checked,
                        t_ty,
                        ps_checked,
                        t_checked.ast.clone(),
                        t_checked.ast,
                    )),
                ))
            }
            Lit(loc, Literal::Nat(n)) => {
                let nat_gi = *self.lang_items.get(&LangItem::Nat).unwrap();
                let ty = Term::data(ValData::new(nat_gi, vec![]));
                let nat_z_gi = *self.lang_items.get(&LangItem::NatZ).unwrap();
                let nat_z_decl = &self.sigma[nat_z_gi].as_cons();
                let nat_s_gi = *self.lang_items.get(&LangItem::NatS).unwrap();
                let nat_s_decl = &self.sigma[nat_s_gi].as_cons();
                let nat_e = nat_to_term(
                    *n,
                    ConHead::new(nat_z_decl.name.clone(), nat_z_gi),
                    ConHead::new(nat_s_decl.name.clone(), nat_s_gi),
                );
                Ok((nat_e.at(loc.clone()), ty))
            }
            e => Err(Error::NotHead(e.clone())),
        }
    }

    pub(crate) fn check(&mut self, input_term: &Expr, against: &Term) -> Result<TermInfo> {
        if !self.trace_tc {
            return self.check_impl(input_term, against);
            // return match self.check_impl(input_term, against) {
            //     Err(Error::Blocked(blocked)) if blocked.is_elim() => {
            //         debug!("{}, trying another way", blocked);
            //         self.check_blocked_impl(input_term, against.clone())
            //     }
            //     x => x,
            // };
        }
        let depth_ws = self.tc_depth_ws();
        debug!("{}⊢ {} ↑? {}", depth_ws, input_term, against);
        self.tc_deeper();
        let a = self.check_impl(input_term, against);
        // let a = match self.check_impl(input_term, against) {
        //     Err(Error::Blocked(blocked)) if blocked.is_elim() => {
        //         debug!("{}, trying another way", blocked);
        //         self.check_blocked_impl(input_term, against.clone())
        //     }
        //     x => x,
        // };
        let a = a.map_err(|e| {
            debug!("{}Error checking {} ↑ {}", depth_ws, input_term, against);
            e
        })?;
        debug!("{}⊢ {} ↑ {} ~> {}", depth_ws, input_term, against, a.ast);
        self.tc_shallower();
        Ok(a)
    }

    fn check_impl(&mut self, abs: &Expr, against: &Term) -> Result<TermInfo> {
        if let Some(gi) = abs.get_gi() {
            if let Some(decl) = self.sigma.get(gi).cloned() {
                let ty = decl.def_type();
                let ident = decl.ident();
                let simplified = ty;
                let loc = ident.loc;
                let res = match decl {
                    Decl::Data(_) => Ok(Term::data(ValData::new(gi, vec![])).at(loc)),
                    Decl::Cons(_) => Ok(Term::cons(ConHead::new(ident, gi), vec![]).at(loc)),
                    _ => Ok(Term::def(gi, ident, vec![]).at(loc)),
                };
                self.subtype(&simplified, against)?;
                return res;
            }
        }

        match (abs, against) {
            (Expr::Universe(info, lower), Term::Universe(upper)) => {
                if upper > lower {
                    Ok(Term::universe(*lower).at(*info))
                } else {
                    Err(Error::DifferentUniverse(
                        abs.loc(),
                        Universe(lower.0 + 1),
                        *upper,
                    ))
                }
            }
            (Expr::Pi(info, bind, ret), Term::Universe(..)) => {
                let bind_ty = self.check(&bind.ty.clone().unwrap(), against)?;
                let new = Bind::identified(bind.licit, bind.name, bind_ty.ast, bind.ident.clone());
                self.gamma.push(new);
                let ret_ty = self.check(ret, against)?;
                let bind_ty = self.gamma.pop().expect("Bad index");
                let term = Term::pi2(bind_ty.boxed(), Closure::plain(ret_ty.ast));
                Ok(term.at(*info))
            }
            (Expr::Lam(_info, bind, ret), Term::Pi(bind_pi, ret_pi)) => {
                let (bind_ty, _bind_ty_ty) = self.infer((*bind.ty).as_ref().unwrap())?;
                let val1 = bind_ty.ast.clone();
                let val2 = *bind_pi.ty.clone();
                self.subtype(&val1, &val2)?;
                let Closure::Plain(ret_pi) = ret_pi;
                let bind_new =
                    Bind::identified(bind.licit, bind.name, bind_ty.ast, bind.ident.clone());
                self.gamma.push(bind_new.clone());
                let body = self.check(ret, &ret_pi)?;
                self.gamma.pop();
                Ok(Term::lam(bind_new.boxed(), body.ast).at(bind_ty.loc))
            }
            (Expr::Match(m), against) => self.check_match(m, against.clone()),
            (expr, anything) => self.check_fallback(expr.clone(), anything),
        }
    }

    pub fn check_match(&mut self, m: &Match, target: Term) -> Result<TermInfo> {
        let vars =
            m.xs.iter()
                .map(|x| self.infer(x).map(|x| x.0))
                .collect::<Result<Vec<_>>>()?;
        let vars = vars
            .into_iter()
            .map(|ti| match ti.ast {
                Term::Var(Var::Bound(idx), _) => idx,
                _ => unimplemented!("Match on non-var"),
            })
            .collect::<Vec<_>>();
        let clauses = m
            .cases
            .iter()
            .map(|c| Clause::new(c.patterns.clone(), c.body.clone()))
            .collect::<Vec<_>>();
        let mut lhs = LshProblem::new(vars, clauses, target);
        lhs.init(self)?;
        let case_tree = lhs.check(self)?;
        debug!("{}⊢ Checked case tree: {}", self.indentation, case_tree);
        Ok(case_tree.into_term().at(Loc::default()))
    }

    pub fn check_fallback(&mut self, expr: Expr, expected_type: &Term) -> Result<TermInfo> {
        let (evaluated, inferred) = self.infer(&expr)?;
        self.subtype(&inferred, expected_type)
            .map_err(|e| e.wrap(expr.loc()))?;
        Ok(evaluated)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::parser::Parser;

    use crate::syntax::core::ValData;
    use crate::syntax::desugar::desugar_prog;
    use crate::syntax::Loc;
    use crate::{assert_err, assert_term_eq, pct, pe, typeck};

    #[test]
    fn test_check_basic() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut des = desugar_prog(p.parse_prog(
            r#"
            data T : Type
        "#,
        )?)?;
        let mut env = TypeCheckState::default();
        env.check_prog(des.clone())?;
        env.trace_tc = true;
        env.indentation_size(2);

        let ty = pct!(p, des, env, "T -> T");
        env.check(&pe!(p, des, "lam (y : T) => y"), &ty)?;

        let ty = pct!(p, des, env, "(ff : T -> T) -> (x : T) -> T");
        env.check(&pe!(p, des, "lam (f : T -> T) (y : T) => f y"), &ty)?;

        let ty = pct!(p, des, env, "Type");
        env.check(&pe!(p, des, "(ff : T -> T) -> (x : T) -> T"), &ty)?;

        let ty = pct!(p, des, env, "Type2");
        env.check(
            &pe!(p, des, "(T : Type1) -> (ff : T -> T) -> (x : T) -> T"),
            &ty,
        )?;

        let ty = pct!(p, des, env, "Type1");
        env.check(&pe!(p, des, "Type0"), &ty)?;

        let ty = pct!(p, des, env, "Type0");
        assert_err!(
            env.check(&pe!(p, des, "Type1"), &ty),
            Error::DifferentUniverse(Loc::new(0, 5), Universe(2), Universe(0))
        );

        let ty = pct!(p, des, env, "T");
        assert_err!(
            env.check(&pe!(p, des, "(ff : T -> T) -> (x : T) -> x"), &ty),
            Error::InvalidPi(
                box Term::Universe(Universe(0)),
                box Term::Data(ValData::new(0, vec![]))
            )
        );

        Ok(())
    }

    #[test]
    fn test_infer() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        let mut des = desugar_prog(p.parse_prog(
            r#"
            data Bool : Type
               | true
               | false

            fn fmap (A : Type) (B : Type) (f : A -> B) (x : A) : B := f x
            fn bool_id (b : Bool) := b
            fn id (A : Type) (a : A) := a
            fn bool := true
            fn idb := id _ bool
            fn deep (f : (A : Type) -> A -> A -> A) (x : Bool) := (lam (y : _) => f _ y x) x
            fn deep' (f : (A : Type) -> A -> A -> A) (x : Bool) := (lam (y : _) => f _ x y) x
       "#,
        )?)?;

        env.trace_tc = true;
        env.check_prog(des.clone())?;

        println!(
            "{}",
            match &env.sigma[3] {
                Decl::Func(f) => {
                    &f.signature
                }
                _ => panic!(),
            }
        );

        let ty = pct!(p, des, env, "Bool");
        env.check(&pe!(p, des, "bool"), &ty)?;

        let ty = pct!(p, des, env, "Type");
        env.check(&pe!(p, des, "Bool"), &ty)?;

        let ty = pct!(p, des, env, "(A : Type) -> (a : A) -> A");
        env.check(&pe!(p, des, "id"), &ty)?;

        let ty = pct!(p, des, env, "Bool");
        env.check(&pe!(p, des, "idb"), &ty)?;

        let ty = pct!(
            p,
            des,
            env,
            "(f : (A : Type) -> A -> A -> A) -> (x : Bool) -> Bool"
        );
        env.check(&pe!(p, des, "deep"), &ty)?;
        env.check(&pe!(p, des, "deep'"), &ty)?;

        Ok(())
    }

    #[test]
    fn test_data() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        let mut des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | O
            | S Nat

        data List (T : Type) : Type1
            | nil
            | cons T (List T)

        fn main := cons _ (S (S O)) (cons _ (S O) (cons _ O (nil _)))
       "#,
        )?)?;

        env.check_prog(des.clone())?;
        env.indentation_size(2);

        let ty = pct!(p, des, env, "Type -> Type1");
        env.check(&pe!(p, des, "List"), &ty)?;
        env.infer(&pe!(p, des, "List"))?.1;

        let ty = pct!(p, des, env, "(T : Type) -> List T");
        env.check(&pe!(p, des, "nil"), &ty)?;

        let ty = pct!(
            p,
            des,
            env,
            "(T : Type) -> (x : T) -> (xs : List T) -> (List T)"
        );
        env.check(&pe!(p, des, "cons"), &ty)?;

        let ty = pct!(p, des, env, "List Nat");
        env.check(&pe!(p, des, "nil Nat"), &ty)?;

        let ty = pct!(p, des, env, "List Nat");
        env.check(
            &pe!(
                p,
                des,
                "cons Nat (S (S O)) (cons Nat (S O) (cons Nat O (nil Nat)))"
            ),
            &ty,
        )?;

        env.trace_tc = true;

        typeck!(
            p,
            des,
            env,
            "cons _ (S (S O)) (cons _ (S O) (cons _ O (nil _)))",
            "List Nat"
        );

        Ok(())
    }

    #[test]
    fn test_complex_data() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let mut des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | O
            | S Nat

        data Bool : Type
            | true
            | false

        data Error : Type
            | err1
            | err2

        data Result (T : Type) (E : Type) : Type1
            | ok T
            | err E

        data Sigma (A : Type) (B : A -> Type) : Type1
            | mkSigma (x : A) (y : B x)
       "#,
        )?)?;
        env.check_prog(des.clone())?;

        typeck!(p, des, env, "ok", "(T E : Type) -> T -> Result T E");

        typeck!(p, des, env, "ok _ Nat true", "Result Bool Nat");

        typeck!(p, des, env, "err", "(T E : Type) -> E -> Result T E");

        typeck!(
            p,
            des,
            env,
            "mkSigma",
            "(A : Type)->(B : A -> Type) -> (x : A) -> (y : B x) -> Sigma A B"
        );

        typeck!(
            p,
            des,
            env,
            "mkSigma _ _ (S O) false",
            "Sigma Nat (lam (x : Nat) => Bool)"
        );
        Ok(())
    }

    #[test]
    fn test_infer_literal() -> eyre::Result<()> {
        use crate::check::TypeCheckState;
        use crate::error::Error;
        use crate::syntax::core::pretty;
        use crate::syntax::desugar::desugar_prog;
        use crate::syntax::parser::Parser;
        use crate::{pct, pe, typeck};

        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        env.trace_tc = true;
        let mut des = desugar_prog(p.parse_prog_with_std(r#""#, None)?)?;
        let result: Result<(), Error> = try {
            env.check_prog(des.clone())?;
            env.trace_tc = true;

            typeck!(p, des, env, "0", "Nat");
            typeck!(p, des, env, "1", "Nat");
            assert_term_eq!(p, des, env, "1", "suc zero");
            assert_term_eq!(p, des, env, "3", "suc (suc (suc zero))");
        };
        if let Err(e) = result {
            println!("{}", pretty(&e, &env));
            return Err(e.into());
        }
        Ok(())
    }
}
