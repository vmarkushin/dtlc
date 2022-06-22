use crate::check::state::TypeCheckState;
use crate::check::{Clause, Error, LshProblem, Result, Unify};
use crate::syntax::abs::{AppView, Expr};
use crate::syntax::core::{Bind, DataInfo, Decl, Elim, Term, TermInfo, Val, ValData};
use crate::syntax::core::{Closure, Ctx};
use crate::syntax::{ConHead, Ident, Loc, Universe, GI};

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
                let bind_ty_ty = self.simplify(bind_ty_ty)?;
                self.gamma.push(bind_ch);
                let (body_ch, body_ty) = self.infer(body)?;
                let body_ty = self.simplify(body_ty)?;
                let bind_ch = self.gamma.pop().expect("Γ is empty");
                let pi_ty = match (bind_ty_ty, body_ty) {
                    (Val::Universe(a), Val::Universe(b)) => Val::Universe(a.max(b)),
                    (a, b) => return Err(Error::InvalidPi(box a, box b)),
                };
                return Ok((
                    Term::Whnf(Val::Pi(
                        bind_ch.map_term(|x| box x),
                        Closure::Plain(box body_ch.ast),
                    ))
                    .at(*loc),
                    pi_ty.into(),
                ));
            }
            Expr::Universe(loc, level) => {
                let me = Term::universe(*level).at(*loc);
                return Ok((me, Term::universe(Universe(level.0 + 1))));
            }
            abs => abs.clone(),
        };
        let view = abs.into_app_view();
        let (head, mut ty) = self.infer_head(&view.fun)?;

        match &head.ast {
            Term::Whnf(Val::Data(ValData { def, args })) => {
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
                    Ident::new("<data>", Loc::default()),
                    info.signature.clone(),
                    |_, gi, args| Term::data(ValData::new(gi, args)),
                )
            }
            Term::Whnf(Val::Cons(ConHead { name, cons_gi: def }, args)) => {
                debug_assert!(args.is_empty());
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
                    let ty_val = self.simplify(ty)?;
                    let res: Result<_> = ty_val
                        .into_pi()
                        .map_left(|e| Error::NotPi(Term::Whnf(e), arg.loc()))
                        .into();
                    let (param, clos) = res?;
                    let param_ty = self.simplify(*param.ty)?;
                    let arg = self.check(&arg, &param_ty)?;
                    ty = clos.instantiate(arg.ast.clone());
                    // TODO: nahuya?
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
            let ty_val = self.simplify(ty)?;
            let res: Result<_> = ty_val
                .into_pi()
                .map_left(|e| Error::NotPi(Term::Whnf(e), arg.loc()))
                .into();
            let (param, clos) = res?;
            let param_ty = self.simplify(*param.ty)?;
            let arg = self.check(&arg, &param_ty)?;
            ty = clos.instantiate(arg.ast.clone());
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
            "{}\u{22A2} {} : {} \u{2192} {}",
            depth_ws, input_term, inferred_ty, evaluated.ast
        );
        self.tc_shallower();
        Ok((evaluated, inferred_ty))
    }

    fn infer_head_impl(&mut self, abs: &Expr) -> Result<(TermInfo, Term)> {
        use Expr::*;
        match abs {
            Proj(id, def) | Fn(id, def) => self
                .type_of_decl(*def)
                .map(|ty| (Term::simple_def(*def, id.clone()).at(id.loc), ty.ast)),
            Cons(id, def) => self.type_of_decl(*def).map(|ty| {
                (
                    Term::cons(ConHead::new(id.clone(), *def), vec![]).at(id.loc),
                    ty.ast,
                )
            }),
            Def(id, def) => self
                .type_of_decl(*def)
                .map(|ty| (Term::data(ValData::new(*def, vec![])).at(id.loc), ty.ast)),
            Lam(loc, bind, body) => {
                let bind_checked = Bind::new(
                    bind.licit,
                    bind.name,
                    self.infer((*bind.ty).as_ref().unwrap())?.0.ast,
                    bind.loc,
                );
                self.gamma.push(bind_checked.clone());
                let (body_term, body_ty) = self.infer(body)?;
                self.gamma.pop();
                let ty = Term::pi_from_tele(vec![bind_checked.clone()], body_ty);
                let lam_checked =
                    Term::lam(bind_checked.map_term(Box::new), body_term.ast).at(*loc);
                Ok((lam_checked, ty))
            }
            Var(loc, var) => {
                let (bind, val) = self.local_by_id(*var);
                Ok((val.at(loc.loc), bind.ty))
            }
            Meta(ident, mi) => {
                let ty = Term::meta(*mi, vec![]);
                let tyty = self.fresh_meta();
                Ok((ty.at(ident.loc), tyty))
            }
            e => Err(Error::NotHead(e.clone())),
        }
    }

    pub(crate) fn check(&mut self, input_term: &Expr, against: &Val) -> Result<TermInfo> {
        if !self.trace_tc {
            return self.check_impl(input_term, against);
        }
        let depth_ws = self.tc_depth_ws();
        debug!("{}⊢ {} ↑? {}", depth_ws, input_term, against);
        self.tc_deeper();
        let a = self.check_impl(input_term, against).map_err(|e| {
            debug!("{}Error checking {} : {}", depth_ws, input_term, against);
            e
        })?;
        debug!("{}⊢ {} ↑ {} ⇝ {}", depth_ws, input_term, against, a.ast);
        self.tc_shallower();
        Ok(a)
    }

    fn check_impl(&mut self, abs: &Expr, against: &Val) -> Result<TermInfo> {
        if let Some(gi) = abs.get_gi() {
            if let Some(decl) = self.sigma.get(gi) {
                let ty = decl.def_type();
                let ident = decl.ident();
                let whnf = self.simplify(ty)?;
                let loc = ident.loc;
                let res = match decl {
                    Decl::Data(_) => Ok(Term::data(ValData::new(gi, vec![])).at(loc)),
                    Decl::Cons(_) => Ok(Term::cons(ConHead::new(ident, gi), vec![]).at(loc)),
                    _ => Ok(Term::def(gi, ident, vec![]).at(loc)),
                };
                self.subtype(&whnf, against)?;
                return res;
            }
        }

        match (abs, against) {
            (Expr::Universe(info, lower), Val::Universe(upper)) => {
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
            (Expr::Pi(info, bind, ret), Val::Universe(..)) => {
                let bind_ty = self.check(&bind.ty.clone().unwrap(), against)?;
                let new = Bind::new(bind.licit, bind.name, bind_ty.ast, bind.loc);
                self.gamma.push(new);
                let ret_ty = self.check(&**ret, against)?;
                let bind_ty = self.gamma.pop().expect("Bad index");
                let term = Term::pi2(bind_ty.boxed(), Closure::plain(ret_ty.ast));
                Ok(term.at(*info))
            }
            (Expr::Lam(_info, bind, ret), Val::Pi(bind_pi, ret_pi)) => {
                let (bind_ty, bind_ty_ty) = self.infer((*bind.ty).as_ref().unwrap())?;
                self.subtype(
                    &self.simplify(bind_ty.ast.clone())?,
                    &self.simplify(*bind_pi.ty.clone())?,
                )?;
                let Closure::Plain(ret_pi) = ret_pi;
                let bind_new = Bind::boxing(bind.licit, bind.name, bind_ty.ast, bind_ty.loc);
                self.gamma.push(bind_new.clone().unboxed());
                let body = self.check(&*ret, &self.simplify(*ret_pi.clone())?)?;
                self.gamma.pop();
                Ok(Term::lam(bind_new, body.ast).at(bind_ty.loc))
            }
            (Expr::Match(xs, cs), against) => {
                let vars = xs
                    .iter()
                    .map(|x| self.infer(x).map(|x| x.0))
                    .collect::<Result<Vec<_>>>()?;
                let vars = vars
                    .into_iter()
                    .map(|ti| match ti.ast {
                        Term::Whnf(Val::Var(idx, _)) => idx,
                        _ => unimplemented!("Match on non-var"),
                    })
                    .collect::<Vec<_>>();
                let clauses = cs
                    .iter()
                    .map(|c| Clause::new(c.patterns.clone(), c.body.clone()))
                    .collect::<Vec<_>>();
                let mut lhs = LshProblem::new(vars, clauses, Term::Whnf(against.clone()));
                lhs.init(self)?;
                let case_tree = lhs.check(self)?;
                Ok(case_tree.into_term().at(Loc::default()))
            }
            (expr, anything) => self.check_fallback(expr.clone(), anything),
        }
    }

    pub fn check_fallback(&mut self, expr: Expr, expected_type: &Val) -> Result<TermInfo> {
        let (evaluated, inferred) = self.infer(&expr)?;
        let whnf = self.simplify(inferred)?;
        self.subtype(&whnf, expected_type)
            .map_err(|e| e.wrap(expr.loc()))?;
        Ok(evaluated)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    use crate::syntax::core::ValData;
    use crate::syntax::desugar::desugar_prog;
    use crate::syntax::Loc;
    use crate::{assert_err, dsp, pct, pe, typeck};

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

        let ty = pct!(p, des, env, "forall (ff : T -> T) (x : T), T");
        env.check(&pe!(p, des, "lam (f : T -> T) (y : T) => f y"), &ty)?;

        let ty = pct!(p, des, env, "Type");
        env.check(&pe!(p, des, "forall (ff : T -> T) (x : T), T"), &ty)?;

        let ty = pct!(p, des, env, "Type2");
        env.check(
            &pe!(p, des, "forall (T : Type1) (ff : T -> T) (x : T), T"),
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
            env.check(&pe!(p, des, "forall (ff : T -> T) (x : T), x"), &ty),
            Error::InvalidPi(
                box Val::Universe(Universe(0)),
                box Val::Data(ValData::new(0, vec![]))
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

            fn bool_id (b : Bool) := b
            fn id (A : Type) (a : A) := a
            fn bool := true
            fn idb := id _ bool
            fn deep (f : forall (A : Type), A -> A -> A) (x : Bool) := (lam (y : _) => f _ y x) x
            fn deep' (f : forall (A : Type), A -> A -> A) (x : Bool) := (lam (y : _) => f _ x y) x
       "#,
        )?)?;

        env.check_prog(des.clone())?;

        let ty = pct!(p, des, env, "Bool");
        env.check(&pe!(p, des, "bool"), &ty)?;

        let ty = pct!(p, des, env, "Type");
        env.check(&pe!(p, des, "Bool"), &ty)?;

        let ty = pct!(p, des, env, "forall (A : Type) (a : A), A");
        env.check(&pe!(p, des, "id"), &ty)?;

        let ty = pct!(p, des, env, "Bool");
        env.check(&pe!(p, des, "idb"), &ty)?;

        let ty = pct!(
            p,
            des,
            env,
            "forall (f : forall (A : Type), A -> A -> A) (x : Bool), Bool"
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

        fn main := cons Nat (S (S O)) (cons Nat (S O) (cons Nat O (nil Nat)))
       "#,
        )?)?;

        env.check_prog(des.clone())?;
        env.indentation_size(2);

        let ty = pct!(p, des, env, "Type -> Type1");
        env.check(&pe!(p, des, "List"), &ty)?;
        dsp!(env.infer(&pe!(p, des, "List"))?.1);

        let ty = pct!(p, des, env, "forall (T : Type), List T");
        env.check(&pe!(p, des, "nil"), &ty)?;

        let ty = pct!(
            p,
            des,
            env,
            "forall (T : Type) (x : T) (xs : List T), (List T)"
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

        typeck!(
            p,
            des,
            env,
            "ok",
            "forall (T : Type) (E : Type), T -> Result T E"
        );

        typeck!(p, des, env, "ok _ Nat true", "Result Bool Nat");

        typeck!(
            p,
            des,
            env,
            "err",
            "forall (T : Type) (E : Type), E -> Result T E"
        );

        typeck!(
            p,
            des,
            env,
            "mkSigma",
            "forall (A : Type) (B : A -> Type) (x : A) (y : B x), Sigma A B"
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
}
