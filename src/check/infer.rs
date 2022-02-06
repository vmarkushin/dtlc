use crate::check::state::TypeCheckState;
use crate::check::{Error, Result};
use crate::syntax::abs::Expr;
use crate::syntax::core::{Bind, DataInfo, Decl, Elim, Term, TermInfo, Val, ValData};
use crate::syntax::core::{Closure, DeBruijn};
use crate::syntax::{ConHead, Universe, GI};

impl TypeCheckState {
    /// Infer the type of the expression.
    pub fn infer(&mut self, input_term: &Expr) -> Result<(TermInfo, Term)> {
        if !self.trace_tc {
            return self.infer_impl(input_term);
        }
        let depth_ws = self.tc_depth_ws();
        self.tc_deeper();
        debug!("{}⊢ {} ↑", depth_ws, input_term);
        let (evaluated, inferred_ty) = self.infer_impl(input_term).map_err(|e| {
            debug!("{}Error inferring {}", depth_ws, input_term);
            e
        })?;
        debug!(
            "{}⊢ {} : {} → {}",
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
        let mut elims = Vec::with_capacity(view.args.len());
        for arg in view.args {
            let ty_val = self.simplify(ty)?;
            match {
                let (param, clos) = match ty_val {
                    Val::Pi(param, clos) => (param, clos),
                    e => return Err(Error::NotPi(Term::Whnf(e), arg.loc())),
                };
                let param_ty = self.simplify(*param.ty)?;
                (param_ty, clos)
            } {
                (param, clos) => {
                    let arg = self.check(&arg, &param)?;
                    ty = clos.instantiate(arg.ast.clone());
                    elims.push(Elim::app(arg.ast));
                }
            }
        }
        Ok((head.map_ast(|t| t.apply_elim(elims)), ty))
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
                let params = &cons.params;
                let data = cons.data;
                let data_tele = match self.def(data) {
                    Decl::Data(i) => &i.params,
                    _ => unreachable!(),
                };
                let params_len = params.len();
                let range = params_len..params_len + data_tele.len();
                let tele = data_tele
                    .iter()
                    .cloned()
                    .map(Bind::into_implicit)
                    .chain(params.iter().cloned())
                    .collect();
                let _ident = self.def(data).def_name().clone();
                let elims = range.rev().map(Term::from_dbi).collect();
                let ret = Term::data(ValData::new(data, elims));
                Ok(Term::pi_from_tele(tele, ret).at(cons.loc()))
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
        debug!("{}⊢ {} ↓ {}", depth_ws, input_term, against);
        self.tc_deeper();
        let a = self.check_impl(input_term, against).map_err(|e| {
            debug!("{}Checking {} : {}", depth_ws, input_term, against);
            e
        })?;
        debug!("{}⊢ {} : {} ↑ {}", depth_ws, input_term, against, a.ast);
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
    use crate::{assert_err, pt, ptis};

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

        let ty = ptis!(p, des, env, "T -> T");
        env.check(&pt!(p, des, "lam (y : T) => y"), &ty)?;

        let ty = ptis!(p, des, env, "forall (ff : T -> T) (x : T), T");
        env.check(&pt!(p, des, "lam (f : T -> T) (y : T) => f y"), &ty)?;

        let ty = ptis!(p, des, env, "Type");
        env.check(&pt!(p, des, "forall (ff : T -> T) (x : T), T"), &ty)?;

        let ty = ptis!(p, des, env, "Type1");
        env.check(&pt!(p, des, "Type0"), &ty)?;

        let ty = ptis!(p, des, env, "Type0");
        assert_err!(
            env.check(&pt!(p, des, "Type1"), &ty),
            Error::DifferentUniverse(Loc::new(0, 5), Universe(2), Universe(0))
        );

        let ty = ptis!(p, des, env, "T");
        assert_err!(
            env.check(&pt!(p, des, "forall (ff : T -> T) (x : T), x"), &ty),
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

        let ty = ptis!(p, des, env, "Bool");
        env.check(&pt!(p, des, "bool"), &ty)?;

        let ty = ptis!(p, des, env, "Type");
        env.check(&pt!(p, des, "Bool"), &ty)?;

        let ty = ptis!(p, des, env, "forall (A : Type) (a : A), A");
        env.check(&pt!(p, des, "id"), &ty)?;

        let ty = ptis!(p, des, env, "Bool");
        env.check(&pt!(p, des, "idb"), &ty)?;

        let ty = ptis!(
            p,
            des,
            env,
            "forall (f : forall (A : Type), A -> A -> A) (x : Bool), Bool"
        );
        env.check(&pt!(p, des, "deep"), &ty)?;
        env.check(&pt!(p, des, "deep'"), &ty)?;

        Ok(())
    }

    #[test]
    #[ignore]
    fn test_data() -> eyre::Result<()> {
        let _parser = Parser::default();
        /*
            let out = env.run(parser.parse_prog(
                r#"
        data Nat
            | O
            | S Nat

        data List (T : Type)
            | nil
            | cons T (List T)

        fn main := cons Nat (S (S O)) (cons Nat (S O) (cons Nat O (nil Nat)))
        "#,
            )?);
            assert_eq!(
                out,
                parser.parse_term("cons Nat (S (S O)) (cons Nat (S O) (cons Nat O (nil Nat)))")?
            );
            assert_eq!(env.infer_type(out)?, parser.parse_term("List Nat")?);
            assert_eq!(
                *env.get_type(&Ident("nil".to_owned())).unwrap(),
                parser.parse_term("forall (T : Type), List T")?
            );
            let x = env.get_type(&Ident("cons".to_owned())).unwrap();
            let term = parser.parse_term("forall (T : Type) (__x2 : T) (__x1 : List T), (List T)")?;
            assert_eq!(*x, term);
             */
        Ok(())
    }
}
