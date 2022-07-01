use crate::check::meta::HasMeta;
use crate::check::{Error, Result, TypeCheckState};
use crate::dsp;
use crate::syntax::abs::{Expr, Pat as PatA};
use crate::syntax::core::{
    Case, Ctx, DataInfo, DeBruijn, Decl, Pat, PrimSubst, Subst, Substitution, Term, Val,
};
use crate::syntax::{ConHead, DBI, UID};
use derive_more::Display;
use itertools::{EitherOrBoth, Itertools};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use vec1::Vec1;

/// {w_k /? p_k : A_k | k = 1...l}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    pat: PatA,
    term: Term,
    ty: Term,
}

impl Constraint {
    pub fn new(pat: PatA, term: Term, ty: Term) -> Self {
        Self { pat, term, ty }
    }

    /// Generate abstract substitution \[x := y\].
    pub fn gen_abs_subst(&self, tcs: &TypeCheckState) -> (UID, Expr) {
        match (&self.pat, &self.term) {
            (PatA::Var(x), Term::Whnf(Val::Var(y, es))) if es.is_empty() => {
                let x1 = tcs.lookup(*y);
                (*x, Expr::Var(x1.clone().ident(), x1.name))
            }
            (PatA::Var(x), Term::Whnf(Val::Cons(con, es))) => (
                *x,
                if es.is_empty() {
                    Expr::Cons(con.name.clone(), con.cons_gi)
                } else {
                    Expr::app(
                        Expr::Cons(con.name.clone(), con.cons_gi),
                        Vec1::try_from_vec(
                            es.iter()
                                .map(|e| match e {
                                    Term::Whnf(Val::Var(y, es)) if es.is_empty() => {
                                        let x1 = tcs.lookup(*y);
                                        Expr::Var(x1.clone().ident(), x1.name)
                                    }
                                    Term::Whnf(Val::Cons(con, es)) if es.is_empty() => {
                                        Expr::Cons(con.name.clone(), con.cons_gi)
                                    }
                                    _ => {
                                        panic!(
                                            "unexpected term in constraint: {} /? {}",
                                            self.term, self.pat
                                        );
                                    }
                                })
                                .collect(),
                        )
                        .unwrap(),
                    )
                },
            ),
            _ => panic!("Invalid constraint: {} /? {}", self.term, self.pat),
        }
    }
}

impl Subst for Constraint {
    fn subst(self, subst: Rc<PrimSubst<Term>>) -> Self {
        let pat = self.pat;
        let term = self.term.subst(subst.clone());
        let ty = self.ty.subst(subst);
        Self { pat, term, ty }
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{} /? {}]", self.term, self.pat)
    }
}

/// \[E\]q ~> rhs
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    /// Constraints `[t /? p]`.
    constraints: Vec<Constraint>,
    /// Patterns given by the user.
    user_pats: Vec<PatA>,
    /// Right-hand side
    rhs: Option<Expr>,
}

impl Display for Clause {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "  | {} {}",
            self.constraints.iter().join(" "),
            // self.constraints,
            self.user_pats.iter().join(" ")
        )?;
        if let Some(rhs) = &self.rhs {
            write!(f, " => {}", rhs)?;
        }
        Ok(())
    }
}

impl Clause {
    pub fn new(user_pats: Vec<PatA>, rhs: Option<Expr>) -> Self {
        Clause {
            constraints: Vec::new(),
            // constraints: Constraints::new(),
            user_pats,
            rhs,
        }
    }
}

impl Display for LshProblem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "P = {{")?;
        for cls in &self.clauses {
            writeln!(f, "{}", cls)?;
        }
        writeln!(f, "  }}")?;
        writeln!(f, "  pats: {}", self.pats.iter().join(", "))?;
        writeln!(f, "  target: {}", self.target)?;
        write!(f, "  vars: {}", self.vars.iter().join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LshProblem {
    /// User patterns with constraints. P = {q_vec_i -> rhs_i | i = 1...n}.
    clauses: Vec<Clause>,
    /// Variables referring to Γ or lets being matched on.
    vars: Vec<DBI>,
    /// Core patterns being refined.
    pats: Vec<Pat>,
    /// Target type `rhs` should be equal too.
    target: Term,
}

/// Potentially partial case tree.
#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum CaseTree {
    Leaf(Term),
    Case(Term, Vec<(Pat, Option<CaseTree>)>),
}

impl Display for CaseTree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            CaseTree::Leaf(t) => write!(f, "{}", t),
            CaseTree::Case(t, cases) => {
                write!(f, "case {} of", t)?;
                for (pat, tree) in cases {
                    write!(f, " {}", pat)?;
                    if let Some(tree) = tree {
                        write!(f, " => ")?;
                        write!(f, "{}", tree)?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl CaseTree {
    pub fn case(term: impl Into<Term>, cases: impl Into<Vec<(Pat, Option<CaseTree>)>>) -> Self {
        Self::Case(term.into(), cases.into())
    }

    /// Converts an elaborated case tree to a core term. Panics if the tree is not fully elaborated.
    pub(crate) fn into_term(self) -> Term {
        match self {
            CaseTree::Leaf(t) => t.clone(),
            CaseTree::Case(i, cases) => {
                let cases = cases
                    .into_iter()
                    .map(|(p, c)| {
                        let pat = match p {
                            Pat::Var(x) => Pat::Var(x),
                            Pat::Wildcard => Pat::Wildcard,
                            Pat::Absurd => {
                                panic!("Unexpected absurd pattern in an elaborated case tree")
                            }
                            Pat::Cons(forced, head, ps) => {
                                debug_assert!(!forced);
                                debug_assert!(ps.iter().all(|x| x.is_var()));
                                Pat::Cons(forced, head, ps)
                            }
                            Pat::Forced(_) => {
                                panic!("Unexpected forced pattern in an elaborated case tree")
                            }
                        };
                        Case {
                            pattern: pat,
                            body: c.expect("empty body in elaborated case tree").into_term(),
                        }
                    })
                    .collect();
                Term::Match(box i, cases)
            }
        }
    }
}

impl HasMeta for CaseTree {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        match self {
            CaseTree::Leaf(t) => Ok(CaseTree::Leaf(t.inline_meta(tcs)?)),
            CaseTree::Case(x, cases) => {
                let cases = cases
                    .into_iter()
                    .map(|(pat, tree)| {
                        let pat = pat.inline_meta(tcs)?;
                        let tree = tree.map(|x| x.inline_meta(tcs)).transpose()?;
                        Ok((pat, tree))
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(CaseTree::Case(x, cases))
            }
        }
    }
}

impl CaseTree {
    pub fn merge(self, other: Self) -> Self {
        use crate::syntax::pattern::Pat::*;
        use CaseTree::*;
        match (self, other) {
            (Case(i, cases_a), Case(j, cases_b)) => {
                debug_assert_eq!(i, j);
                let cases = cases_a
                    .into_iter()
                    .merge_join_by(cases_b, |(pat_a, _ct_a), (pat_b, _ct_b)| {
                        match (pat_a, pat_b) {
                            (Cons(forced_a, head_a, pats_a), Cons(forced_b, head_b, pats_b)) => {
                                assert!(!forced_a && !forced_b);
                                debug_assert!(pats_a.iter().all(Pat::is_var));
                                debug_assert!(pats_b.iter().all(Pat::is_var));
                                if head_a.cons_gi == head_b.cons_gi {
                                    Ordering::Equal
                                } else {
                                    Ordering::Less
                                }
                            }
                            (Var(a), Var(b)) => {
                                debug_assert_eq!(a, b);
                                Ordering::Less
                            }
                            (Cons(..), Var(..)) => Ordering::Less,
                            (Var(..), Cons(..)) => Ordering::Greater,
                            (_, _) => panic!("Can't merge patterns in a case tree"),
                        }
                    })
                    .map(|choice| match choice {
                        EitherOrBoth::Both((pat_a, ct_a), (pat_b, ct_b)) => {
                            debug_assert_eq!(pat_a, pat_b);
                            let ct = match (ct_a, ct_b) {
                                (Some(ct_a), Some(ct_b)) => Some(ct_a.merge(ct_b)),
                                (_, None) => panic!(),
                                (None, _) => panic!(),
                            };
                            (pat_a, ct)
                        }
                        EitherOrBoth::Left(x) | EitherOrBoth::Right(x) => x,
                    })
                    .collect::<Vec<_>>();
                Case(i, cases)
            }
            (Leaf(a), Leaf(b)) => {
                assert_eq!(a, b);
                Leaf(a)
            }
            (Leaf(a), Case(..)) => Leaf(a),
            (a, b) => {
                error!("Can't merge trees:\n{a:#?},\n{b:#?}");
                panic!("Can't merge case trees");
            }
        }
    }
}

impl LshProblem {
    pub fn new(vars: Vec<DBI>, clauses: Vec<Clause>, target: Term) -> Self {
        LshProblem {
            clauses,
            vars,
            pats: Vec::new(),
            target,
        }
    }

    pub fn init(&mut self, tcs: &TypeCheckState) -> Result<()> {
        // Intro rule
        let vars_len = self.vars.len();
        for clause in &mut self.clauses {
            let mut constraints = Vec::with_capacity(vars_len);
            let mut user_pats = clause.user_pats.iter();
            for (i, bind) in self.vars.iter().map(|v| (*v, tcs.lookup(*v))) {
                if bind.is_implicit() {
                    todo!("Support for implicit patterns");
                } else if let Some(pat) = user_pats.next() {
                    constraints.push(Constraint::new(
                        pat.clone(),
                        Term::from_dbi(i),
                        bind.ty.clone(),
                    ))
                } else {
                    // All patterns were handled
                    return Err(Error::TooFewPatterns);
                }
            }
            clause.constraints.extend(constraints);

            // Remove handled user patterns
            clause.user_pats =
                clause.user_pats[(clause.user_pats.len() - user_pats.len())..].to_vec();
            if !clause.user_pats.is_empty() {
                return Err(Error::TooManyPatterns);
            }
        }
        self.pats.extend((0..vars_len).rev().map(Pat::Var));
        Ok(())
    }

    pub fn check(self, tcs: &mut TypeCheckState) -> Result<CaseTree> {
        if self.clauses.is_empty() {
            return Err(Error::NonExhaustiveMatch);
        }

        let clause_1 = &self.clauses[0];
        let maybe_ct = clause_1
            .constraints
            .iter()
            .enumerate()
            .find(|(_, x)| (x.pat.is_cons() || x.pat.is_abusrd()) && x.term.is_eta_var());
        if let Some((_ct_idx, ct)) = maybe_ct {
            match &ct.ty {
                Term::Whnf(Val::Data(data)) => match ct.term.dbi_view() {
                    Some(x) => {
                        let data_args = &data.args;
                        match tcs.def(data.def).clone() {
                            Decl::Data(data) => {
                                if data.conses.is_empty() {
                                    return Self::split_empty(clause_1, ct, x);
                                }
                                self.split_con(tcs, ct, x, data_args, data)
                            }
                            _ => unreachable!("Data type definition expected"),
                        }
                    }
                    None => {
                        unimplemented!("Eta var expected");
                    }
                },
                _ => unreachable!("Attempt to split on non-data type"),
            }
        } else {
            if clause_1
                .constraints
                .iter()
                .all(|x| x.pat.is_var() && (x.term.is_eta_var() || x.term.is_cons()))
            {
                Self::done(tcs, clause_1, self.target)
            } else {
                unimplemented!("{}", clause_1.constraints.iter().join(", "));
            }
        }
    }

    fn split_empty(clause_1: &Clause, ct: &Constraint, x: DBI) -> Result<CaseTree> {
        if !ct.pat.is_abusrd() {
            return Err(Error::ExpectedAbsurd(box ct.pat.clone()));
        }
        if clause_1.rhs.is_some() {
            return Err(Error::UnexpectedRhs);
        }
        return Ok(CaseTree::case(x, Vec::new()));
    }

    fn split_con(
        &self,
        tcs: &mut TypeCheckState,
        ct: &Constraint,
        x: DBI,
        data_args: &Vec<Term>,
        data: DataInfo,
    ) -> Result<CaseTree> {
        let mut ct_clauses = Vec::new();
        let conses = data
            .conses
            .iter()
            .map(|c| tcs.def(*c).as_cons().clone())
            .collect::<Vec<_>>();
        for (cons_ix, cons) in conses.into_iter().enumerate() {
            debug!("\nSplitting constraint {} with {}", ct, cons.name);
            debug!("Problem before: {}", &self);
            debug!("Context before {}", tcs.gamma);

            let delta_len = data_args.len();
            let delta_i = cons.signature.clone().tele_view().0;
            let delta_tick_i = Ctx(delta_i.clone());
            let mut gamma1 = tcs.gamma.clone();
            let (xx, mut gamma2) = gamma1.split(x);
            debug_assert_eq!(xx.ty, ct.ty);
            let mut delta_tick_hat_i =
                (data_args.clone()).subst(Substitution::raise(cons.params.len()));
            delta_tick_hat_i.extend((0..cons.params.len()).rev().map(|i| Term::from_dbi(i)));
            let cons_gi = cons.data_gi + cons_ix + 1;
            let con_head = ConHead::new(cons.name.clone(), cons_gi);
            let alpha = Substitution::raise(cons.params.len())
                .cons(Term::cons(con_head.clone(), delta_tick_hat_i.clone()));
            gamma2 = gamma2.subst(alpha.clone());

            debug!("α = {}", &alpha);
            let beta = alpha.clone().lift_by(gamma2.len());
            debug!("β = {}", &beta);
            let target_new = self.target.clone().subst(beta.clone());
            debug!("Γ1 = {}", gamma1);
            let clauses_new = self
                .clauses
                .clone()
                .into_iter()
                .filter_map(|mut clause| {
                    clause.constraints = clause.constraints.clone().subst(beta.clone());
                    debug!("transforming clause: {}", &clause);
                    let mut constraints_new = Vec::new();
                    for cst in clause.constraints.clone() {
                        match (cst.term, cst.pat) {
                            (
                                Term::Whnf(Val::Cons(con_head, delta_tick_hat_i)),
                                PatA::Cons(false, pat_head, es),
                            ) => {
                                if con_head.cons_gi != pat_head.cons_gi {
                                    debug!("  <-- removed");
                                    return None;
                                }
                                debug_assert_eq!(delta_tick_hat_i.len(), es.len());
                                let mut delta_tick_i_renamed =
                                    delta_tick_i.clone().skipping(delta_len);
                                delta_tick_i_renamed.iter_mut().zip(es.iter()).for_each(
                                    |(x, y)| {
                                        x.name = match y {
                                            PatA::Var(i) => *i,
                                            _ => panic!(),
                                        };
                                    },
                                );

                                gamma1.extend(delta_tick_i_renamed);

                                constraints_new.extend(
                                    delta_tick_hat_i
                                        .into_iter()
                                        .zip(es)
                                        .zip(delta_tick_i.iter().cloned())
                                        .map(|((delta_tick_hat_i, pat), bind)| {
                                            Constraint::new(pat, delta_tick_hat_i, bind.ty)
                                        }),
                                );
                            }
                            v @ (Term::Whnf(Val::Cons(..)), PatA::Var(_)) => {
                                let delta_tick_i_renamed = delta_tick_i.clone().skipping(delta_len);
                                gamma1.extend(delta_tick_i_renamed);

                                constraints_new.push(Constraint::new(v.1, v.0, cst.ty));
                            }
                            (t, p) => constraints_new.push(Constraint::new(p, t, cst.ty)),
                        };
                    }
                    debug!("");

                    clause.constraints = constraints_new;
                    Some(clause)
                })
                .collect();
            debug!("Γ1Δ'i = {}", gamma1);

            let pats_new = self.pats.clone().subst(beta);
            let mut lhs_new = self.clone();
            lhs_new.target = target_new;
            lhs_new.pats = pats_new;
            lhs_new.clauses = clauses_new;
            gamma1.extend(gamma2);
            let gamma_new = gamma1;
            let ct = tcs.under_ctx(gamma_new, |tcs| {
                debug!("Problem after: {}", &lhs_new);
                debug!("Context after {}", tcs.gamma);
                lhs_new.check(tcs)
            })?;
            // TODO: use self.pats?
            let clause_pat = Pat::cons(
                con_head,
                delta_tick_hat_i
                    .into_iter()
                    .map(|x| match x {
                        Term::Whnf(Val::Var(i, _)) => Pat::Var(i),
                        _ => unreachable!(),
                    })
                    .collect(),
            );
            ct_clauses.push((clause_pat, Some(ct)));
        }
        return Ok(CaseTree::case(x, ct_clauses));
    }

    fn done(tcs: &mut TypeCheckState, clause_1: &Clause, target: Term) -> Result<CaseTree> {
        let refined_user_pats = Rc::new(
            clause_1
                .constraints
                .iter()
                .map(|c| c.gen_abs_subst(tcs))
                .collect::<HashMap<_, _>>(),
        );

        let mut rhs1 = clause_1.rhs.clone().unwrap();
        debug!("rhs = {}", rhs1);
        debug!("new abs-subst = {:?}", refined_user_pats);
        rhs1.subst_abs(refined_user_pats.clone());
        debug!("rhs refined = {}", rhs1);
        debug!("target = {}", target);
        let checked_rhs = tcs.check(&rhs1, &tcs.simplify(target)?)?.ast;
        return Ok(CaseTree::Leaf(checked_rhs));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::Unify;
    use crate::parser::Parser;
    use crate::pct;
    use crate::syntax::core::{Elim, Func, ValData};
    use crate::syntax::desugar::desugar_prog;
    use crate::syntax::Plicitness::Explicit;
    use crate::syntax::{Bind, ConHead, Ident, Loc};

    #[test]
    fn test_fail_build_case_tree() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let des = desugar_prog(p.parse_prog(
            r#"
         data Nat : Type
             | zero
             | suc Nat

         data Empty : Type

         fn absurd (x : Empty) : Nat := match x {
             | !, zero
         }
        "#,
        )?)?;

        assert_eq!(
            env.check_prog(des.clone()).unwrap_err(),
            Error::TooManyPatterns
        );

        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let des = desugar_prog(p.parse_prog(
            r#"
         data Nat : Type
             | zero
             | suc Nat

         data Empty : Type

         fn f (x : Nat) (y : Nat) : Nat := match x, y {
             | x => x
         }
        "#,
        )?)?;

        assert_eq!(
            env.check_prog(des.clone()).unwrap_err(),
            Error::TooFewPatterns
        );

        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        data Empty : Type

        fn f (x : Nat) (y : Nat) : Nat := match x, y {
            | x,       zero => x
            | (suc x), y => x
        }
       "#,
        )?)?;

        assert_eq!(
            env.check_prog(des.clone()).unwrap_err(),
            Error::NonExhaustiveMatch
        );

        Ok(())
    }

    #[test]
    fn test_build_case_tree() -> eyre::Result<()> {
        use crate::syntax::pattern::Pat::*;
        use Term::*;

        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        fn max (x : Nat) (y : Nat) : Nat := match x, y {
              | x,        zero    => x
              | zero,     y       => y
              | (suc x),  (suc y) => suc (max x y)
        }

        data Empty : Type

        fn absurd (A : Type) (x : Empty) : A := match x {
            | !
        }
       "#,
        )?)?;
        env.check_prog(des.clone())?;

        let ct = env
            .def(*des.decls_map.get("max").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;

        /*
        match 0 {
         | zero => @0
         | (suc 0) => match 1 {
             | zero => (suc @0)
             | (suc 0) => (suc @1 @0)
            }
        }
         */
        let cte = Term::mat_elim(
            0,
            [
                Case {
                    pattern: Cons(
                        false,
                        ConHead {
                            name: Ident {
                                text: "zero".to_string(),
                                loc: Loc { start: 39, end: 43 },
                            },
                            cons_gi: 1,
                        },
                        vec![],
                    ),
                    body: Term::from_dbi(0),
                },
                Case {
                    pattern: Cons(
                        false,
                        ConHead {
                            name: Ident {
                                text: "suc".to_owned(),
                                loc: Loc { start: 58, end: 61 },
                            },
                            cons_gi: 2,
                        },
                        vec![Pat::from_dbi(0)],
                    ),
                    body: Match(
                        box Term::from_dbi(1),
                        vec![
                            Case {
                                pattern: Cons(
                                    false,
                                    ConHead {
                                        name: Ident {
                                            text: "zero".to_owned(),
                                            loc: Loc { start: 39, end: 43 },
                                        },
                                        cons_gi: 1,
                                    },
                                    vec![],
                                ),
                                body: Term::cons(
                                    ConHead {
                                        name: Ident {
                                            text: "suc".to_owned(),
                                            loc: Loc { start: 58, end: 61 },
                                        },
                                        cons_gi: 2,
                                    },
                                    vec![Term::from_dbi(0)],
                                ),
                            },
                            Case {
                                pattern: Cons(
                                    false,
                                    ConHead {
                                        name: Ident {
                                            text: "suc".to_owned(),
                                            loc: Loc { start: 58, end: 61 },
                                        },
                                        cons_gi: 2,
                                    },
                                    vec![Pat::from_dbi(0)],
                                ),
                                body: Term::cons(
                                    ConHead {
                                        name: Ident {
                                            text: "suc".to_owned(),
                                            loc: Loc {
                                                start: 239,
                                                end: 242,
                                            },
                                        },
                                        cons_gi: 2,
                                    },
                                    vec![Redex(
                                        Func::Index(3),
                                        Ident {
                                            text: "max".to_owned(),
                                            loc: Loc {
                                                start: 244,
                                                end: 247,
                                            },
                                        },
                                        vec![
                                            Elim::App(box Term::from_dbi(1)),
                                            Elim::App(box Term::from_dbi(0)),
                                        ],
                                    )],
                                ),
                            },
                        ],
                    ),
                },
            ],
        );
        assert_eq!(ct, cte);

        let ct = env
            .def(*des.decls_map.get("absurd").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;
        let cte = Term::mat_elim(0, []);
        assert_eq!(ct, cte);

        Ok(())
    }

    #[test]
    fn test_build_case_tree_pairs() -> eyre::Result<()> {
        use crate::syntax::pattern::Pat::*;

        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        data Pair (A : Type) (B : Type) : Type1
            | mkPair A B

        fn proj1 (A : Type) (B : Type) (x : Pair A B) : A := match x {
            | (mkPair t1 t2 a b) => a
        }

        fn proj2 (A : Type) (B : Type) (x : Pair A B) : B := match x {
            | (mkPair t1 t2 a b) => b
        }
       "#,
        )?)?;
        env.check_prog(des.clone())?;

        let ct = env
            .def(*des.decls_map.get("proj1").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;
        let cte = Term::mat_elim(
            0,
            [Case {
                pattern: Cons(
                    false,
                    ConHead {
                        name: Ident {
                            text: "mkPair".to_owned(),
                            loc: Loc {
                                start: 129,
                                end: 135,
                            },
                        },
                        cons_gi: 4,
                    },
                    vec![
                        Pat::from_dbi(3),
                        Pat::from_dbi(2),
                        Pat::from_dbi(1),
                        Pat::from_dbi(0),
                    ],
                ),
                body: Term::from_dbi(1),
            }],
        );
        assert_eq!(ct, cte);

        let ct = env
            .def(*des.decls_map.get("proj2").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;
        let cte = Term::mat_elim(
            0,
            [Case {
                pattern: Cons(
                    false,
                    ConHead {
                        name: Ident {
                            text: "mkPair".to_owned(),
                            loc: Loc {
                                start: 129,
                                end: 135,
                            },
                        },
                        cons_gi: 4,
                    },
                    vec![
                        Pat::from_dbi(3),
                        Pat::from_dbi(2),
                        Pat::from_dbi(1),
                        Pat::from_dbi(0),
                    ],
                ),
                body: Term::from_dbi(0),
            }],
        );
        assert_eq!(ct, cte);

        Ok(())
    }

    #[test]
    fn test_eval_case_tree_1() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let mut des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        data Single : Type
            | cons Nat Nat

        fn foo (s : Single) : Nat := match s {
              | (cons n m) => n
        }

        fn main : Nat := foo (cons (suc zero) zero)
       "#,
        )?)?;
        env.check_prog(des.clone())?;
        let val = pct!(p, des, env, "main");
        let val1 = pct!(p, des, env, "(suc zero)");
        Val::unify(&mut env, &val1, &val)?;
        Ok(())
    }

    #[test]
    fn test_eval_case_tree_2() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let mut des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        fn max (x : Nat) (y : Nat) : Nat := match x, y {
              | x,        zero    => x
              | zero,     y       => y
              | (suc x),  (suc y) => suc (max x y)
        }

        fn main : Nat := max (suc (suc zero)) (suc zero)
       "#,
        )?)?;
        env.check_prog(des.clone())?;
        let ct = env
            .def(*des.decls_map.get("max").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;
        debug!("{}", ct);
        /*
        match 0 { -- x
         | zero => @0
         | (suc 0) => match 1 { -- y
             | zero => (suc @0)
             | (suc 0) => (suc (max @1 @1)) -- suc (max @1 @1)
            }
        }
         */
        let val = pct!(p, des, env, "main");
        let val1 = pct!(p, des, env, "(suc (suc zero))");
        Val::unify(&mut env, &val1, &val)?;
        Ok(())
    }

    #[test]
    fn test_eval_case_tree_3() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        env.trace_tc = true;
        let mut des = desugar_prog(p.parse_prog(
            r#"
        data Sigma (A : Type) (B : A -> Type) : Type1
            | mkSigma (x : A) (y : B x)

        data Nat : Type
            | zero
            | suc Nat

        data Bool : Type
            | true
            | false

        data Pair (A : Type) (B : Type) : Type1
            | mkPair A B

        fn proj1 (A : Type) (B : Type) (x : Pair A B) : A := match x {
            | (mkPair t1 t2 a b) => a
        }

        fn proj2 (A : Type) (B : Type) (x : Pair A B) : B := match x {
            | (mkPair t1 t2 a b) => b
        }

        fn sproj1 (A : Type) (B : A -> Type) (x : Sigma A B) : A := match x {
            | (mkSigma t1 t2 a b) => a
        }

        fn sproj2 (A : Type) (B : A -> Type) (x : Sigma A B) : B (match x { | (mkSigma t1 t2 a b) => a }) := match x {
             | (mkSigma t1 t2 a b) => b
        }

        fn dep_fn (x : Nat) : (match x { | zero => Nat | (suc n) => Bool }) := match x {
            | zero => zero
            | (suc n) => false
        }

        fn sigma_test1 : Sigma Nat (lam z : Nat => match z { | zero => Nat | (suc n) => Bool }) :=
            mkSigma
                Nat
                (lam z : Nat => match z { | zero => Nat | (suc n) => Bool })
                zero
                zero

        fn sigma_test2 : Sigma Nat (lam z : Nat => match z { | zero => Nat | (suc n) => Bool }) :=
            mkSigma
                Nat
                (lam z : Nat => match z { | zero => Nat | (suc n) => Bool })
                (suc zero)
                true

        fn pair := mkPair Nat Nat (suc zero) zero
        fn tst1 : Nat := proj1 Nat Nat pair
        fn tst2 : Nat := proj2 Nat Nat pair

        fn sigma := mkSigma Nat (lam z : Nat => Nat) (suc zero) zero
        fn tst3 : Nat := sproj1 Nat (lam z : Nat => Nat) sigma
        fn tst4 : Nat := sproj2 Nat (lam z : Nat => Nat) sigma
        fn tst5 : Nat := sproj2 Nat (lam z : Nat => match z { | zero => Nat | o => Bool }) (mkSigma Nat (lam z : Nat => match z { | zero => Nat | o => Bool }) zero zero)
        fn tst6 : Bool := sproj2 Nat (lam z : Nat => match z { | zero => Nat | o => Bool }) (mkSigma Nat (lam z : Nat => match z { | zero => Nat | o => Bool }) (suc zero) true)
        fn tst7 : Nat := dep_fn zero
        fn tst8 : Bool := dep_fn (suc zero)
       "#,
        )?)?;
        env.check_prog(des.clone())?;

        let val = pct!(p, des, env, "tst1");
        let val1 = pct!(p, des, env, "(suc zero)");
        Val::unify(&mut env, &val1, &val)?;

        let val = pct!(p, des, env, "tst2");
        let val1 = pct!(p, des, env, "zero");
        Val::unify(&mut env, &val1, &val)?;

        let val = pct!(p, des, env, "tst3");
        let val1 = pct!(p, des, env, "(suc zero)");
        Val::unify(&mut env, &val1, &val)?;

        let val = pct!(p, des, env, "tst4");
        let val1 = pct!(p, des, env, "zero");
        Val::unify(&mut env, &val1, &val)?;

        let val = pct!(p, des, env, "tst5");
        let val1 = pct!(p, des, env, "zero");
        Val::unify(&mut env, &val1, &val)?;

        let val = pct!(p, des, env, "tst6");
        let val1 = pct!(p, des, env, "true");
        Val::unify(&mut env, &val1, &val)?;

        let val = pct!(p, des, env, "tst7");
        let val1 = pct!(p, des, env, "zero");
        Val::unify(&mut env, &val1, &val)?;

        let val = pct!(p, des, env, "tst8");
        let val1 = pct!(p, des, env, "false");
        Val::unify(&mut env, &val1, &val)?;

        Ok(())
    }

    #[test]
    fn test_subst() {
        // A = 0
        // B = 1
        // C = 2
        // D = 3

        // E = 4
        // F = 5
        // G = 6
        // Cons = 7

        //    v-- split
        // A, B, C(B), D(B)
        //               1
        // A, Ba, Bb, Bc, C(BC Ba Bb Bc), D(A)
        //                     2  1  0      4 (=2 + 3-1)
        let mut gamma = vec![
            Bind::new(
                Explicit,
                0,
                Term::data(ValData::new(0, vec![])),
                Loc::default(),
            ),
            Bind::new(
                Explicit,
                1,
                Term::data(ValData::new(1, vec![])),
                Loc::default(),
            ),
            Bind::new(
                Explicit,
                2,
                Term::data(ValData::new(2, vec![Term::from_dbi(0)])),
                Loc::default(),
            ),
            Bind::new(
                Explicit,
                3,
                Term::data(ValData::new(3, vec![Term::from_dbi(2)])),
                Loc::default(),
            ),
        ];
        for b in &gamma {
            print!("{}, ", b);
        }
        debug!("");
        let _b = gamma.remove(1);
        let mut gamma1 = gamma.clone();
        let gamma2 = gamma1.split_off(1);
        let delta = vec![
            Bind::new(
                Explicit,
                4,
                Term::data(ValData::new(4, vec![])),
                Loc::default(),
            ),
            Bind::new(
                Explicit,
                5,
                Term::data(ValData::new(5, vec![])),
                Loc::default(),
            ),
            Bind::new(
                Explicit,
                6,
                Term::data(ValData::new(6, vec![])),
                Loc::default(),
            ),
        ];
        gamma1.extend(delta.clone());
        let cons = Term::cons(
            ConHead::new(Ident::new("Cons", Loc::default()), 7),
            (0..delta.len()).rev().map(|i| Term::from_dbi(i)).collect(),
        );
        let rise = delta.len();
        for b in &gamma2 {
            print!("{}, ", b);
        }
        debug!("");
        let gamma2 = Ctx(gamma2)
            .subst(
                // Substitution::one(cons).weaken(rise),
                Substitution::raise(rise).cons(cons),
            )
            .0;
        gamma1.extend(gamma2);
        for b in &gamma1 {
            print!("{}, ", b);
        }
        debug!("");
    }

    #[test]
    fn test_subst_2() {
        // A B C D
        //   ^
        // A Ba Bb Bc C D
        let cons = Term::cons(
            ConHead::new(Ident::new("CC", Loc::default()), 7),
            [2, 1, 3].into_iter().map(|i| Term::from_dbi(i)).collect(),
        );
        // CC B C A
        // CC (Cons Ba Bb Bc) C A
        let term = cons.clone().apply(vec![Term::from_dbi(2)]);
        let cons2 = Term::cons(
            ConHead::new(Ident::new("Cons", Loc::default()), 7),
            (0..3).rev().map(|i| Term::from_dbi(i)).collect(),
        );
        let rise = 3;
        debug!("{}", term);
        let term = term.subst(
            // Substitution::one(cons).weaken(rise),
            Substitution::raise(rise).cons(cons2).lift_by(2),
        );
        debug!("{}", term);
        // n m
        let x = Term::from_dbi(1);
        let cons2 = Term::cons(
            ConHead::new(Ident::new("C2", Loc::default()), 7),
            [2, 1, 3].into_iter().map(|i| Term::from_dbi(i)).collect(),
        );
        let rc = Substitution::one(cons).cons(cons2);
        debug!("{}", rc);
        debug!("{}", x.subst(rc));
    }

    #[test]
    fn merge_case_trees() {
        /*
        CT1 = match m
          | Z => n

        CT2 = match m
          | Z   => match n
                   | Z => Z
          | S p => match n
                   | Z => (S p)

        CT3 = match m
          | S p => match n
                   | S q => S (max p q)

        CT = match m
             | Z   => n
             | S p => match n
                      | Z   => (S p)
                      | S q => S (max p q)
         */
        use crate::syntax::pattern::Pat::*;
        use CaseTree::*;

        // Γ = (m : Nat) (n : Nat)
        let con_z = ConHead::new(Ident::new("Z", Loc::default()), 0);
        let pat_z = Cons(false, con_z.clone(), vec![]);
        let con_s = ConHead::new(Ident::new("S", Loc::default()), 1);
        let pat_s = |x: DBI| Cons(false, con_s.clone(), vec![Var(x)]);
        let ct_1 = Case(
            Term::from_dbi(1),
            vec![(
                // Γ = (n : Nat)
                pat_z.clone(),
                Some(Leaf(Term::from_dbi(0))),
            )],
        );
        // Γ = (m : Nat) (n : Nat)
        let ct_2 = Case(
            Term::from_dbi(1),
            vec![
                (
                    // Γ = (n : Nat)
                    pat_z.clone(),
                    Some(Case(
                        Term::from_dbi(0),
                        vec![(
                            // Γ = ε
                            pat_z.clone(),
                            Some(Leaf(Term::cons(con_z.clone(), vec![]))),
                        )],
                    )),
                ),
                (
                    // Γ = (n : Nat) (p : Nat)
                    pat_s(0),
                    Some(Case(
                        Term::from_dbi(1),
                        vec![(
                            // Γ = (p : Nat)
                            pat_z.clone(),
                            Some(Leaf(Term::cons(con_s.clone(), vec![Term::from_dbi(0)]))),
                        )],
                    )),
                ),
            ],
        );
        // Γ = (m : Nat) (n : Nat)
        let ct_3 = Case(
            Term::from_dbi(1),
            vec![(
                // Γ = (n : Nat) (p : Nat)
                pat_s(0),
                Some(Case(
                    Term::from_dbi(1),
                    vec![(
                        // Γ = (p : Nat) (q : Nat)
                        pat_s(0),
                        // S (max p q)
                        Some(Leaf(Term::cons(
                            con_s.clone(),
                            vec![Term::cons(
                                con_s.clone(),
                                vec![Term::def(
                                    2,
                                    Ident::new("max", Loc::default()),
                                    vec![Elim::from_dbi(1), Elim::from_dbi(0)],
                                )],
                            )],
                        ))),
                    )],
                )),
            )],
        );

        let ct_exp = Case(
            Term::from_dbi(1),
            vec![
                (
                    // Γ = (n : Nat)
                    pat_z.clone(),
                    Some(Leaf(Term::from_dbi(0))),
                ),
                (
                    // Γ = (n : Nat) (p : Nat)
                    pat_s(0),
                    Some(Case(
                        Term::from_dbi(1),
                        vec![
                            (
                                // Γ = (p : Nat)
                                pat_z.clone(),
                                Some(Leaf(Term::cons(con_s.clone(), vec![Term::from_dbi(0)]))),
                            ),
                            (
                                // Γ = (p : Nat) (q : Nat)
                                pat_s(0),
                                // S (max p q)
                                Some(Leaf(Term::cons(
                                    con_s.clone(),
                                    vec![Term::cons(
                                        con_s.clone(),
                                        vec![Term::def(
                                            2,
                                            Ident::new("max", Loc::default()),
                                            vec![Elim::from_dbi(1), Elim::from_dbi(0)],
                                        )],
                                    )],
                                ))),
                            ),
                        ],
                    )),
                ),
            ],
        );
        let _ = env_logger::try_init();
        let ct = ct_1.merge(ct_2).merge(ct_3);
        assert_eq!(ct, ct_exp);
    }
}
