use crate::check::meta::HasMeta;
use crate::check::{Error, Result, TypeCheckState};
use crate::syntax::abs::{Expr, Pat as PatA};
use crate::syntax::core::{
    Case, DataInfo, DeBruijn, Decl, Pat, SubstWith, Substitution, Term, Val, Var,
};
use crate::syntax::{ConHead, DBI, UID};
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
            (PatA::Var(x), Term::Whnf(Val::Var(Var::Bound(y), es))) if es.is_empty() => {
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
                                    Term::Whnf(Val::Var(Var::Bound(y), es)) if es.is_empty() => {
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

impl SubstWith<'_> for Constraint {
    fn subst_with(self, subst: Rc<Substitution>, tcs: &mut TypeCheckState) -> Self {
        let pat = self.pat;
        let term = self.term.subst_with(subst.clone(), tcs);
        let ty = self.ty.subst_with(subst, tcs);
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
                    write!(f, " | {}", pat)?;
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
            CaseTree::Leaf(t) => t,
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
        } else if clause_1
            .constraints
            .iter()
            .all(|x| x.pat.is_var() && (x.term.is_eta_var() || x.term.is_cons()))
        {
            Self::done(tcs, clause_1, self.target)
        } else {
            unimplemented!("{}", clause_1.constraints.iter().join(", "));
        }
    }

    fn split_empty(clause_1: &Clause, ct: &Constraint, x: DBI) -> Result<CaseTree> {
        if !ct.pat.is_abusrd() {
            return Err(Error::ExpectedAbsurd(box ct.pat.clone()));
        }
        if clause_1.rhs.is_some() {
            return Err(Error::UnexpectedRhs);
        }
        Ok(CaseTree::case(x, Vec::new()))
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
        // TODO: clippy::needless_collect
        #[allow(clippy::needless_collect)]
        let conses = data
            .conses
            .iter()
            .map(|c| tcs.def(*c).as_cons().clone())
            .collect::<Vec<_>>();
        for (cons_ix, cons) in conses.into_iter().enumerate() {
            trace!("");
            trace!("Splitting var {} with {}", ct.term, cons.name);
            trace!("Problem before: {}", &self);
            trace!("Context before: {}", tcs.gamma);

            let delta_len = data_args.len();
            // let delta_i = cons.signature.clone().tele_view().0;
            let delta_i = cons.params.clone();
            trace!("Δi = {}", delta_i);
            trace!(
                "data args = {}",
                data_args.iter().map(|x| x.to_string()).join(", ")
            );
            let delta_tick_i = delta_i.subst_with(
                Substitution::parallel(data_args.into_iter().rev().cloned()),
                tcs,
            );
            trace!("Δ'i = {}", delta_tick_i);
            let mut gamma1 = tcs.gamma.clone();
            let (xx, mut gamma2) = gamma1.split(x);
            debug_assert_eq!(xx.ty, ct.ty);
            // let mut delta_tick_hat_i =
            //     (data_args.clone()).subst(Substitution::raise(cons.params.len()));
            // delta_tick_hat_i.extend((x..cons.params.len() + x).rev().map(Term::from_dbi));
            let mut delta_tick_hat_i = (0..cons.params.len())
                // .map(|i| i + x)
                .rev()
                .map(Term::from_dbi)
                .collect::<Vec<_>>();
            let cons_gi = cons.data_gi + cons_ix + 1;
            let con_head = ConHead::new(cons.name.clone(), cons_gi);
            // let alpha = Substitution::raise(cons.params.len())
            //     .cons(Term::cons(con_head.clone(), delta_tick_hat_i.clone()));
            let alpha = Substitution::raise(delta_tick_hat_i.len())
                .cons(Term::cons(con_head.clone(), delta_tick_hat_i.clone()));
            trace!("Γ2 = {}", gamma2);
            gamma2 = gamma2.subst_with(alpha.clone(), tcs);
            trace!("Γ2α = {}", gamma2);

            trace!("α = {}", &alpha);
            let beta = alpha.clone().lift_by(gamma2.len());
            trace!("β = {}", &beta);
            let target_new = self.target.clone().subst_with(beta.clone(), tcs);
            trace!("Γ1 = {}", gamma1);
            let mut i = 0;
            // For sanity check.
            let mut flag = false;
            let clauses_new = self
                .clauses
                .clone()
                .into_iter()
                .filter_map(|mut clause| {
                    clause.constraints = clause.constraints.clone().subst_with(beta.clone(), tcs);
                    trace!("transforming clause: {}", &clause);
                    let mut constraints_new = Vec::new();
                    for cst in clause.constraints.clone() {
                        match (cst.term, cst.pat) {
                            (
                                Term::Whnf(Val::Cons(con_head, delta_tick_hat_i_lifted)),
                                PatA::Cons(false, pat_head, es),
                            ) => {
                                if con_head.cons_gi != pat_head.cons_gi {
                                    trace!("^-- removed");
                                    return None;
                                }
                                debug_assert_eq!(delta_tick_hat_i_lifted.len(), es.len());
                                if i == 0 {
                                    debug_assert!(!flag, "Unexpected second split constraint");
                                    flag = true;
                                    delta_tick_hat_i = delta_tick_hat_i_lifted.clone();
                                    let mut delta_tick_i_renamed = delta_tick_i.clone(); //.skipping(delta_len);
                                    delta_tick_i_renamed.iter_mut().zip(es.iter()).for_each(
                                        |(x, y)| {
                                            x.name = match y {
                                                PatA::Var(i) => *i,
                                                _ => panic!(),
                                            };
                                        },
                                    );
                                    trace!("Δ'i' = {}", delta_tick_i_renamed);
                                    gamma1.extend(delta_tick_i_renamed);
                                }

                                constraints_new.extend(
                                    delta_tick_hat_i_lifted
                                        .into_iter()
                                        .zip(es)
                                        .zip(delta_tick_i.iter().cloned())
                                        .map(|((term, pat), bind)| {
                                            Constraint::new(pat, term, bind.ty)
                                        }),
                                );
                            }
                            v @ (Term::Whnf(Val::Cons(..)), PatA::Var(_)) => {
                                if i == 0 {
                                    let delta_tick_i_renamed =
                                        delta_tick_i.clone().skipping(delta_len);
                                    gamma1.extend(delta_tick_i_renamed);
                                }
                                constraints_new.push(Constraint::new(v.1, v.0, cst.ty));
                            }
                            (t, p) => constraints_new.push(Constraint::new(p, t, cst.ty)),
                        };
                    }

                    i += 1;
                    clause.constraints = constraints_new;
                    Some(clause)
                })
                .collect();
            trace!("Γ1Δ'i = {}", gamma1);

            let pats_new = self.pats.clone().subst_with(beta, tcs);
            let mut lhs_new = self.clone();
            lhs_new.target = target_new;
            lhs_new.pats = pats_new;
            lhs_new.clauses = clauses_new;
            gamma1.extend(gamma2);
            let gamma_new = gamma1;
            let ct = tcs.under_ctx(gamma_new, |tcs| {
                trace!("Problem after: {}", &lhs_new);
                trace!("Context after {}", tcs.gamma);
                lhs_new.check(tcs)
            })?;
            // TODO: use self.pats?
            let clause_pat = Pat::cons(
                con_head,
                delta_tick_hat_i
                    .into_iter()
                    .map(|x| match x {
                        Term::Whnf(Val::Var(Var::Bound(i), _)) => Pat::Var(i),
                        _ => unreachable!(),
                    })
                    .collect(),
            );
            ct_clauses.push((clause_pat, Some(ct)));
        }
        Ok(CaseTree::case(x, ct_clauses))
    }

    /*
       fn tst (A : Type) (B : Type) (p : Pair A B) (f : A -> B) : B := match p {
           | (mkPair a b) => f a
                          Γ = A B a b f
       }
    */
    fn done(tcs: &mut TypeCheckState, clause_1: &Clause, target: Term) -> Result<CaseTree> {
        debug!("Γdone = {}", tcs.gamma);
        let refined_user_pats = Rc::new(
            clause_1
                .constraints
                .iter()
                .map(|cst| {
                    trace!("Generating abstract substitution for {}", cst);
                    let subst = cst.gen_abs_subst(tcs);
                    trace!(" = [{} := {}]", subst.0, subst.1);
                    subst
                })
                .collect::<HashMap<_, _>>(),
        );

        let mut rhs1 = clause_1.rhs.clone().unwrap();
        trace!("rhs = {}", rhs1);
        trace!("new abs-subst = {:?}", refined_user_pats);
        rhs1.subst_abs(refined_user_pats);
        trace!("rhs refined = {}", rhs1);
        trace!("target = {}", target);
        let val = tcs.simplify(target)?;
        let checked_rhs = tcs.check(&rhs1, &val)?.ast;
        Ok(CaseTree::Leaf(checked_rhs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::Unify;
    use crate::parser::Parser;
    use crate::syntax::core::{Elim, Func, Subst, ValData};
    use crate::syntax::desugar::desugar_prog;
    use crate::syntax::pattern::Pat::{Cons, Var};
    use crate::syntax::Plicitness::Explicit;
    use crate::syntax::{Bind, ConHead, Ident, Loc};
    use crate::{dsp, pct};

    #[test]
    fn test_fail_build_case_tree() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let p = Parser::default();
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

        assert_eq!(env.check_prog(des).unwrap_err(), Error::TooManyPatterns);

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

        assert_eq!(env.check_prog(des).unwrap_err(), Error::TooFewPatterns);

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

        assert_eq!(env.check_prog(des).unwrap_err(), Error::NonExhaustiveMatch);

        Ok(())
    }

    #[test]
    fn test_build_case_tree() -> eyre::Result<()> {
        use crate::syntax::pattern::Pat::*;
        use Term::*;

        let _ = env_logger::try_init();
        let p = Parser::default();
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
        match @0 {
         | zero => @0
         | (suc 0) => match 1 {
             | zero => (suc @0)
             | (suc 1) => (suc @1 @0)
            }
        }
         */
        let cte = Term::match_elim(
            0,
            [
                Case {
                    pattern: Cons(
                        false,
                        ConHead {
                            name: Ident {
                                text: "zero".to_string(),
                                loc: Loc::default(),
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
                                loc: Loc::default(),
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
                                            loc: Loc::default(),
                                        },
                                        cons_gi: 1,
                                    },
                                    vec![],
                                ),
                                body: Term::cons(
                                    ConHead {
                                        name: Ident {
                                            text: "suc".to_owned(),
                                            loc: Loc::default(),
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
                                            loc: Loc::default(),
                                        },
                                        cons_gi: 2,
                                    },
                                    vec![Pat::from_dbi(1)],
                                ),
                                body: Term::cons(
                                    ConHead {
                                        name: Ident {
                                            text: "suc".to_owned(),
                                            loc: Loc::default(),
                                        },
                                        cons_gi: 2,
                                    },
                                    vec![Redex(
                                        Func::Index(3),
                                        Ident {
                                            text: "max".to_owned(),
                                            loc: Loc::default(),
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
        debug!("ct = {}", ct);
        debug!("cte = {}", cte);

        assert_eq!(ct, cte);

        let ct = env
            .def(*des.decls_map.get("absurd").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;
        let cte = Term::match_elim(0, []);
        assert_eq!(ct, cte);

        Ok(())
    }

    #[test]
    fn test_build_case_tree_pairs() -> eyre::Result<()> {
        use crate::syntax::pattern::Pat::*;

        let _ = env_logger::try_init();
        let p = Parser::default();
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
            | (mkPair a b) => a
        }

        fn proj2 (A : Type) (B : Type) (x : Pair A B) : B := match x {
            | (mkPair a b) => b
        }

        fn tst (A : Type) (B : Type) (p : Pair A B) (f : A -> B) : B := match p {
            | (mkPair a b) => f a
        }
       "#,
        )?)?;
        dsp!(&des.decls[5]);
        env.check_prog(des.clone())?;

        let ct = env
            .def(*des.decls_map.get("proj1").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;
        let cte = Term::match_elim(
            0,
            [Case {
                pattern: Cons(
                    false,
                    ConHead {
                        name: Ident {
                            text: "mkPair".to_owned(),
                            loc: Loc::default(),
                        },
                        cons_gi: 4,
                    },
                    vec![Pat::from_dbi(1), Pat::from_dbi(0)],
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
        let cte = Term::match_elim(
            0,
            [Case {
                pattern: Cons(
                    false,
                    ConHead {
                        name: Ident {
                            text: "mkPair".to_owned(),
                            loc: Loc::default(),
                        },
                        cons_gi: 4,
                    },
                    vec![Pat::from_dbi(1), Pat::from_dbi(0)],
                ),
                body: Term::from_dbi(0),
            }],
        );
        assert_eq!(ct, cte);

        dsp!(
            &env.def(*des.decls_map.get("tst").unwrap())
                .as_func()
                .signature
        );
        let ct = env
            .def(*des.decls_map.get("tst").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;

        let cte = Term::match_elim(
            1,
            [Case::new(
                Pat::cons(ConHead::new("mkPair", 4), [2, 1].map(Var).to_vec()),
                Term::from_dbi(0).apply(vec![Term::from_dbi(2)]),
            )],
        );
        assert_eq!(ct, cte);

        Ok(())
    }

    #[test]
    fn test_eval_case_tree_if() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let mut des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        data Bool : Type
            | true
            | false

        fn n3 : Nat := (suc (suc (suc zero)))
        fn n7 : Nat := (suc (suc (suc (suc n3))))

        fn if (x : Bool) (t : Nat) (e : Nat) : Nat := match x {
            | true => t
            | false => e
        }

        fn tst1 : Nat := if true n7 n3
        fn tst2 : Nat := if false n7 n3
       "#,
        )?)?;
        env.check_prog(des.clone())?;

        let ct = env
            .def(*des.decls_map.get("if").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;
        let cte = Term::match_elim(
            2,
            [
                Case {
                    pattern: Cons(
                        false,
                        ConHead {
                            name: Ident {
                                text: "true".to_owned(),
                                loc: Loc::default(),
                            },
                            cons_gi: 4,
                        },
                        vec![],
                    ),
                    body: Term::from_dbi(1),
                },
                Case {
                    pattern: Cons(
                        false,
                        ConHead {
                            name: Ident {
                                text: "false".to_owned(),
                                loc: Loc::default(),
                            },
                            cons_gi: 5,
                        },
                        vec![],
                    ),
                    body: Term::from_dbi(0),
                },
            ],
        );
        assert_eq!(ct, cte);
        let val = pct!(p, des, env, "tst2");
        let val1 = pct!(p, des, env, "n3");
        Val::unify(&mut env, &val1, &val)?;
        let val = pct!(p, des, env, "tst1");
        let val1 = pct!(p, des, env, "n7");
        Val::unify(&mut env, &val1, &val)?;
        Ok(())
    }

    #[test]
    fn test_eval_case_tree_add() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let mut des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        fn add (x : Nat) (y : Nat) : Nat := match y {
          | zero => x
          | (suc y') => suc (add x y')
        }

        fn add' (x : Nat) (y : Nat) : Nat := match x {
          | zero => y
          | (suc x') => suc (add' x' y)
        }

        fn n0 : Nat := zero
        fn n1 : Nat := (suc n0)
        fn n2 : Nat := (suc n1)
        fn n3 : Nat := (suc (suc (suc zero)))
        fn n5 : Nat := (suc (suc (suc (suc (suc zero)))))
        fn n7 : Nat := (suc (suc (suc (suc n3))))
        fn n10 : Nat := (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
        fn tst (f : Nat -> Nat -> Nat) (x : Nat) (y : Nat) : Nat := f x y
        fn tst1 : Nat := add n3 zero
        fn tst2 : Nat := add zero n3
        fn tst3 : Nat := add n3 n7
        fn tst4 : Nat := add n7 n3
        fn tst5 : Nat := add' n3 zero
        fn tst6 : Nat := add' zero n3
        fn tst7 : Nat := add' n3 n7
        fn tst8 : Nat := add' n7 n3
       "#,
        )?)?;
        env.check_prog(des.clone())?;

        let ct = env
            .def(*des.decls_map.get("add").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;
        let cte = Term::match_elim(
            0,
            [
                Case {
                    pattern: Cons(
                        false,
                        ConHead {
                            name: Ident {
                                text: "zero".to_owned(),
                                loc: Loc::default(),
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
                                loc: Loc::default(),
                            },
                            cons_gi: 2,
                        },
                        vec![Var(0)],
                    ),
                    body: Term::cons(
                        ConHead {
                            name: Ident {
                                text: "suc".to_owned(),
                                loc: Loc::default(),
                            },
                            cons_gi: 2,
                        },
                        vec![Term::Redex(
                            Func::Index(3),
                            Ident {
                                text: "add".to_owned(),
                                loc: Loc::default(),
                            },
                            vec![
                                Elim::App(box Term::from_dbi(1)),
                                Elim::App(box Term::from_dbi(0)),
                            ],
                        )],
                    ),
                },
            ],
        );
        assert_eq!(ct, cte);

        let ct = env
            .def(*des.decls_map.get("add'").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;
        let cte = Term::match_elim(
            1,
            [
                Case {
                    pattern: Cons(
                        false,
                        ConHead {
                            name: Ident {
                                text: "zero".to_owned(),
                                loc: Loc::default(),
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
                                loc: Loc::default(),
                            },
                            cons_gi: 2,
                        },
                        vec![Var(1)],
                    ),
                    body: Term::cons(
                        ConHead {
                            name: Ident {
                                text: "suc".to_owned(),
                                loc: Loc::default(),
                            },
                            cons_gi: 2,
                        },
                        vec![Term::Redex(
                            Func::Index(4),
                            Ident {
                                text: "add'".to_owned(),
                                loc: Loc::default(),
                            },
                            vec![
                                Elim::App(box Term::from_dbi(1)),
                                Elim::App(box Term::from_dbi(0)),
                            ],
                        )],
                    ),
                },
            ],
        );
        assert_eq!(ct, cte);
        let val = pct!(p, des, env, "tst1");
        let val1 = pct!(p, des, env, "n3");
        Val::unify(&mut env, &val1, &val)?;
        let val = pct!(p, des, env, "tst2");
        let val1 = pct!(p, des, env, "n3");
        Val::unify(&mut env, &val1, &val)?;
        let val = pct!(p, des, env, "tst3");
        let val1 = pct!(p, des, env, "n10");
        Val::unify(&mut env, &val1, &val)?;
        let val = pct!(p, des, env, "tst4");
        let val1 = pct!(p, des, env, "n10");
        Val::unify(&mut env, &val1, &val)?;
        let val = pct!(p, des, env, "tst5");
        let val1 = pct!(p, des, env, "n3");
        Val::unify(&mut env, &val1, &val)?;
        let val = pct!(p, des, env, "tst6");
        let val1 = pct!(p, des, env, "n3");
        Val::unify(&mut env, &val1, &val)?;
        let val = pct!(p, des, env, "tst7");
        let val1 = pct!(p, des, env, "n10");
        Val::unify(&mut env, &val1, &val)?;
        let val = pct!(p, des, env, "tst8");
        let val1 = pct!(p, des, env, "n10");
        Val::unify(&mut env, &val1, &val)?;
        Ok(())
    }

    #[test]
    fn test_eval_case_tree_sub() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let mut des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        fn sub (x : Nat) (y : Nat) : Nat := match x, y {
          | zero, y => zero
          | (suc x), zero => suc x
          | (suc x), (suc y) => sub x y
        }

        fn n0 : Nat := zero
        fn n1 : Nat := (suc n0)
        fn n2 : Nat := (suc n1)
        fn n3 : Nat := (suc (suc (suc zero)))
        fn n4 : Nat := (suc (suc (suc (suc zero))))
        fn n5 : Nat := (suc (suc (suc (suc (suc zero)))))
        fn n7 : Nat := (suc (suc (suc (suc n3))))
        fn n10 : Nat := (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))

        fn tst1 : Nat := sub n3 zero -- n3
        fn tst2 : Nat := sub zero n3 -- zero
        fn tst3 : Nat := sub n1 n2 -- zero
        fn tst4 : Nat := sub n7 n3 -- n4
       "#,
        )?)?;
        env.check_prog(des.clone())?;

        /*
        case @1
            | zero => zero
            | (suc 1) => case @0
                            | zero => (suc @0)
                            | (suc 0) => (sub @1 @0)
         */

        let ct = env
            .def(*des.decls_map.get("sub").unwrap())
            .as_func()
            .body
            .clone()
            .unwrap()
            .tele_view()
            .1;
        println!("ct = {}", ct);
        let _cte = Term::match_elim(
            0,
            [
                Case {
                    pattern: Cons(
                        false,
                        ConHead {
                            name: Ident {
                                text: "zero".to_owned(),
                                loc: Loc::default(),
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
                                loc: Loc::default(),
                            },
                            cons_gi: 2,
                        },
                        vec![Var(0)],
                    ),
                    body: Term::cons(
                        ConHead {
                            name: Ident {
                                text: "suc".to_owned(),
                                loc: Loc::default(),
                            },
                            cons_gi: 2,
                        },
                        vec![Term::Redex(
                            Func::Index(3),
                            Ident {
                                text: "add".to_owned(),
                                loc: Loc::default(),
                            },
                            vec![
                                Elim::App(box Term::from_dbi(1)),
                                Elim::App(box Term::from_dbi(0)),
                            ],
                        )],
                    ),
                },
            ],
        );
        // assert_eq!(ct, cte);

        // let val = pct!(p, des, env, "tst1");
        // let val1 = pct!(p, des, env, "n3");
        // Val::unify(&mut env, &val1, &val)?;
        // let val = pct!(p, des, env, "tst2");
        // let val1 = pct!(p, des, env, "zero");
        // Val::unify(&mut env, &val1, &val)?;
        let val = pct!(p, des, env, "tst3");
        let val1 = pct!(p, des, env, "zero");
        Val::unify(&mut env, &val1, &val)?;
        // let val = pct!(p, des, env, "tst4");
        // let val1 = pct!(p, des, env, "n10");
        Ok(())
    }

    #[test]
    fn test_eval_case_tree_1() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let p = Parser::default();
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

    /*
    Cons((suc zero), Cons((suc (suc zero)), ε))

    match @0 {
     | zero => @0
     | (suc 0) => match @1 {
         | zero => (suc @0)
         | (suc 1) => (suc (max @1 @0))
        }
    }

    match @0 {
     | zero => @0
     | (suc 0) => match (suc (suc zero)) {
         | zero => (suc @0)
         | (suc 1) => (suc (max @1 @0))
        }
    }
     */
    #[test]
    fn test_eval_case_tree_2() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let p = Parser::default();
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
        match @0 { -- y
         | zero => @0 -- x
         | (suc 0) => match 1 { -- x
             | zero => (suc @0) -- (suc y)
             | (suc 0) => (suc (max @1 @0))
            }
        }

        match @0 { -- y
         | zero => @0 -- x
         | (suc 0) => match 1 { -- x
             | zero => (suc @0) -- (suc y)
             | (suc 0) => (suc (max @1 @0))
            }
        }
         */
        let val = pct!(p, des, env, "main");
        let val1 = pct!(p, des, env, "(suc (suc zero))");
        Val::unify(&mut env, &val1, &val)?;
        Ok(())
    }

    #[test]
    #[ignore]
    fn test_eval_case_tree_3() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let p = Parser::default();
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
            | (mkPair a b) => a
        }

        fn proj2 (A : Type) (B : Type) (x : Pair A B) : B := match x {
            | (mkPair a b) => b
        }

        fn sproj1 (A : Type) (B : A -> Type) (x : Sigma A B) : A := match x {
            | (mkSigma a b) => a
        }

        fn sproj2 (A : Type) (B : A -> Type) (x : Sigma A B)
            : B (match x { | (mkSigma a b) => a }) := match x {
             | (mkSigma a b) => b
        }

        fn dep_fn (x : Nat) : (match x { | zero => Nat | (suc n) => Bool }) := match x {
            | zero => zero
            | (suc n) => false
        }

        fn sigma_test1 : Sigma Nat (lam z : Nat => match z { | zero => Nat | (suc n) => Bool }) :=
            mkSigma _ _ zero zero

        fn sigma_test2 : Sigma Nat (lam z : Nat => match z { | zero => Nat | (suc n) => Bool }) :=
            mkSigma _ _ (suc zero) true

        fn pair : Pair Nat Nat := mkPair _ _ (suc zero) zero
        fn tst1 := proj1 _ _ pair
        fn tst2 := proj2 _ _ pair

        fn sigma : Sigma Nat (lam z : Nat => Nat) := mkSigma _ _ (suc zero) zero
        fn tst3 : Nat := sproj1 _ _ sigma
        fn tst4 : Nat := sproj2 _ _ sigma
        fn tst5 : Nat := sproj2 _ (lam z : Nat => match z { | zero => Nat | o => Bool }) (mkSigma _ _ zero zero)
        fn tst6 : Bool := sproj2 _ (lam z : Nat => match z { | zero => Nat | o => Bool }) (mkSigma _ _ (suc zero) true)
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
        let _cons = Term::cons(
            ConHead::new(Ident::new("Cons", Loc::default()), 7),
            (0..delta.len()).rev().map(Term::from_dbi).collect(),
        );
        let _rise = delta.len();
        for b in &gamma2 {
            print!("{}, ", b);
        }
        debug!("");
        // let gamma2 = Ctx(gamma2)
        //     .subst(
        //         // Substitution::one(cons).weaken(rise),
        //         Substitution::raise(rise).cons(cons),
        //     )
        //     .0;
        // gamma1.extend(gamma2);
        // for b in &gamma1 {
        //     print!("{}, ", b);
        // }
        // debug!("");
    }

    #[test]
    fn test_subst_2() {
        // Γ = x' y
        /*         y
            match @0 {
                         x'
         | zero => (suc @0)
                y'          x' y'
         | (suc 0) => (sub @1 @0)
        }
         */
        let ct = Term::match_elim(
            0,
            [
                Case {
                    pattern: Cons(
                        false,
                        ConHead {
                            name: Ident {
                                text: "zero".to_owned(),
                                loc: Loc::default(),
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
                                loc: Loc::default(),
                            },
                            cons_gi: 2,
                        },
                        vec![Var(0)],
                    ),
                    body: Term::cons(
                        ConHead {
                            name: Ident {
                                text: "suc".to_owned(),
                                loc: Loc::default(),
                            },
                            cons_gi: 2,
                        },
                        vec![Term::Redex(
                            Func::Index(3),
                            Ident {
                                text: "sub".to_owned(),
                                loc: Loc::default(),
                            },
                            vec![
                                Elim::App(box Term::from_dbi(1)),
                                Elim::App(box Term::from_dbi(0)),
                            ],
                        )],
                    ),
                },
            ],
        );
        println!("{}", ct);
        let subst = Substitution::one(Term::cons(
            ConHead {
                name: Ident {
                    text: "zero".to_owned(),
                    loc: Loc::default(),
                },
                cons_gi: 1,
            },
            vec![],
        ));
        // .lift_by(1);
        let nct = ct.subst(subst);
        println!("{}", nct);
    }

    #[test]
    fn test_subst_3() {
        // A B C D
        //   ^
        // A Ba Bb Bc C D
        let cons = Term::cons(
            ConHead::new(Ident::new("CC", Loc::default()), 7),
            [2, 1, 3].into_iter().map(Term::from_dbi).collect(),
        );
        // CC B C A
        // CC (Cons Ba Bb Bc) C A
        let term = cons.clone().apply(vec![Term::from_dbi(2)]);
        let cons2 = Term::cons(
            ConHead::new(Ident::new("Cons", Loc::default()), 7),
            (0..3).rev().map(Term::from_dbi).collect(),
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
            [2, 1, 3].into_iter().map(Term::from_dbi).collect(),
        );
        let rc = Substitution::one(cons).cons(cons2);
        debug!("{}", rc);
        debug!("{}", x.subst(rc));
    }

    #[test]
    fn test_subst_4() {
        // Γ = x' y
        /*
                         x'
         | zero => (suc @0)
                y'          x' y'
         | (suc 0) => (sub @1 @0)
        }
         */
        let ct = Term::match_elim(
            0,
            [
                Case {
                    pattern: Cons(
                        false,
                        ConHead {
                            name: Ident {
                                text: "zero".to_owned(),
                                loc: Loc::default(),
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
                                loc: Loc::default(),
                            },
                            cons_gi: 2,
                        },
                        vec![Var(0)],
                    ),
                    body: Term::cons(
                        ConHead {
                            name: Ident {
                                text: "suc".to_owned(),
                                loc: Loc::default(),
                            },
                            cons_gi: 2,
                        },
                        vec![Term::Redex(
                            Func::Index(3),
                            Ident {
                                text: "sub".to_owned(),
                                loc: Loc::default(),
                            },
                            vec![
                                Elim::App(box Term::from_dbi(1)),
                                Elim::App(box Term::from_dbi(0)),
                            ],
                        )],
                    ),
                },
            ],
        );
        println!("{}", ct);
        let subst = Substitution::one(Term::Redex(
            Func::Index(1),
            Ident::new("n1", Loc::default()),
            vec![],
        ));
        // let subst = Substitution::one(Term::cons(
        //     ConHead {
        //         name: Ident {
        //             text: "zero".to_owned(),
        //             loc: Loc::default(),
        //         },
        //         cons_gi: 1,
        //     },
        //     vec![],
        // ));
        let nct = ct.subst(subst);
        println!("{}", nct);
    }

    #[test]
    fn test_subst_in_case_tree() -> eyre::Result<()> {
        let p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        data NilPair : Type
            | nil
            | pair Nat Nat

        fn n0 : Nat := zero
        fn n1 : Nat := (suc n0)
        fn n2 : Nat := (suc n1)
        fn n3 : Nat := (suc n2)
        fn n4 : Nat := (suc n4)
        fn n5 : Nat := (suc n5)
        fn n7 : Nat := (suc (suc (suc (suc n3))))
        fn n10 : Nat := (suc (suc (suc n7)))
       "#,
        )?)?;
        env.check_prog(des.clone())?;
        let con_nil = ConHead::new("nil", 4);
        let pat_nil = Pat::cons(con_nil.clone(), Vec::new());
        let con_pair = ConHead::new("pair", 5);
        let pat_pair = |p1, p2| Pat::cons(con_pair.clone(), vec![Var(p1), Var(p2)]);
        let ct = Term::match_elim(
            0,
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(4, "bar", [3, 2, 1].map(Term::from_dbi)),
                ),
                Case::new(
                    pat_pair(1, 0),
                    Term::fun_app(3, "foo", [5, 1, 0].map(Term::from_dbi)),
                ),
            ],
        );

        let nct = Term::match_elim(
            3,
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(
                        4,
                        "bar",
                        [
                            Term::cons(con_nil.clone(), vec![]),
                            Term::from_dbi(2),
                            Term::from_dbi(1),
                        ],
                    ),
                ),
                Case::new(
                    pat_pair(4, 3),
                    Term::fun_app(
                        3,
                        "foo",
                        [
                            Term::cons(con_pair.clone(), [4, 3].map(Term::from_dbi).to_vec()),
                            Term::from_dbi(4),
                            Term::from_dbi(3),
                        ],
                    ),
                ),
            ],
        );
        let subst = Substitution::one(Term::from_dbi(3));
        let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);
        /*
        subst: cons 3

        bar @4 @3 @2
        foo @1 _  _
        baz @4 _  _
        match @0 {
         | nil => (bar @3 @2 @1)
         | (pair 1 0) => (foo @2 @1 @0)
         | (pair 1 0) => (baz @5 @1 @0)
        }

        bar @3 @2 @1
        foo @0 _  _
        baz @3 _  _
        match @3 {
         | nil => (bar nil @2 @1)
         | (pair 4 3) => (foo @0 @4 @3)
         | (pair 4 3) => (baz (pair 4 3) @4 @3)
        }
         */
        let ct = Term::match_elim(
            0,
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(4, "bar", [3, 2, 1].map(Term::from_dbi)),
                ),
                Case::new(
                    pat_pair(1, 0),
                    Term::fun_app(3, "foo", [2, 1, 0].map(Term::from_dbi)),
                ),
            ],
        );
        let nct = Term::match_elim(
            3,
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(4, "bar", [2, 1, 0].map(Term::from_dbi)),
                ),
                Case::new(
                    pat_pair(4, 3),
                    Term::fun_app(3, "foo", [5, 4, 3].map(Term::from_dbi)),
                ),
            ],
        );
        let subst = Substitution::one(Term::from_dbi(4)).cons(Term::from_dbi(3));
        // let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);
        /*
        subst: cons 4, cons 3

        bar @4 @3 @2
        baz @4 _  _
        match @0 {
         | nil => (bar @3 @2 @1)
         | (pair 1 0) => (baz @5 @1 @0)
        }

        bar @2 @1 @0
        baz @3 _  _
        match @3 {
         | nil => (bar nil @2 @1)
         | (pair 4 3) => (foo @0 @4 @3)
         | (pair 4 3) => (baz (pair 4 3) @4 @3)
        }
         */

        let pair_3_4 = Term::cons(con_pair.clone(), vec![Term::from_dbi(3), Term::from_dbi(4)]);
        let nct = Term::match_case(
            pair_3_4.clone(),
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(4, "bar", [3, 2, 1].map(Term::from_dbi)),
                ),
                Case::new(
                    pat_pair(1, 0),
                    Term::fun_app(3, "foo", [2, 1, 0].map(Term::from_dbi)),
                ),
            ],
        );
        let subst = Substitution::one(pair_3_4.clone());
        let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);

        let nct = Term::match_case(
            pair_3_4.clone(),
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(4, "bar", [2, 1, 0].map(Term::from_dbi)),
                ),
                Case::new(
                    pat_pair(1, 0),
                    Term::fun_app(3, "foo", [6, 1, 0].map(Term::from_dbi)),
                ),
            ],
        );
        let subst = Substitution::one(Term::from_dbi(4)).cons(pair_3_4.clone());
        // let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);
        /*
        subst: Cons((pair @3 @4), Cons(@4, ε))
        bar @4 @3 @2
        foo @1 ?0 ?1
        match @0 {
         | nil => (bar @3 @2 @1)
         | (pair 1 0) => (foo @2 @1 @0)
        }

        bar @2 @1 @0
        foo @4 ?0 ?1
        match (pair @3 @4) {
         | nil => (bar @2 @1 @0)
         | (pair 1 0) => (foo @6 @1 @0)
        }
         */

        let nil_term = pat_nil.clone().into_term();
        let nct = Term::match_case(
            Term::from_dbi(1),
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(
                        4,
                        "bar",
                        [Term::from_dbi(1), nil_term.clone(), Term::from_dbi(0)],
                    ),
                ),
                Case::new(
                    pat_pair(2, 1),
                    Term::fun_app(
                        3,
                        "foo",
                        [
                            pair_3_4.clone().subst(Substitution::raise(1)),
                            Term::from_dbi(2),
                            Term::from_dbi(1),
                        ],
                    ),
                ),
            ],
        );
        let subst = Substitution::one(pair_3_4.clone()).cons(Term::from_dbi(1));
        // let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);
        /*
        subst: Cons(@1, Cons((pair @3 @4), ε))
        bar @4 @3 @2
        foo @1 ?0 ?1
        match @0 {
         | nil => (bar @3 @2 @1)
         | (pair 1 0) => (foo @2 @1 @0)
        }

        bar @2 @1 @0
        foo (pair @3 @4) ?0 ?1
        match @1 {
         | nil => (bar @1 nil @0)
         | (pair 2 1) => (foo (pair @4 @5) @2 @1)
        }
         */

        let nct = Term::match_case(
            pair_3_4.clone(),
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(
                        4,
                        "bar",
                        [Term::from_dbi(2), Term::from_dbi(1), Term::from_dbi(0)],
                    ),
                ),
                Case::new(
                    pat_pair(1, 0),
                    Term::fun_app(
                        3,
                        "foo",
                        [
                            pair_3_4.clone().subst(Substitution::raise(2)),
                            Term::from_dbi(1),
                            Term::from_dbi(0),
                        ],
                    ),
                ),
            ],
        );
        let subst = Substitution::one(pair_3_4.clone()).cons(pair_3_4.clone());
        let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);
        /*
        subst: Cons((pair @3 @4), Cons((pair @3 @4), ε))
        bar @4 @3 @2
        foo @1 ?0 ?1
        match @0 {
         | nil => (bar @3 @2 @1)
         | (pair 1 0) => (foo @2 @1 @0)
        }

        bar @2 @1 @0
        foo (pair @3 @4) ?0 ?1
        match (pair @3 @4) {
         | nil => (bar @2 @1 @0)
         | (pair 1 0) => (foo (pair @5 @6) @1 @0)
        }
         */
        Ok(())
    }

    #[test]
    fn test_subst_in_case_tree_2() -> eyre::Result<()> {
        let p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        data NilPair : Type
            | nil
            | pair Nat Nat
       "#,
        )?)?;
        env.check_prog(des.clone())?;
        let pat_nil = Pat::cons(ConHead::new("nil", 4), Vec::new());
        let con_pair = ConHead::new("pair", 5);
        let pat_pair = |p1, p2| Pat::cons(con_pair.clone(), vec![Var(p1), Var(p2)]);
        let ct = Term::match_elim(
            1,
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(4, "bar", [2, 1, 0].map(Term::from_dbi)),
                ),
                Case::new(
                    pat_pair(2, 1),
                    Term::fun_app(3, "foo", [2, 1, 0].map(Term::from_dbi)),
                ),
            ],
        );
        let nct = Term::match_elim(
            0,
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(4, "bar", [1, 0, 2].map(Term::from_dbi)),
                ),
                Case::new(
                    pat_pair(1, 0),
                    Term::fun_app(3, "foo", [1, 0, 4].map(Term::from_dbi)),
                ),
            ],
        );
        let subst = Substitution::one(Term::from_dbi(3));
        // let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);

        let nct = Term::match_elim(
            4,
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(4, "bar", [1, 0, 3].map(Term::from_dbi)),
                ),
                Case::new(
                    pat_pair(5, 4),
                    Term::fun_app(3, "foo", [5, 4, 3].map(Term::from_dbi)),
                ),
            ],
        );
        let subst = Substitution::one(Term::from_dbi(4)).cons(Term::from_dbi(3));
        // let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);

        let pair_3_4 = Term::cons(con_pair.clone(), vec![Term::from_dbi(3), Term::from_dbi(4)]);
        let nct = Term::match_case(
            Term::from_dbi(0),
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(
                        4,
                        "bar",
                        [
                            Term::from_dbi(1),
                            Term::from_dbi(0),
                            pair_3_4.clone().subst(Substitution::strengthen(1)),
                        ],
                    ),
                ),
                Case::new(
                    pat_pair(1, 0),
                    Term::fun_app(
                        3,
                        "foo",
                        [
                            Term::from_dbi(1),
                            Term::from_dbi(0),
                            pair_3_4.clone().subst(Substitution::raise(1)),
                        ],
                    ),
                ),
            ],
        );
        let subst = Substitution::one(pair_3_4.clone());
        // let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);

        let nct = Term::match_case(
            Term::from_dbi(4),
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(
                        4,
                        "bar",
                        [
                            Term::from_dbi(1),
                            Term::from_dbi(0),
                            Term::cons(
                                con_pair.clone(),
                                vec![Term::from_dbi(3), pat_nil.clone().into_term()],
                            ),
                        ],
                    ),
                ),
                Case::new(
                    pat_pair(5, 4),
                    Term::fun_app(
                        3,
                        "foo",
                        [
                            Term::from_dbi(5),
                            Term::from_dbi(4),
                            Term::cons(
                                con_pair.clone(),
                                vec![
                                    Term::from_dbi(3),
                                    Term::cons(
                                        con_pair.clone(),
                                        vec![Term::from_dbi(5), Term::from_dbi(4)],
                                    ),
                                ],
                            ),
                        ],
                    ),
                ),
            ],
        );
        let subst = Substitution::one(Term::from_dbi(4)).cons(pair_3_4.clone());
        // let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);

        let nct = Term::match_case(
            pair_3_4.clone(),
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(
                        4,
                        "bar",
                        [Term::from_dbi(1), Term::from_dbi(0), Term::from_dbi(1)],
                    ),
                ),
                Case::new(
                    pat_pair(2, 1),
                    Term::fun_app(
                        3,
                        "foo",
                        [Term::from_dbi(2), Term::from_dbi(1), Term::from_dbi(3)],
                    ),
                ),
            ],
        );
        let subst = Substitution::one(pair_3_4.clone()).cons(Term::from_dbi(1));
        // let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);

        let nct = Term::match_case(
            pair_3_4.clone(),
            [
                Case::new(
                    pat_nil.clone(),
                    Term::fun_app(
                        4,
                        "bar",
                        [Term::from_dbi(1), Term::from_dbi(0), pair_3_4.clone()],
                    ),
                ),
                Case::new(
                    pat_pair(2, 1),
                    Term::fun_app(
                        3,
                        "foo",
                        [
                            Term::from_dbi(2),
                            Term::from_dbi(1),
                            pair_3_4.clone().subst(Substitution::raise(2)),
                        ],
                    ),
                ),
            ],
        );
        let subst = Substitution::one(pair_3_4.clone()).cons(pair_3_4.clone());
        let _ = env_logger::try_init();
        debug!("{}", ct);
        let cta = ct.clone().subst(subst);
        debug!("{}", cta);
        assert_eq!(cta, nct);
        Ok(())
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
                            Some(Leaf(Term::cons(con_z, vec![]))),
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
                                pat_z,
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
