use crate::check::meta::HasMeta;
use crate::check::{Error, Result, TypeCheckState};
use crate::syntax::abs::{Expr, Pat as PatA, Tele as TeleA};
use crate::syntax::core::{
    build_subst, Case, Ctx, DeBruijn, Decl, Pat, PrimSubst, Subst, Substitution, Tele, Term, Val,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraints(pub Vec<Constraint>);

impl Constraints {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn iter(&self) -> impl Iterator<Item = &Constraint> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = Constraint> {
        self.0.into_iter()
    }
}

impl Iterator for Constraints {
    type Item = Constraint;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}

impl Subst for Constraints {
    fn subst(self, subst: Rc<PrimSubst<Term>>) -> Self {
        let mut prev_tele_len = 0;
        Self(
            self.0
                .into_iter()
                .enumerate()
                .map(|(i, c)| {
                    if i == 0 {
                        let new_c = c.subst(subst.clone());
                        prev_tele_len = new_c.ty.tele_len();
                        new_c
                    } else {
                        c.subst(subst.clone().lift_by(prev_tele_len))
                    }
                })
                .collect(),
        )
    }
}

impl Display for Constraints {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.iter().join(" "))
    }
}

/// \[E\]q ~> rhs
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    /// Constraints `[t /? p]`.
    constraints: Vec<Constraint>,
    // constraints: Constraints,
    /// Patterns given by the user.
    user_pats: Vec<PatA>,
    /// Right-hand side
    rhs: Option<Expr>,
}

impl Display for Clause {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "| {} {}",
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
// A
// x / C n m => CC n m
// C i j / C n m => CC n m
// Aa Ab
// i / n, j / m => CC n m
// 4   0  6   1
// 0 => 4, 6 => 1

impl Display for LshProblem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "P = {{")?;
        for cls in &self.clauses {
            writeln!(f, "{}", cls)?;
        }
        writeln!(f, "}}")?;
        writeln!(f, "pats: {}", self.pats.iter().join(", "))?;
        writeln!(f, "target: {}", self.target)?;
        write!(f, "vars: {}", self.vars.iter().join(", "))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LshProblem {
    /// User patterns with constraints. P = {q_vec_i -> rhs_i | i = 1...n}.
    clauses: Vec<Clause>,
    /// Variables referring to Γ being matched on.
    vars: Vec<DBI>,
    /// Core patterns being refined.
    pats: Vec<Pat>,
    /// Ambient context.
    // gamma: Ctx,
    /// Target type `rhs` should be equal too.
    target: Term,
}

/// Potentially partial case tree.
#[derive(Debug, Clone)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub enum CaseTree {
    Leaf(Term),
    Case(DBI, Vec<(Pat, Option<CaseTree>)>),
}

impl CaseTree {
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
                Term::Match(i, cases)
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
                    .merge_join_by(cases_b, |(pat_a, ct_a), (pat_b, ct_b)| {
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
                            (a, b) => panic!("Can't merge patterns in a case tree"),
                        }
                    })
                    .map(|choice| match choice {
                        EitherOrBoth::Both((pat_a, ct_a), (pat_b, ct_b)) => {
                            debug_assert_eq!(pat_a, pat_b);
                            let ct = match (ct_a, ct_b) {
                                (Some(ct_a), Some(ct_b)) => Some(ct_a.merge(ct_b)),
                                (a, None) => panic!(),
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

/*
fn max (n : Nat) (m : Nat) : Nat => match n, m
      | Z,        j       => j
      | i,        Z       => i
      | (S i),    (S j)   => S (max i j)

Problem:
(m : Nat) (n : Nat) |- P | max m n : Nat

C1:
E = [m /? Z, n /? j]
Initial problem:
    | [m /? Z],     [n /? j] => j

Step 1 (split m):
    | [Z     /? Z], [n /? j] => j
-x> | [(S p) /? Z], [n /? j] => j (remove this case, because of the absurdity pattern)
Step 2 (subst j with n):
    | [Z]           [n]      => n
(no patterns left, finish)

CT1 = match m
      | Z => n

C2:
E = [m /? i, n /? Z]
Initial problem:
    | [m /? i],     [n /? Z]     => i

Step 1 (split m):
    | [Z   /? i],   [n /? Z] => i
    | [S p /? i],   [n /? Z] => i
Step 2 (subst i with Z and S p):
    | [Z]           [n /? Z] => Z
    | [S p]         [n /? Z] => (S p)
Step 3 (split n):
    | [Z]           [Z     /? Z] => Z
-x> | [Z]           [(S q) /? Z] => Z
    | [S p]         [Z     /? Z] => (S p)
-x> | [S p]         [(S q) /? Z] => (S p)
Step 4 (subst):
    | [Z]           [Z]          => Z
    | [S p]         [Z]          => (S p)

CT2 = match m
      | Z   => match n
               | Z => Z
      | S p => match n
               | Z => (S p)

C3:
E = [m /? (S i), n /? (S j)]
Initial problem:
    | [m /? (S i)], [n /? (S j)] => S (max i j)

Step 1 (split m):
-x> | [Z     /? (S i)], [n /? (S j)] => S (max i j)
    | [(S p) /? (S i)], [n /? (S j)] => S (max i j)
Simpl:
    | [p /? i],         [n /? (S j)] => S (max i j)
Step 2 (split n):
-x> | [p /? i],         [Z     /? (S j)] => S (max i j)
    | [p /? i],         [(S q) /? (S j)] => S (max i j)
Simpl:
    | [p /? i],         [q /? j]         => S (max i j)
Step 3 (subst):
    | [p],              [q]              => S (max p q)

CT3 = match m
      | S p => match n
               | S q => S (max p q)

Merge:
CT = match m
     | Z   => n
     | S p => match n
              | Z   => (S p)
              | S q => S (max p q)


Example 2:
fn non_triv (n : Nat) : Nat =>
    match n
        | (S (S i)) => S (S Z)
        | (S i)     => S Z
        | Z         => Z

    | [n /? (S (S i))] => S (S Z)

 x  | [Z /? (S (S i))] => S (S Z)
    | [S p /? (S (S i))] => S (S Z)

    | [p /? (S i)] => S (S Z)

 x  | [Z /? (S i)] => S (S Z)
    | [S pp /? (S i)] => S (S Z)

    | [pp /? i] => S (S Z)

CT1 = match n
      | S p => match p
               | S pp => S (S Z)

CT2 = match n
      | S p => S Z

CT3 = match n
      | Z => Z

Final result:
CT  = match n
      | S p => match p
               | S pp => S (S Z)
               | p    => S Z
      | Z => Z


*/
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
        // let subst = Substitution::raise(vars_len);
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
            // self.clause.constraints = self.clause.constraints.clone().subst(subst.clone());
            clause.constraints.extend(constraints);

            // Remove handled user patterns
            clause.user_pats =
                clause.user_pats[(clause.user_pats.len() - user_pats.len())..].to_vec();
            if !clause.user_pats.is_empty() {
                return Err(Error::TooManyPatterns);
            }
        }
        // self.pats = self.pats.clone().subst(subst);
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
            // Split rule
            match &ct.ty {
                Term::Whnf(Val::Data(data)) => {
                    let x = ct.term.dbi_view().unwrap();
                    let v_vec = &data.args;
                    match tcs.def(data.def).clone() {
                        Decl::Data(data) => {
                            if data.conses.is_empty() {
                                if !ct.pat.is_abusrd() {
                                    return Err(Error::ExpectedAbsurd(box ct.pat.clone()));
                                }
                                // SplitEmpty rule
                                if clause_1.rhs.is_some() {
                                    return Err(Error::UnexpectedRhs);
                                }
                                return Ok(CaseTree::Case(x, Vec::new()));
                            }

                            let mut ct_clauses = Vec::new();
                            let conses = data
                                .conses
                                .iter()
                                .map(|c| tcs.def(*c).as_cons().clone())
                                .collect::<Vec<_>>();
                            for (cons_ix, cons) in conses.into_iter().enumerate() {
                                println!("\nSplitting constraint {} with {}", ct, cons.name);
                                println!("Problem before: {}", &self);
                                println!("Context before {}", tcs.gamma);

                                // let delta = &data.params;
                                let delta_i = &cons.params;
                                let delta_tick_i = Ctx(delta_i.clone())
                                    .subst(Substitution::parallel(v_vec.into_iter().cloned()))
                                    .0;
                                let mut gamma1 = tcs.gamma.clone();
                                let (xx, mut gamma2) = gamma1.split(x);
                                debug_assert_eq!(xx.ty, ct.ty);
                                gamma1.extend(delta_tick_i.clone());
                                let delta_tick_hat_i = (0..delta_tick_i.len())
                                    .rev()
                                    .map(|i| Term::from_dbi(i))
                                    .collect::<Vec<_>>();
                                let cons_gi = cons.data_gi + cons_ix + 1;
                                let con_head = ConHead::new(cons.name.clone(), cons_gi);
                                let alpha = Substitution::raise(delta_tick_i.len())
                                    .cons(Term::cons(con_head.clone(), delta_tick_hat_i.clone()));
                                gamma2 = gamma2.subst(alpha.clone());
                                println!("α = {}", &alpha);
                                let beta = alpha.clone().lift_by(gamma2.len());
                                println!("β = {}", &beta);
                                let target_new = self.target.clone().subst(beta.clone());
                                let clauses_new = self
                                    .clauses
                                    .clone()
                                    .into_iter()
                                    .filter_map(|mut clause| {
                                        clause.constraints =
                                            clause.constraints.clone().subst(beta.clone());
                                        print!("transforming clause: {}", &clause);
                                        let mut constraints_new = Vec::new();
                                        for cst in clause.constraints.clone() {
                                            match (cst.term, cst.pat) {
                                                (
                                                    Term::Whnf(Val::Cons(
                                                        con_head,
                                                        delta_tick_hat_i,
                                                    )),
                                                    PatA::Cons(false, pat_head, es),
                                                ) => {
                                                    if con_head.cons_gi != pat_head.cons_gi {
                                                        println!("  <-- removed");
                                                        return None;
                                                    }
                                                    debug_assert_eq!(
                                                        delta_tick_hat_i.len(),
                                                        es.len()
                                                    );
                                                    constraints_new.extend(
                                                        delta_tick_hat_i
                                                            .into_iter()
                                                            .zip(es.into_iter())
                                                            .zip(delta_tick_i.iter().cloned())
                                                            .map(|((delta_tick_hat_i, pat), bind)| {
                                                                Constraint::new(
                                                                    pat,
                                                                    delta_tick_hat_i,
                                                                    bind.ty,
                                                                )
                                                            }),
                                                    );
                                                }
                                                (t, p) => constraints_new
                                                    .push(Constraint::new(p, t, cst.ty)),
                                            };
                                        }
                                        println!();

                                        clause.constraints = constraints_new;
                                        Some(clause)
                                    })
                                    .collect();
                                let pats_new = self.pats.clone().subst(beta);
                                let mut lhs_new = self.clone();
                                lhs_new.target = target_new;
                                lhs_new.pats = pats_new;
                                lhs_new.clauses = clauses_new;
                                gamma1.extend(gamma2);
                                // let pat = lhs_new.pats[ct_idx].clone();
                                let gamma_new = gamma1;
                                let ct = tcs.under_ctx(gamma_new, |tcs| {
                                    println!("Problem after: {}", &lhs_new);
                                    println!("Context after {}", tcs.gamma);

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
                            return Ok(CaseTree::Case(x, ct_clauses));
                        }
                        _ => unreachable!("Data type definition expected"),
                    }
                }
                _ => unreachable!("Attempt to split on non-data type"),
            }
        } else {
            // Done rule
            if clause_1
                .constraints
                .iter()
                .all(|x| x.pat.is_var() && (x.term.is_eta_var() || x.term.is_cons()))
            {
                let refined_user_pats = Rc::new(
                    clause_1
                        .constraints
                        .iter()
                        .map(|c| c.gen_abs_subst(tcs))
                        .collect::<HashMap<_, _>>(),
                );
                let mut rhs1 = clause_1.rhs.clone().unwrap();
                println!("rhs = {}", rhs1);
                rhs1.subst_abs(refined_user_pats.clone());
                println!("rhs_refined = {}", rhs1);

                let checked_rhs = tcs.check(&rhs1, &tcs.simplify(self.target)?)?.ast;
                return Ok(CaseTree::Leaf(checked_rhs));
            } else {
                panic!("wtf?");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::Unify;
    use crate::parser::Parser;
    use crate::syntax::core::{Elim, ValData};
    use crate::syntax::desugar::desugar_prog;
    use crate::syntax::Plicitness::Explicit;
    use crate::syntax::{Bind, ConHead, Ident, Loc};
    use crate::{pct, typeck};

    #[test]
    fn test_fail_build_case_tree() -> eyre::Result<()> {
        let _ = env_logger::try_init();
        let mut p = Parser::default();
        let mut env = TypeCheckState::default();
        env.indentation_size(2);
        let mut des = desugar_prog(p.parse_prog(
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
        let mut des = desugar_prog(p.parse_prog(
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
        let mut des = desugar_prog(p.parse_prog(
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
        let mut des = desugar_prog(p.parse_prog(
            r#"
        data Nat : Type
            | zero
            | suc Nat

        fn max (x : Nat) (y : Nat) : Nat := match x, y {
              | x,        zero    => x
              | zero,     y       => y
              | (suc x),  (suc y) => suc x
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
             | (suc 0) => (suc @1)
            }
        }
         */
        let cte = Term::mat(
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
                        1,
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
                                    vec![Term::from_dbi(1)],
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
        let cte = Term::mat(0, []);
        assert_eq!(ct, cte);

        Ok(())
    }

    #[test]
    fn test_eval_case_tree() -> eyre::Result<()> {
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
        let val = pct!(p, des, env, "main");
        let val1 = pct!(p, des, env, "(suc (suc zero))");
        Val::unify(&mut env, &val, &val1)?;
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
        println!();
        let b = gamma.remove(1);
        let mut gamma1 = gamma.clone();
        let mut gamma2 = gamma1.split_off(1);
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
        println!();
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
        println!();
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
        let term = cons.apply(vec![Term::from_dbi(2)]);
        let cons2 = Term::cons(
            ConHead::new(Ident::new("Cons", Loc::default()), 7),
            (0..3).rev().map(|i| Term::from_dbi(i)).collect(),
        );
        let rise = 3;
        println!("{}", term);
        let term = term.subst(
            // Substitution::one(cons).weaken(rise),
            Substitution::raise(rise).cons(cons2).lift_by(2),
        );
        println!("{}", term);
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
            1,
            vec![(
                // Γ = (n : Nat)
                pat_z.clone(),
                Some(Leaf(Term::from_dbi(0))),
            )],
        );
        // Γ = (m : Nat) (n : Nat)
        let ct_2 = Case(
            1,
            vec![
                (
                    // Γ = (n : Nat)
                    pat_z.clone(),
                    Some(Case(
                        0,
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
                        1,
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
            1,
            vec![(
                // Γ = (n : Nat) (p : Nat)
                pat_s(0),
                Some(Case(
                    1,
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
            1,
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
                        1,
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
