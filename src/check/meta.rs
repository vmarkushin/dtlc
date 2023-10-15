use crate::check::state::TypeCheckState;
use crate::check::Result;
use crate::syntax::core::{
    self, Bind, Case, Closure, Elim, Func, Lambda, Pat, Subst, Substitution, Tele, Term, ValData,
    Var,
};
use crate::syntax::{DBI, MI};
use std::{
    fmt::{Debug, Display, Formatter, Write},
    rc::Rc,
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum MetaSol<Val> {
    /// Solved meta, solved at .
    ///
    /// Boxed to make the variable smaller.
    Solved(DBI, Box<Val>),
    /// Not yet solved meta.
    Unsolved,
}

impl<Val> Default for MetaSol<Val> {
    fn default() -> Self {
        MetaSol::Unsolved
    }
}

impl<R, T: Subst<R>> Subst<MetaSol<R>> for MetaSol<T> {
    fn subst(self, subst: Rc<Substitution>) -> MetaSol<R> {
        use MetaSol::*;
        match self {
            Solved(i, t) => MetaSol::solved(i, t.subst(subst)),
            Unsolved => Unsolved,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MetaContext<Val>(Vec<MetaSol<Val>>);

impl<Val> Default for MetaContext<Val> {
    fn default() -> Self {
        MetaContext(Vec::new())
    }
}

impl<Val> MetaSol<Val> {
    pub fn solved(at: DBI, val: Val) -> Self {
        MetaSol::Solved(at, Box::new(val))
    }
}

impl<Val> MetaContext<Val> {
    pub fn solutions(&self) -> &Vec<MetaSol<Val>> {
        &self.0
    }

    pub fn solution(&self, index: MI) -> &MetaSol<Val> {
        &self.solutions()[index]
    }

    pub fn mut_solutions(&mut self) -> &mut Vec<MetaSol<Val>> {
        &mut self.0
    }

    /// Add many unsolved metas to the context.
    pub fn expand_with_fresh_meta(&mut self, meta_count: MI) {
        // debug_assert!(self.solutions().len() <= meta_count);
        let i = self.solutions().len();
        self.mut_solutions()
            .resize_with(i + meta_count, Default::default);
    }

    /// Create a new valid but unsolved meta variable,
    /// used for generating fresh metas during elaboration.
    pub fn fresh_meta(&mut self, new_meta: impl FnOnce(MI) -> Val) -> Val {
        let meta = new_meta(self.solutions().len());
        self.mut_solutions().push(MetaSol::Unsolved);
        meta
    }
}

impl<Val: Display + Debug + Eq> MetaContext<Val> {
    /// Submit a solution to a meta variable to the context.
    pub fn solve_meta(&mut self, meta_index: MI, at: DBI, solution: Val) {
        let meta_solution = &mut self.mut_solutions()[meta_index];
        debug_assert_eq!(meta_solution, &mut MetaSol::Unsolved);
        *meta_solution = MetaSol::solved(at, solution);
    }
}

impl<Val: Display> Display for MetaContext<Val> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use MetaSol::*;
        f.write_char('[')?;
        let solutions = self.solutions();
        let mut iter = solutions.iter().enumerate();
        if let Some((ix, sol)) = iter.next() {
            write!(f, "?{:?}", ix)?;
            if let Solved(i, sol) = sol {
                write!(f, "={}({:?})", sol, i)?;
            }
        }
        for (ix, sol) in iter {
            write!(f, ", ?{:?}", ix)?;
            match sol {
                Solved(i, sol) => write!(f, "={}({:?})", sol, i)?,
                Unsolved => f.write_char(',')?,
            }
        }
        f.write_char(']')
    }
}

/// Somehow like
/// [this](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Reduce.html#Instantiate)
/// in Agda, but different (Agda's instantiates one meta, but this one
/// instantiates the term fully. Maybe this corresponds to `instantiateFull`?).
pub trait HasMeta: Sized {
    /// Inline solved metas inside `self`.
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self>;
}

impl<T: HasMeta> HasMeta for Vec<T> {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        let mut r = Vec::with_capacity(self.len());
        for t in self {
            let t = t.inline_meta(tcs)?;
            r.push(t);
        }
        Ok(r)
    }
}

impl HasMeta for ValData {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        let args = self.args.inline_meta(tcs)?;
        Ok(ValData::new(self.def, args))
    }
}

impl HasMeta for Elim {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        match self {
            Elim::App(a) => a.inline_meta(tcs).map(Elim::App),
            Elim::Proj(p) => Ok(Elim::Proj(p)),
        }
    }
}

impl<T: HasMeta> HasMeta for Box<T> {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        Ok(Box::new((*self).inline_meta(tcs)?))
    }
}

impl HasMeta for Lambda {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        Ok(Lambda(self.0.inline_meta(tcs)?, self.1.inline_meta(tcs)?))
    }
}

impl HasMeta for Func {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        match self {
            Func::Lam(lam) => Ok(Func::Lam(lam.inline_meta(tcs)?)),
            x => Ok(x),
        }
    }
}

impl HasMeta for Pat {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        use crate::syntax::pattern::Pat::*;
        match self {
            p @ Var(_) => Ok(p),
            Wildcard => Ok(Wildcard),
            Absurd => Ok(Absurd),
            Cons(forced, head, args) => Ok(Cons(forced, head, args.inline_meta(tcs)?)),
            Forced(t) => Ok(Forced(t.inline_meta(tcs)?)),
        }
    }
}

impl HasMeta for Case {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        Ok(Case {
            pattern: self.pattern.inline_meta(tcs)?,
            body: self.body.inline_meta(tcs)?,
        })
    }
}

impl HasMeta for Tele {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        self.0.inline_meta(tcs).map(Tele)
    }
}

impl HasMeta for Term {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        match self {
            // Prefer not to simplify
            // Term::Meta(mi, elims) => solve_meta(tcs, mi, elims),
            Term::Universe(l) => Ok(Term::Universe(l)),
            Term::Data(info) => info.inline_meta(tcs).map(Term::Data),
            Term::Pi(t, clos) => {
                let t = t.unboxed().inline_meta(tcs)?;
                let clos = clos.inline_meta(tcs)?;
                Ok(Term::Pi(t.boxed(), clos))
            }
            Term::Lam(Lambda(t, clos)) => {
                let t = t.unboxed().inline_meta(tcs)?;
                let clos = clos.inline_meta(tcs)?;
                Ok(Term::Lam(Lambda(t.boxed(), clos)))
            }
            Term::Cons(c, ts) => ts.inline_meta(tcs).map(|ts| Term::Cons(c, ts)),
            Term::Var(Var::Meta(mi), elims) => {
                let sol = solve_meta(tcs, mi, elims)?;
                tcs.simplify(sol)
            }
            Term::Var(head, args) => args.inline_meta(tcs).map(|a| Term::Var(head, a)),
            Term::Id(id) => Ok(Term::Id(core::Id::new(
                id.tele.inline_meta(tcs)?,
                id.ty.inline_meta(tcs)?,
                id.paths.inline_meta(tcs)?,
                id.a1.inline_meta(tcs)?,
                id.a2.inline_meta(tcs)?,
            ))),
            Term::Refl(val) => {
                let val = val.inline_meta(tcs)?;
                Ok(Term::Refl(val))
            }
            Term::Redex(func, id, elims) => {
                let func = func.inline_meta(tcs)?;
                let elims = elims.inline_meta(tcs)?;
                Ok(Term::Redex(func, id, elims))
            }
            Term::Match(term, term_ty, cases) => {
                let cases = cases.inline_meta(tcs)?;
                let term_ty = term_ty.inline_meta(tcs)?;
                Ok(Term::Match(term.inline_meta(tcs)?, term_ty, cases))
            }
            Term::Ap(tele, fs, ps) => {
                let tele = tele.inline_meta(tcs)?;
                let fs = fs.inline_meta(tcs)?;
                let ps = ps.inline_meta(tcs)?;
                Ok(Term::Ap(tele, fs, ps))
            }
        }
    }
}

impl<T: HasMeta> HasMeta for Bind<T> {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        let ty = self.ty.inline_meta(tcs)?;
        Ok(Bind::identified(self.licit, self.name, ty, self.ident))
    }
}

impl HasMeta for Closure {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        tcs.unify_depth_inc(1);
        let closure = match self {
            Closure::Plain(body) => {
                let res = body.inline_meta(tcs);
                tcs.unify_depth_dec(1);
                let body = res?;
                Closure::Plain(body)
            }
        };
        Ok(closure)
    }
}

fn solve_meta(tcs: &mut TypeCheckState, mut mi: MI, elims: Vec<Elim>) -> Result<Term> {
    use MetaSol::*;
    let (_ix, sol) = loop {
        match tcs.meta_ctx().solution(mi) {
            Solved(ix, sol) if sol.is_meta() => {
                let (idx, elims) = sol.as_meta().unwrap();
                assert!(elims.is_empty());
                if idx == mi {
                    break (*ix, sol.clone());
                }
                mi = idx;
            }
            Solved(ix, sol) => break (*ix, sol.clone()),
            Unsolved => return Ok(Term::meta_with(mi, elims)),
            // Unsolved => return Err(Error::MetaUnsolved(mi)),
        };
    };
    let elims = elims.inline_meta(tcs)?;
    Ok(sol.apply_elim(elims))
}

impl<T: HasMeta, U: HasMeta> HasMeta for (T, U) {
    fn inline_meta(self, tcs: &mut TypeCheckState) -> Result<Self> {
        let (t, u) = self;
        Ok((t.inline_meta(tcs)?, u.inline_meta(tcs)?))
    }
}
