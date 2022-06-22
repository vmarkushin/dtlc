use crate::check::CaseTree;
use crate::syntax::core::term::{Case, Pat};
use crate::syntax::core::{Closure, DeBruijn, Elim, Func, Lambda, Term, Val};

pub trait FoldVal {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E>;
}

impl<T: FoldVal> FoldVal for [T] {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        self.iter().try_fold(init, |a, v| v.try_fold_val(a, f))
    }
}

impl FoldVal for Lambda {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        self.1.try_fold_val(self.0.ty.try_fold_val(init, f)?, f)
    }
}

impl FoldVal for Func {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        match self {
            Func::Index(_) => Ok(init),
            Func::Lam(lam) => lam.try_fold_val(init, f),
        }
    }
}

impl FoldVal for Pat {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        match self {
            Pat::Var(_) => Ok(init),
            Pat::Wildcard => Ok(init),
            Pat::Absurd => Ok(init),
            Pat::Cons(_, _, args) => args.try_fold_val(init, f),
            Pat::Forced(term) => term.try_fold_val(init, f),
        }
    }
}

impl FoldVal for Case {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        self.pattern
            .try_fold_val(self.body.try_fold_val(init, f)?, f)
    }
}

impl FoldVal for CaseTree {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        match self {
            CaseTree::Leaf(t) => t.try_fold_val(init, f),
            CaseTree::Case(x, cs) => Val::from_dbi(*x).try_fold_val(cs.try_fold_val(init, f)?, f),
        }
    }
}

impl FoldVal for Term {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        use Term::*;
        match self {
            Whnf(val) => val.try_fold_val(init, f),
            Redex(func, _, args) => args.try_fold_val(func.try_fold_val(init, f)?, f),
            Match(_, cases) => cases.try_fold_val(init, f),
        }
    }
}

impl FoldVal for Elim {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        match self {
            Elim::App(a) => a.try_fold_val(init, f),
            Elim::Proj(..) => Ok(init),
        }
    }
}

impl FoldVal for Closure {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        match self {
            Closure::Plain(t) => t.try_fold_val(init, f),
        }
    }
}

impl FoldVal for Val {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        use Val::*;
        let init = f(init, self)?;
        match self {
            Cons(_, v) => v.try_fold_val(init, f),
            Data(i) => i.args.try_fold_val(init, f),
            Universe(..) => Ok(init),
            Pi(p, clos) => clos.try_fold_val(p.ty.try_fold_val(init, f)?, f),
            Lam(Lambda(p, clos)) => clos.try_fold_val(p.ty.try_fold_val(init, f)?, f),
            Var(_, v) | Meta(_, v) => v.try_fold_val(init, f),
        }
    }
}

impl<A: FoldVal, B: FoldVal> FoldVal for (A, B) {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        self.0.try_fold_val(self.1.try_fold_val(init, f)?, f)
    }
}

impl<T: FoldVal> FoldVal for Option<T> {
    fn try_fold_val<E, R>(
        &self,
        init: R,
        f: impl Fn(R, &Val) -> Result<R, E> + Copy,
    ) -> Result<R, E> {
        match self {
            Some(t) => t.try_fold_val(init, f),
            None => Ok(init),
        }
    }
}
