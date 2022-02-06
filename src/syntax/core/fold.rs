use crate::syntax::core::{Closure, Elim, Func, Lambda, Term, Val};

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
