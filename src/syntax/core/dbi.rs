use std::rc::Rc;

use crate::syntax::core::{subst::PrimSubst, Elim, Term, Val};
use crate::syntax::DBI;

pub trait DeBruijn {
    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.DeBruijn.html#deBruijnView).
    fn dbi_view(&self) -> Option<DBI>;

    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.DeBruijn.html#deBruijnVar).
    fn from_dbi(dbi: DBI) -> Self;
}

impl DeBruijn for Val {
    fn dbi_view(&self) -> Option<DBI> {
        match self {
            Val::Var(i, v) if v.is_empty() => Some(*i),
            _ => None,
        }
    }

    fn from_dbi(dbi: DBI) -> Self {
        Val::Var(dbi, Default::default())
    }
}

impl DeBruijn for Elim {
    fn dbi_view(&self) -> Option<DBI> {
        match self {
            Elim::App(a) => a.dbi_view(),
            Elim::Proj(..) => None,
        }
    }

    fn from_dbi(dbi: DBI) -> Self {
        Elim::app(DeBruijn::from_dbi(dbi))
    }
}

impl DeBruijn for Term {
    fn dbi_view(&self) -> Option<DBI> {
        match self {
            Term::Whnf(w) => w.dbi_view(),
            Term::Redex(..) => None,
        }
    }

    fn from_dbi(dbi: DBI) -> Self {
        Term::Whnf(DeBruijn::from_dbi(dbi))
    }
}

impl<T: DeBruijn> PrimSubst<T> {
    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#%2B%2B%23).
    pub fn concat(ts: impl DoubleEndedIterator<Item = T>, to: Rc<Self>) -> Rc<Self> {
        ts.rfold(to, Self::cons)
    }

    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#parallelS).
    pub fn parallel(ts: impl DoubleEndedIterator<Item = T>) -> Rc<Self> {
        Self::concat(ts, Default::default())
    }

    /// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#consS).
    pub fn cons(self: Rc<Self>, t: T) -> Rc<Self> {
        match (t.dbi_view(), &*self) {
            (Some(n), PrimSubst::Weak(m, rho)) if n + 1 == *m => {
                rho.clone().lift_by(1).weaken(*m - 1)
            }
            _ => Rc::new(PrimSubst::Cons(t, self)),
        }
    }
}
