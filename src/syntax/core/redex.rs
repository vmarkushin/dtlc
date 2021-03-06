use super::Term;
use crate::syntax::core::subst::{PrimSubst, Substitution};
use crate::syntax::core::term::Lambda;
use crate::syntax::core::{Closure, Elim, Func, Val, ValData};
use crate::syntax::{Bind, Ident, GI};
use std::rc::Rc;

impl Term {
    /// Use `Term` instead of `Self` to emphasize that it's not `Elim`.
    pub fn apply(self, args: Vec<Term>) -> Self {
        self.apply_elim(args.into_iter().map(Elim::app).collect())
    }

    pub fn apply_elim(self, mut args: Vec<Elim>) -> Self {
        if args.is_empty() {
            return self;
        }
        match self {
            Term::Whnf(Val::Var(f, mut a)) => {
                a.append(&mut args);
                Term::Whnf(Val::Var(f, a))
            }
            Term::Whnf(Val::Meta(m, mut a)) => {
                a.append(&mut args);
                Term::meta(m, a)
            }
            Term::Whnf(Val::Lam(lam)) => Term::Redex(Func::Lam(lam), Ident::new("<λ>", 0..0), args),
            Term::Whnf(Val::Cons(c, mut a)) => {
                let mut iter = args.into_iter();
                match iter.next() {
                    None => Term::cons(c, a),
                    Some(Elim::App(arg)) => {
                        a.push(*arg);
                        Term::cons(c, a).apply_elim(iter.collect())
                    }
                    Some(Elim::Proj(_field)) => {
                        unimplemented!()
                    }
                }
            }
            Term::Redex(Func::Index(f), id, a) => def_app(f, id, a, args),
            Term::Redex(Func::Lam(lam), id, mut a) => {
                a.append(&mut args);
                Term::Redex(Func::Lam(lam), id, a)
            }
            e => panic!("Cannot eliminate `{}`.", e),
        }
    }
}

/// Application on a definition.
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.html#defApp).
pub fn def_app(f: GI, id: Ident, mut a: Vec<Elim>, mut args: Vec<Elim>) -> Term {
    a.append(&mut args);
    Term::Redex(Func::Index(f), id, a)
}

/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.Class.html#Subst).
pub trait Subst<T: Sized = Self, A = Term>: Sized {
    /// Apply a substitution to an open term.
    fn subst(self, subst: Rc<PrimSubst<A>>) -> T;
}

impl Subst for Term {
    fn subst(self, subst: Rc<Substitution>) -> Term {
        match self {
            Term::Whnf(n) => n.subst(subst),
            Term::Redex(Func::Index(f), id, args) => def_app(f, id, vec![], args.subst(subst)),
            Term::Redex(Func::Lam(lam), id, args) => {
                Term::Redex(Func::Lam(lam.subst(subst.clone())), id, args.subst(subst))
            }
        }
    }
}

impl Subst for Elim {
    fn subst(self, subst: Rc<Substitution>) -> Elim {
        match self {
            Elim::App(term) => Elim::app(term.subst(subst)),
            e => e,
        }
    }
}

impl Subst for Lambda {
    fn subst(self, subst: Rc<PrimSubst<Term>>) -> Self {
        match self {
            Lambda(arg, closure) => Lambda(
                arg.unboxed().subst(subst.clone()).boxed(),
                closure.subst(subst),
            ),
        }
    }
}

impl Subst<Term> for Val {
    fn subst(self, subst: Rc<Substitution>) -> Term {
        match self {
            Val::Pi(arg, closure) => Term::pi2(
                arg.unboxed().subst(subst.clone()).boxed(),
                closure.subst(subst),
            ),
            Val::Lam(lam) => Term::Whnf(Val::Lam(lam.subst(subst))),
            Val::Cons(name, a) => Term::cons(name, a.subst(subst)),
            Val::Universe(n) => Term::universe(n),
            Val::Data(info) => Term::data(info.subst(subst)),
            Val::Meta(m, a) => Term::meta(m, a.subst(subst)),
            Val::Var(f, args) => subst.lookup(f).apply_elim(args.subst(subst)),
        }
    }
}

impl Subst for Closure {
    fn subst(self, subst: Rc<Substitution>) -> Self {
        match self {
            Closure::Plain(body) => Self::plain(body.subst(subst.lift_by(1))),
        }
    }
}

/// For `Tele`.
impl<R, T: Subst<R>> Subst<Vec<R>> for Vec<T> {
    fn subst(self, subst: Rc<Substitution>) -> Vec<R> {
        self.into_iter().map(|e| e.subst(subst.clone())).collect()
    }
}

impl<A, B, X: Subst<A>, Y: Subst<B>> Subst<(A, B)> for (X, Y) {
    fn subst(self, subst: Rc<Substitution>) -> (A, B) {
        let (x, y) = self;
        (x.subst(subst.clone()), y.subst(subst))
    }
}

impl<R, T: Subst<R>> Subst<Bind<R>> for Bind<T> {
    fn subst(self, subst: Rc<Substitution>) -> Bind<R> {
        self.map_term(|t| t.subst(subst))
    }
}

impl Subst for ValData {
    fn subst(self, subst: Rc<Substitution>) -> Self {
        ValData::new(self.def, self.args.subst(subst))
    }
}
