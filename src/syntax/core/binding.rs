use std::fmt::{Display, Formatter};
use std::rc::Rc;
use itertools::Either;
use crate::syntax::core::{Bind, Boxed, Closure, Ctx, DeBruijn, Elim, Func, Id, Lambda, Name, PrimSubst, Subst, SubstCtx, SubstWith, Tele, Term, Type, ValData, Var};
use crate::syntax::{DBI, UID};
use crate::syntax::pattern::Pat;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Unbind(pub UID);
pub type UnbindSubst = PrimSubst<Unbind>;

impl DeBruijn for Unbind {
    fn dbi_view(&self) -> Option<DBI> {
        None
    }

    fn from_dbi(dbi: DBI) -> Self {
        panic!("Unbind::from_dbi is not definable")
    }
}

impl Display for Unbind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unbind({})", self.0)
    }
}

impl<C> SubstWith<Unbind, C> for Unbind {
    fn subst_with(self, _subst: Rc<UnbindSubst>, _tcs: &mut C) -> Unbind {
        self
    }
}

impl<C: SubstCtx> SubstWith<Unbind, C, Term> for Var {
    fn subst_with(self, subst: Rc<UnbindSubst>, state: &mut C) -> Term {
        match self {
            Var::V(Name::Bound(f), twin) => {
                let either = subst
                    .lookup_with_impl2::<C>(f, state);
                match either {
                    Either::Left(Unbind(uid)) => {
                        Term::Var(Var::V(Name::Free(uid), twin), vec![])
                    }
                    Either::Right(t) => { t }
                }
            }
            v => Term::Var(v, vec![]),
        }
    }
}

impl<C> SubstWith<Unbind, C> for Pat<DBI, Term>
where
    C: SubstCtx,
{
    fn subst_with(self, subst: Rc<PrimSubst<Unbind>>, tcs: &mut C) -> Self {
        match self {
            Pat::Absurd => Pat::Absurd,
            Pat::Var(v) => {
                todo!()
                // let t = subst.lookup_with(v, tcs);
                // if let Some(dbi) = t.dbi_view() {
                //     Pat::Var(dbi)
                // } else {
                //     Pat::Var(v)
                // }
            }
            Pat::Cons(f, c, pats) => {
                let mut pats_new = Vec::with_capacity(pats.len());
                let mut i = None::<usize>;
                for (pi, p) in pats.into_iter().rev().enumerate() {
                    let np = match p {
                        Pat::Var(v) => {
                            if pi == 0 {
                                todo!()
                                // let t = subst.lookup_with(v, tcs);
                                // match t.dbi_view() {
                                //     Some(nv) => {
                                //         i = Some(nv);
                                //         Pat::Var(nv)
                                //     }
                                //     _ => Pat::Var(v),
                                // }
                            } else if let Some(j) = i {
                                i = Some(j + 1);
                                Pat::Var(j + 1)
                            } else {
                                Pat::Var(v)
                            }
                        }
                        Pat::Absurd => panic!(),
                        Pat::Wildcard => panic!(),
                        Pat::Cons(..) => {
                            panic!("substitution in case trees with nested conses is not allowed")
                        }
                        Pat::Forced(t) => Pat::Forced(t.subst_with(subst.clone(), tcs)),
                    };
                    pats_new.insert(0, np);
                }
                Pat::Cons(f, c, pats_new)
            }
            Pat::Forced(t) => Pat::Forced(t.subst_with(subst, tcs)),
            Pat::Wildcard => Pat::Wildcard,
        }
    }
}

pub fn unbind_closed<C: SubstCtx>(t: Term, tcs: &mut C, limit: usize) -> (Tele, Term) {
    let (tele, t) = t.tele_view_n(limit);
    let tele_unbound = tele.into_iter().map(|b| {
        b.unbind(tcs)
    }).collect::<Tele>();
    let subst = PrimSubst::parallel(tele_unbound.clone().into_iter().map(|b| Unbind(b.name)).rev());
    let body_free = t.subst_with(subst, tcs);
    (tele_unbound, body_free)
}

pub trait Bindable
where
    Self: Sized,
{
    type Out;

    fn unbind<C: SubstCtx>(self, uid: UID, ctx: &mut C) -> (Bind, Self::Out);

    fn unbind_n<C: SubstCtx>(self, uid: UID, ctx: &mut C, limit: usize) -> (Vec<Bind>, Self::Out) {
        unimplemented!()
    }

    fn unbind_open_with<C: SubstCtx>(self, uid: UID, ctx: &mut C) -> Self::Out;

    fn unbind_open<C: SubstCtx>(self, uid: UID, ctx: &mut C) -> (UID, Self::Out) {
        let uid = ctx.fresh_uid();
        let out = self.unbind_open_with(uid, ctx);
        (uid, out)
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use super::*;

    struct MockSubstCtx {
        uid: Cell<UID>,
    }

    impl MockSubstCtx {
        fn reset(&self) {
            self.uid.set(0);
        }
    }

    impl SubstCtx for MockSubstCtx {
        fn fresh_uid(&mut self) -> UID {
            self.uid.update(|x| x + 1)
        }

        fn next_fresh_uid(&mut self) -> UID {
            self.uid.get()
        }
    }

    #[test]
    fn test_unbind_closed() {
        let long_term = Term::lams(
            vec![
                Bind::unnamed(Term::universe(0)),
                Bind::unnamed(Term::universe(0)),
                Bind::unnamed(Term::universe(0)),
            ],
            Term::Var(Var::bound(0), vec![
                Elim::app(Term::bound_var(1)),
                Elim::app(Term::bound_var(2)),
            ]),
        );

        println!("{}", long_term);

        let mut tcs = MockSubstCtx { uid: Cell::new(0) };

        let (tele, t) = unbind_closed(long_term.clone(), &mut tcs, 3);
        println!("{tele}, {t}");

        // check that names were distributed correctly
        assert_eq!(tele.0.len(), 3);
        assert_eq!(tele.0[0].name, 1);
        assert_eq!(tele.0[1].name, 2);
        assert_eq!(tele.0[2].name, 3);

        // check that the term was unbound correctly
        assert_eq!(t, Term::Var(Var::free(3), vec![
            Elim::app(Term::Var(Var::free(2), vec![])),
            Elim::app(Term::Var(Var::free(1), vec![])),
        ]));

        tcs.reset();
        let (tele_2, t_2) = unbind_closed(long_term.clone(), &mut tcs, 33);
        assert_eq!(tele, tele_2);
        assert_eq!(t, t_2);

        tcs.reset();

        let (tele_3, t_3) = unbind_closed(long_term.clone(), &mut tcs, 2);
        assert_eq!(tele_3.0.len(), 2);
        assert_eq!(tele_3.0[0].name, 1);
        assert_eq!(tele_3.0[1].name, 2);

        println!("{t_3}");
        assert_eq!(t_3, Term::lam(Bind::unnamed(Term::universe(0)).boxed(), Term::Var(Var::bound(0), vec![
            Elim::app(Term::Var(Var::free(2), vec![])),
            Elim::app(Term::Var(Var::free(1), vec![])),
        ])));

        tcs.reset();
        let (tele_3, t_3) = unbind_closed(long_term.clone(), &mut tcs, 1);
        assert_eq!(tele_3.0.len(), 1);
        assert_eq!(tele_3.0[0].name, 1);

        println!("{t_3}");
        assert_eq!(t_3, Term::lams(
            vec![
                Bind::unnamed(Term::universe(0)),
                Bind::unnamed(Term::universe(0)),
            ],
            Term::Var(Var::bound(0), vec![
                Elim::app(Term::Var(Var::bound(1), vec![])),
                Elim::app(Term::Var(Var::free(1), vec![])),
            ]),
        ));
    }
}