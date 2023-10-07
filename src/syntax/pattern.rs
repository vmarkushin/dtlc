use crate::check::TypeCheckState;
use crate::syntax::core::{display_application, Bind, Name, Term, Type};
use crate::syntax::{ConHead, Ident};
use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pat<Ix, Term> {
    /// Variable pattern. Potentially can be constructor.
    /// Note: it has a name suggestion in Agda.
    /// https://hackage.haskell.org/package/Agda-2.6.0.1/docs/Agda-Syntax-Internal.html#t:Pattern
    Var(Ix),
    Wildcard,
    /// Impossible pattern.
    Absurd,
    /// Dual to [`crate::syntax::core::Term::Cons`],
    /// but can be forced (the first member is "is_forced").
    Cons(bool, ConHead, Vec<Self>),
    /// Forced term as an expression.
    Forced(Term),
}

impl<Ix> Pat<Ix, Term> {
    pub(crate) fn binders(&self) -> Vec<Bind> {
        match self {
            Pat::Var(_) => vec![Bind::explicit(0, Term::meta(13333337), Ident::new("_p"))],
            Pat::Wildcard => vec![],
            Pat::Absurd => vec![],
            Pat::Cons(false, _, args) => args.iter().flat_map(|arg| arg.binders()).collect(),
            Pat::Cons(true, _, _) => vec![],
            Pat::Forced(..) => vec![],
        }
    }
}

impl<Ix: Clone, Term> Pat<Ix, Term> {
    pub(crate) fn unbind(&self, tcs: &mut TypeCheckState) -> Vec<Name> {
        match self {
            Pat::Var(name) => vec![Name::Free(tcs.next_uid())],
            Pat::Wildcard => vec![],
            Pat::Absurd => vec![],
            Pat::Cons(false, _, args) => args.iter().flat_map(|arg| arg.unbind(tcs)).collect(),
            Pat::Cons(true, _, _) => vec![],
            Pat::Forced(..) => vec![],
        }
    }
}

impl<Ix: Copy, Term> Pat<Ix, Term> {
    pub(crate) fn as_var(&self) -> Ix {
        match self {
            Pat::Var(v) => *v,
            _ => panic!("Not a variable pattern"),
        }
    }
}

impl<Ix, Term> Pat<Ix, Term> {
    pub(crate) fn is_abusrd(&self) -> bool {
        matches!(self, Pat::Absurd)
    }

    pub(crate) fn is_cons(&self) -> bool {
        matches!(self, Pat::Cons(..))
    }

    pub fn cons_surf(forced: bool, ident: Ident, args: Vec<Self>) -> Self {
        Self::Cons(forced, ConHead::new(ident, 0), args)
    }

    pub fn cons(con_head: ConHead, params: Vec<Self>) -> Self {
        Pat::Cons(false, con_head, params)
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(_))
    }

    /// Pattern variables `PV(qs)`.By removing the forcing brackets, patterns p embed into terms
    /// ps, and copatterns q into elimination qs, except for the absurd pattern.
    /// [norell_phd](Ulf Norell's PhD, page. 35)
    pub fn vars(&self) -> Vec<Ix>
    where
        Ix: Clone,
    {
        match self {
            Pat::Var(ix) => vec![ix.clone()],
            Pat::Wildcard => vec![],
            Pat::Absurd => vec![],
            Pat::Cons(_, _, args) => args.iter().flat_map(|arg| arg.vars()).collect(),
            Pat::Forced(..) => vec![],
        }
    }
}

impl<Ix: Display, Term: Display> Display for Pat<Ix, Term> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Pat::Var(name) => {
                write!(f, "{}", name)
            }
            Pat::Wildcard => {
                write!(f, "_")
            }
            Pat::Absurd => {
                write!(f, "!")
            }
            Pat::Cons(forced, head, args) => {
                if *forced {
                    write!(f, ".")?;
                }
                display_application(f, head, args)
            }
            Pat::Forced(e) => {
                write!(f, ".{}", e)
            }
        }
    }
}
