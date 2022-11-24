use crate::syntax::core::Term;
use crate::syntax::{ConHead, GI};
use std::fmt::{Display, Formatter};

pub type Nat = usize;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Literal {
    Nat(Nat),
    Str(String),
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Nat(n) => write!(f, "{}", n),
            Literal::Str(s) => write!(f, "{}", s),
        }
    }
}

pub fn nat_to_term(n: Nat, nat_z: ConHead, nat_s: ConHead) -> Term {
    let mut t = Term::cons(nat_z, vec![]);
    for _ in 0..n {
        // t = Term::Redex(nat_s.clone(), vec![]).apply(vec![t]);
        t = Term::cons(nat_s.clone(), vec![]).apply(vec![t]);
    }
    t
}
