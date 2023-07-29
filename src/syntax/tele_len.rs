use crate::check::unification::{Equation, Problem};
use crate::syntax::core::{Lambda, Term};
use std::any::type_name_of_val;

pub trait TeleLen {
    fn tele_len(&self) -> usize;

    fn lam_len(&self) -> usize {
        unimplemented!("lam_len not implemented for {}", type_name_of_val(self))
    }

    fn ctx_len(&self) -> usize {
        unimplemented!("ctx_len not implemented for {}", type_name_of_val(self))
    }
}

impl TeleLen for Term {
    fn tele_len(&self) -> usize {
        match self {
            Term::Pi(_, b) => 1 + b.as_inner().tele_len(),
            _ => 0,
        }
    }

    fn lam_len(&self) -> usize {
        match self {
            Term::Lam(Lambda(_, body)) => 1 + body.as_inner().lam_len(),
            _ => 0,
        }
    }

    fn ctx_len(&self) -> usize {
        match self {
            Term::Pi(_, b) => 1 + b.as_inner().ctx_len(),
            Term::Lam(Lambda(_, body)) => 1 + body.as_inner().ctx_len(),
            _ => 0,
        }
    }
}

impl TeleLen for Problem {
    fn tele_len(&self) -> usize {
        match self {
            Problem::All(_, p) => 1 + p.tele_len(),
            Problem::Unify(_) => 0,
        }
    }

    fn ctx_len(&self) -> usize {
        match self {
            Problem::All(_, p) => 1 + p.ctx_len(),
            Problem::Unify(Equation { tm1, ty1, tm2, ty2 }) => ty1.ctx_len(),
        }
    }
}
