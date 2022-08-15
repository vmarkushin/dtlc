use crate::syntax::core::term::{Bind, Case, Lambda};
use crate::syntax::core::{Closure, Elim, Func, Term, TermInfo, Val, ValData, Var};
use crate::syntax::{ConHead, Plicitness};
use std::fmt::{Display, Error, Formatter, Write};

#[derive(Copy, Clone, Debug, Default)]
pub struct Indentation {
    pub tc_depth: usize,
    /// How many indentations should we add when enter each sub-inference-rule?
    pub indentation_size: usize,
}

impl Display for Indentation {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        for _ in 0..self.tc_depth * self.indentation_size {
            f.write_char(' ')?;
        }
        Ok(())
    }
}

impl Display for Elim {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        match self {
            Elim::App(app) => app.fmt(f),
            Elim::Proj(field) => write!(f, ".{}", field),
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use Term::*;
        match self {
            Whnf(v) => v.fmt(f),
            Redex(Func::Index(_), ident, args) => pretty_application(f, &ident.text, args),
            Redex(Func::Lam(lam), _ident, args) => {
                write!(f, "({})", lam)?;
                pretty_application(f, &"".to_owned(), args)
            }
            Match(term, cases) => {
                writeln!(f, "match {} {{", term)?;
                for Case { pattern, body } in cases {
                    writeln!(f, " | {} => {}", pattern, body)?;
                }
                write!(f, "}}")?;
                Ok(())
            }
        }
    }
}

impl Display for Lambda {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Plicitness::*;
        match self {
            Lambda(Bind { licit, ty, .. }, clos) => match licit {
                Explicit => write!(f, "(\\{}. {})", ty, clos),
                Implicit => write!(f, "({{\\{}}}. {})", ty, clos),
            },
        }
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Var::Bound(i) => {
                write!(f, "@{}", i)
            }
            Var::Free(i) => {
                if *i < 26 {
                    let ci = (97 + *i) as u8 as char;
                    write!(f, "{}", ci)
                } else {
                    write!(f, "#{}", i)
                }
            }
        }
    }
}

impl Display for Val {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use Plicitness::*;
        use Val::*;
        match self {
            Meta(mi, a) => {
                f.write_str("?")?;
                pretty_application(f, mi, a)
            }
            Var(v, a) => pretty_application(f, &format!("{}", v), a),
            Universe(l) => write!(f, "{}", l),
            Pi(Bind { licit, ty, .. }, clos) => match licit {
                Explicit => write!(f, "({} -> {})", ty, clos),
                Implicit => write!(f, "({{{}}} -> {})", ty, clos),
            },
            Lam(lam) => lam.fmt(f),
            Cons(name, a) => pretty_application(f, name, a),
            Data(info) => info.fmt(f),
        }
    }
}

impl Display for ValData {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        f.write_str("data")?;
        pretty_application(f, &self.def, &self.args)
    }
}

impl Display for Closure {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use Closure::*;
        let Plain(body) = self;
        body.fmt(f)
    }
}

impl Display for ConHead {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        self.name.text.fmt(f)
    }
}

impl Display for TermInfo {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        write!(f, "{}", self.ast)
    }
}

pub fn pretty_list(
    f: &mut Formatter,
    a: &[impl Display],
    delim: impl Display,
) -> Result<(), Error> {
    if a.is_empty() {
        Ok(())
    } else {
        write!(f, "{}", a[0])?;
        for x in &a[1..] {
            write!(f, "{}{}", x, delim)?;
        }
        Ok(())
    }
}

pub fn pretty_application(
    f: &mut Formatter,
    fun: &impl Display,
    a: &[impl Display],
) -> Result<(), Error> {
    if a.is_empty() {
        fun.fmt(f)
    } else {
        write!(f, "({}", fun)?;
        for x in a {
            write!(f, " {}", x)?;
        }
        f.write_str(")")
    }
}
