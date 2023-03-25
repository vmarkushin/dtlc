use crate::check::TypeCheckState;
use crate::syntax::core::term::{Bind, Case, Id, Lambda};
use crate::syntax::core::{Closure, Elim, Func, Pat, Tele, Term, TermInfo, ValData, Var};
use crate::syntax::surf::Nat;
use crate::syntax::Plicitness::*;
use crate::syntax::{ConHead, LangItem, Plicitness};
use core::fmt;
use itertools::Itertools;
use std::fmt::{Display, Error, Formatter, Write};
use std::marker::PhantomData;

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
            Elim::App(app) => write!(f, "{}", app),
            Elim::Proj(field) => write!(f, ".{}", field),
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use Term::*;
        match self {
            Meta(mi, a) => {
                f.write_str("?")?;
                display_application(f, mi, a)
            }
            Var(v, a) => display_application(f, &format!("{}", v), a),
            Universe(l) => write!(f, "{}", l),
            Pi(Bind { licit, ty, .. }, clos) => match licit {
                Explicit => write!(f, "({} -> {})", ty, clos),
                Implicit => write!(f, "({{{}}} -> {})", ty, clos),
            },
            Lam(lam) => lam.fmt(f),
            Cons(name, a) => display_application(f, name, a),
            Data(info) => info.fmt(f),
            Id(id) => id.fmt(f),
            Refl(t) => write!(f, "refl {}", t),
            Redex(Func::Index(_), ident, args) => display_application(f, &ident.text, args),
            Redex(Func::Lam(lam), _ident, args) => {
                write!(f, "({})", lam)?;
                display_application(f, &"".to_owned(), args)
            }
            Match(term, cases) => {
                writeln!(f, "match {} {{", term)?;
                for Case { pattern, body } in cases {
                    writeln!(f, " | {} => {}", pattern, body)?;
                }
                write!(f, "}}")?;
                Ok(())
            }
            Ap(tele, ps, t) => {
                write!(f, "ap (\\{}. {}) {}", tele, t, ps.iter().join(", "))
            }
        }
    }
}

impl Display for Id {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Id (\\{}. {}) ({}) {} {}",
            self.ty,
            self.tele,
            self.paths.iter().join(", "),
            self.a1,
            self.a2
        )
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
            Var::Twin(i, b) => {
                if *b {
                    write!(f, "@r{}", i)
                } else {
                    write!(f, "@l{}", i)
                }
            }
            Var::Meta(m) => {
                write!(f, "?{}", m)
            }
        }
    }
}

impl Display for ValData {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        f.write_str("data")?;
        display_application(f, &self.def, &self.args)
    }
}

impl Display for Closure {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use Closure::*;
        let Plain(body) = self;
        Display::fmt(body, f)
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

pub fn display_application(
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

/*pub fn pretty_application(
    f: &mut Formatter,
    s: &TypeCheckState,
    fun: &impl Display,
    a: &[impl Display],
) -> Result<(), Error> {
    if a.is_empty() {
        // let pretty = Pretty { s, inner: 1u32 };
        // Display::fmt(&pretty, f)
        write!(f, "{}", fun)
    } else {
        write!(f, "({}", fun)?;
        for x in a {
            write!(f, " {}", pretty(x, s))?;
        }
        f.write_str(")")
    }
}
*/

pub struct StatefulFormatter<'a, S> {
    f: &'a mut Formatter<'a>,
    s: S,
}

impl<'a, S> From<(S, &'a mut Formatter<'a>)> for StatefulFormatter<'a, S> {
    fn from((s, f): (S, &'a mut Formatter<'a>)) -> Self {
        StatefulFormatter { f, s }
    }
}

impl<'a, S> Write for StatefulFormatter<'a, S> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.f.write_str(s)
    }
}

pub trait Delimiter {
    fn get() -> &'static str;
}

pub struct CommaDelimiter;

impl Delimiter for CommaDelimiter {
    fn get() -> &'static str {
        ","
    }
}

pub struct NewlineDelimiter;

impl Delimiter for NewlineDelimiter {
    fn get() -> &'static str {
        "\n\t"
    }
}

pub struct Pretty<'a, T, S = TypeCheckState, D = CommaDelimiter> {
    pub inner: &'a T,
    pub s: &'a S,
    pub d: PhantomData<D>,
}

pub fn pretty<'a, T, D>(val: &'a T, s: &'a TypeCheckState) -> Pretty<'a, T, TypeCheckState, D> {
    Pretty {
        inner: val,
        s,
        d: PhantomData,
    }
}

impl Display for Pretty<'_, Term> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.s;
        match &self.inner {
            Term::Universe(uni) => uni.fmt(f),
            Term::Data(data) => {
                let data_name = &s.def(data.def).def_name().text;
                let args = data.args.iter().map(|x| pretty(x, s)).collect::<Vec<_>>();
                display_application(f, &data_name, &args)
            }
            Term::Pi(
                Bind {
                    licit, ty, ident, ..
                },
                clos,
            ) => {
                let ty = pretty(&**ty, s);
                let clos = pretty(clos, s);
                match licit {
                    Explicit => write!(f, "(({} : {}) -> {})", ident, ty, clos),
                    Implicit => write!(f, "({{{} : {}}} -> {})", ident, ty, clos),
                }
            }
            Term::Lam(Lambda(
                Bind {
                    licit, ty, ident, ..
                },
                clos,
            )) => {
                let ty = pretty(&**ty, s);
                let clos = pretty(clos, s);
                match licit {
                    Explicit => write!(f, "(lam {} : {} => {})", ident, ty, clos),
                    Implicit => write!(f, "(lam {} : {{{}}} => {})", ident, ty, clos),
                }
            }
            Term::Cons(cons, args) => {
                if let Some(nat) = maybe_pretty_nat(cons, args, s) {
                    nat.fmt(f)
                } else {
                    let args = args.iter().map(|x| pretty(x, s)).collect::<Vec<_>>();
                    display_application(f, &cons.name, &args)
                }
            }
            Term::Meta(mi, args) | Term::Var(Var::Meta(mi), args) => {
                let args = args.iter().map(|x| pretty(x, s)).collect::<Vec<_>>();
                display_application(f, &format!("?{}", mi), &args)
            }
            Term::Var(v, args) => {
                let args = args.iter().map(|x| pretty(x, s)).collect::<Vec<_>>();
                let var = match v {
                    Var::Bound(dbi) => {
                        let x = s.lookup(*dbi);
                        format!("{}", x.ident.text)
                    }
                    Var::Free(uid) => {
                        if *uid < 26 {
                            let ci = (97 + *uid) as u8 as char;
                            format!("{}", ci)
                        } else {
                            format!("#{}", uid)
                        }
                    }
                    v @ Var::Twin(..) => {
                        let x = s.gamma2.lookup(*v);
                        format!("{}", x.ident.text)
                    }
                    Var::Meta(_) => {
                        unreachable!()
                    }
                };
                display_application(f, &var, &args)
            }
            Term::Id(id) => pretty(id, s).fmt(f),
            Term::Refl(t) => write!(f, "(refl {})", pretty(t.as_ref(), s)),
            Term::Redex(_f, ident, es) => {
                write!(f, "({} {})", ident, pretty(es, s))
            }
            Term::Match(t, cs) => {
                write!(f, "match {} {{{}}}", pretty(&**t, s), pretty(cs, s))
            }
            Term::Ap(tele, ps, t) => {
                write!(
                    f,
                    "ap {} {} {}",
                    pretty(tele, s),
                    pretty(ps, s),
                    pretty(&**t, s)
                )
            }
        }
    }
}

impl Display for Pretty<'_, Func> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.s;
        match &self.inner {
            Func::Index(gi) => {
                write!(f, "{}", s.def(*gi).def_name())
            }
            Func::Lam(lam) => {
                write!(f, "{}", pretty(lam, s))
            }
        }
    }
}

impl Display for Pretty<'_, Lambda> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.s;
        write!(
            f,
            "lam {} => {}",
            pretty(&self.inner.0.clone().map_term(|x| *x), s),
            pretty(&self.inner.1, s)
        )
    }
}

impl Display for Pretty<'_, Case> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.s;
        write!(
            f,
            "| {} => {}",
            pretty(&self.inner.pattern, s),
            pretty(&self.inner.body, s)
        )
    }
}

impl Display for Pretty<'_, Pat> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.s;
        write!(f, "{}", pretty(&self.inner.clone().into_term(), s),)
    }
}

impl Display for Pretty<'_, Elim> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.s;
        match &self.inner {
            Elim::App(t) => {
                write!(f, "{}", pretty(&**t, s))
            }
            Elim::Proj(_) => {
                unimplemented!()
            }
        }
    }
}

fn maybe_pretty_nat(con: &ConHead, mut args: &[Term], s: &TypeCheckState) -> Option<Nat> {
    if let Some(nat_z) = s.lang_item(LangItem::NatZ) {
        let nat_s = s.lang_item(LangItem::NatS).unwrap();
        if con.cons_gi != nat_z && con.cons_gi != nat_s {
            return None;
        }
        let mut nat = Nat::default();
        while !args.is_empty() {
            let (_, sargs) = args.first().unwrap().as_cons().unwrap();
            args = sargs;
            nat += 1;
        }
        return Some(nat);
    }
    None
}

/*
default impl<'a, T: Display> Display for Pretty<'a, T, TypeCheckState> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        todo!()
        // self.inner.fmt(f)
    }
}*/

impl Display for Pretty<'_, String> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/*
impl<T: Display> Display for Pretty<'_, [T]> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        todo!()
        // self.inner.fmt(f)
    }
}
*/

impl Display for Pretty<'_, Closure> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let Closure::Plain(body) = self.inner;
        let body = &**body;
        pretty(body, self.s).fmt(f)
    }
}

/*impl<T: Display> Display for Pretty<'_, Vec<T>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.s;
        if self.inner.is_empty() {
            return Ok(());
        }
        pretty(&self.inner[0], s).fmt(f)?;
        if self.inner.len() == 1 {
            return Ok(());
        }
        for x in &self.inner[1..] {
            write!(f, ", {}", pretty(x, s))?;
        }
        Ok(())
    }
}
*/

impl Display for Pretty<'_, Bind> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.s;
        if self.inner.licit == Plicitness::Implicit {
            write!(f, "{{{}:{}}}", self.inner.ident, pretty(&self.inner.ty, s))
        } else {
            write!(f, "{}:{}", self.inner.ident, pretty(&self.inner.ty, s))
        }
    }
}

impl Display for Pretty<'_, Tele> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.s;
        if self.inner.is_empty() {
            return Ok(());
        }
        pretty(&self.inner.0[0], s).fmt(f)?;
        if self.inner.len() == 1 {
            return Ok(());
        }
        for x in &self.inner.0[1..] {
            write!(f, ", {}", pretty(x, s))?;
        }
        Ok(())
    }
}

macro_rules! impl_pretty_vec {
    ($T:ty, $D:ty) => {
        impl Display for Pretty<'_, Vec<$T>, TypeCheckState, $D> {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                let s = self.s;
                if self.inner.is_empty() {
                    return Ok(());
                }
                pretty(&self.inner[0], s).fmt(f)?;
                if self.inner.len() == 1 {
                    return Ok(());
                }
                for x in &self.inner[1..] {
                    write!(f, ", {}", pretty(x, s))?;
                }
                Ok(())
            }
        }
    };
    ($T:ty) => {
        impl_pretty_vec!($T, CommaDelimiter);
    };
}
impl_pretty_vec!(Term);
impl_pretty_vec!(Elim);
impl_pretty_vec!(Case, NewlineDelimiter);

impl Display for Pretty<'_, Id> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.s;
        // self.inner.ty is skipped formatted
        write!(
            f,
            "{} = {}",
            pretty(&*self.inner.a1, s),
            pretty(&*self.inner.a2, s)
        )?;
        if !self.inner.tele.is_empty() {
            write!(
                f,
                " [{} : {}]",
                pretty(&self.inner.paths, s),
                pretty(&self.inner.tele, s)
            )?;
        }
        Ok(())
    }
}

#[macro_export]
macro_rules! pretty_write {
    ($f:ident, $s:ident, $($x:expr),+) => {
        write!($f, "{}", $(pretty($x, $s)),+)
    };
}
