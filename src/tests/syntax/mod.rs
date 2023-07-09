mod subst;

use crate::syntax::core::PrimSubst::IdS;
use crate::syntax::core::{Boxed, DeBruijn, PrimSubst, Subst};
use crate::syntax::DBI;
use quickcheck::{Arbitrary, Gen, TestResult, Testable};
use std::fmt::Display;
use std::rc::Rc;

#[derive(Eq, PartialEq, PartialOrd, Debug, Clone)]
pub enum Ty {
    A,
    B,
    C,
    // X denotes forbidden variables
    X,
    Arr(Box<(Ty, Ty)>),
}

#[derive(Eq, PartialEq, PartialOrd, Debug, Clone)]
pub enum Cx {
    Nil,
    Ext(Box<Cx>, Ty),
}

impl Cx {
    pub(crate) fn len(&self) -> usize {
        match self {
            Cx::Nil => 0,
            Cx::Ext(cx, _) => 1 + cx.len(),
        }
    }

    fn split(self, n: DBI) -> (Cx, Cx) {
        match (n, self) {
            (0, g) => (g, Cx::Nil),
            (n, Cx::Ext(cx, ty)) => {
                let (cx1, cx2) = cx.split(n - 1);
                (cx1, cx2.ext(ty))
            }
            (_, Cx::Nil) => {
                unreachable!()
            }
        }
    }

    pub fn ext(self, ty: Ty) -> Cx {
        Cx::Ext(Box::new(self), ty)
    }

    pub fn extend(self, cx: Self) -> Cx {
        match cx {
            Cx::Nil => self,
            Cx::Ext(delta, t) => self.extend(*delta).ext(t),
        }
    }

    pub fn from_list(it: impl DoubleEndedIterator<Item = Ty>) -> Self {
        it.into_iter()
            .rev()
            .fold(Cx::Nil, |cx, ty| Cx::Ext(Box::new(cx), ty))
    }

    pub fn vars(&self) -> Vec<(usize, Ty)> {
        fn go(i: usize, c: &Cx) -> Vec<(usize, Ty)> {
            match (i, c) {
                (_, Cx::Nil) => Vec::new(),
                (i, Cx::Ext(c, t)) => {
                    let mut xs = go(i + 1, c);
                    xs.insert(0, (i, t.clone()));
                    xs
                }
            }
        }
        go(0, self)
    }
}

#[derive(Eq, PartialEq, PartialOrd, Debug, Clone)]
pub enum Tm {
    Var(usize),
    Ann(Box<Tm>, Ty),
    Con(Ty, Vec<Tm>),
    Lam(Ty, Box<Tm>),
}

impl Tm {
    pub(crate) fn get_ty(&self) -> Ty {
        match self {
            Tm::Var(_) => {
                unreachable!()
            }
            Tm::Ann(_, t) => t.clone(),
            Tm::Con(t, _) => t.clone(),
            Tm::Lam(t, v) => Ty::Arr(Box::new((t.clone(), v.get_ty()))),
        }
    }
}

pub fn var(ty: Ty, idx: usize) -> Tm {
    use Tm::*;
    Ann(Var(idx).boxed(), ty)
}

type Sub = PrimSubst<Tm>;

impl DeBruijn for Tm {
    fn dbi_view(&self) -> Option<DBI> {
        use Tm::*;
        match self {
            Var(idx) => Some(*idx),
            _ => None,
        }
    }

    fn from_dbi(dbi: DBI) -> Self {
        Tm::Var(dbi)
    }
}

impl Subst<Tm, Tm> for Tm {
    fn subst(self, subst: Rc<PrimSubst<Tm>>) -> Self {
        use Tm::*;
        match self {
            Var(idx) => subst.lookup(idx),
            Ann(tm, ty) => Ann(tm.subst(subst.clone()).boxed(), ty),
            Con(ty, tms) => Con(
                ty,
                tms.iter()
                    .map(|tm| tm.clone().subst(subst.clone()))
                    .collect(),
            ),
            Lam(ty, tm) => Lam(ty, tm.subst(subst.clone().lift_by(1)).boxed()),
        }
    }
}

pub fn gen_base_ty(g: &mut Gen) -> Ty {
    use Ty::*;
    g.choose(&[A, B, C]).unwrap().clone()
}

impl Arbitrary for Ty {
    fn arbitrary(g: &mut Gen) -> Self {
        fn arb(g: &mut Gen, n: usize) -> Ty {
            let mut xs = Vec::<Ty>::new();
            xs.push(gen_base_ty(g));
            if n > 0 {
                xs.push(Ty::Arr((gen_base_ty(g), arb(g, n / 2)).boxed()));
            }
            g.choose(&xs).unwrap().clone()
        }
        arb(g, g.size())
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        use Ty::*;
        match self {
            Arr(inn) => {
                let (s, t) = &**inn;
                let mut xs = vec![s.clone(), t.clone()];
                xs.extend(s.shrink().map(|x| Arr((x, t.clone()).boxed())));
                xs.extend(t.shrink().map(|x| Arr((s.clone(), x).boxed())));
                Box::new(xs.into_iter())
            }
            _ => return Box::new(std::iter::empty()),
        }
    }
}

impl Arbitrary for Cx {
    fn arbitrary(g: &mut Gen) -> Self {
        let n = usize::arbitrary(g) % g.size();
        let mut ng = Gen::new(g.size());
        Self::from_list((0..n).map(|_| g.choose(&[gen_base_ty(&mut ng), Ty::X]).unwrap().clone()))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        match self {
            Cx::Nil => Box::new(std::iter::empty()),
            Cx::Ext(g, t) => {
                let mut xs = vec![Cx::Nil, (&**g).clone()];
                xs.extend(g.shrink().map(|x| Cx::Ext(x, t.clone())));
                xs.extend(t.shrink().map(|x| Cx::Ext(g.clone(), x)));
                Box::new(xs.into_iter())
            }
        }
    }
}

pub fn gen_tm(g: &mut Gen, c: Cx, t: Ty) -> Tm {
    use Ty::*;
    fn var_or_lam(g: &mut Gen, c: Cx) -> Tm {
        use Ty::*;
        let mut vec = c
            .vars()
            .into_iter()
            .filter(|(_x, t)| t != &X)
            .collect::<Vec<_>>();
        let n = usize::arbitrary(g) % (vec.len() + 1);
        match n {
            0 => {
                let s = gen_base_ty(g);
                Tm::Lam(
                    s.clone(),
                    var_or_lam(g, Cx::Ext(c.clone().boxed(), s)).boxed(),
                )
            }
            x => {
                let i = x - 1;
                let (x, t) = vec.remove(i);
                var(t, x)
            }
        }
    }

    let mut xs = Vec::<Tm>::new();
    xs.extend(c.vars().iter().filter_map(|(x, s)| {
        use Ty::*;
        if s != &X && s == &t {
            Some(var(t.clone(), *x))
        } else {
            None
        }
    }));
    let n = usize::arbitrary(g) % 3 + 1;
    xs.extend((0..n).map(|_| var_or_lam(g, c.clone())));

    let matches = matches!(t, Arr(_));
    let n = usize::arbitrary(g) % (xs.len() + if matches { 1 } else { 0 });
    if matches {
        if n == xs.len() {
            if let Arr(inn) = t {
                let (s, t) = &*inn;
                Tm::Lam(
                    s.clone(),
                    gen_tm(g, c.clone().ext(s.clone()), t.clone()).boxed(),
                )
            } else {
                unreachable!()
            }
        } else {
            xs.remove(n)
        }
    } else {
        xs.remove(n)
    }
}

impl Arbitrary for Tm {
    fn arbitrary(g: &mut Gen) -> Self {
        let c = Cx::arbitrary(g);
        let t = Ty::arbitrary(g);
        gen_tm(g, c, t)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        match self {
            Tm::Con(t, vs) => {
                let t = t.clone();
                Box::new(vs.shrink().map(move |vs| Tm::Con(t.clone(), vs))).into_iter()
            }
            v => Box::new(vec![Tm::Con(v.get_ty(), Vec::new())].into_iter()),
        }
    }
}

pub fn gen_sub(g: &mut Gen, delta: Cx) -> (Cx, Sub) {
    let mut xs = Vec::new();
    let dc = delta.clone();
    xs.push((Box::new(move || (dc.clone(), IdS))) as Box<dyn FnOnce() -> (_, _)>);
    /*
    if delta == Cx::Nil {
        let c = Cx::arbitrary(g);
        xs.push(box move || (c.clone(), Sub::Empty))
    }
     */
    let gen_cons = move |delta, t, mut g| {
        let (gamma, rho) = gen_sub(&mut g, delta);
        match t {
            Ty::X => (gamma, Sub::Succ(Rc::new(rho))),
            _ => {
                let v = gen_tm(&mut g, gamma.clone(), t);
                (gamma, Sub::Cons(v, Rc::new(rho)))
            }
        }
    };
    if let Cx::Ext(cx, t) = delta.clone() {
        let gen = Gen::new(g.size());
        xs.push((Box::new(move || gen_cons(*cx, t, gen))) as Box<dyn FnOnce() -> (_, _)>)
    }
    let gen_wk = |mut g: Gen, delta| {
        let n = usize::arbitrary(&mut g) % 3;
        let psi = Cx::from_list((0..n).map(|_| gen_base_ty(&mut g)));
        let (gamma, rho) = gen_sub(&mut g, delta);
        (gamma.extend(psi), Sub::Weak(n, rho.into()))
    };
    let gen = Gen::new(g.size());
    let dc = delta.clone();
    xs.push((Box::new(move || gen_wk(gen, dc))) as Box<dyn FnOnce() -> (_, _)>);

    let gen_lift = |mut g: Gen, delta: Cx| {
        // n <- choose (1, min 3 $ cxLen delta)
        // let (delta1, delta2) = splitCx n delta
        //     (gamma, rho) <- genSub delta1
        // pure (gamma <> delta2, Lift n rho)
        let n = usize::arbitrary(&mut g) % (3.min(delta.len())) + 1;
        let (delta1, delta2) = delta.split(n);
        let (gamma, rho) = gen_sub(&mut g, delta1);
        (gamma.extend(delta2), Sub::Lift(n, rho.into()))
    };
    if delta.len() > 0 {
        let gen = Gen::new(g.size());
        xs.push((Box::new(move || gen_lift(gen, delta.clone()))) as Box<dyn FnOnce() -> (_, _)>);
    }
    let n = usize::arbitrary(g) % xs.len();
    xs.remove(n)()
}

fn eq_sub(g: &mut Gen, rho: Rc<Sub>, sgm: Rc<Sub>, delta: Cx) -> bool {
    // let mut g = Gen::new();
    let ty = gen_base_ty(g);
    ty.shrink().all(|t| {
        let term = gen_tm(g, delta.clone(), t);
        term.shrink()
            .all(|v| v.clone().subst(rho.clone()) == v.subst(sgm.clone()))
    })
}

#[derive(Debug, Clone)]
struct SubCx(Cx, Sub);

impl Arbitrary for SubCx {
    fn arbitrary(g: &mut Gen) -> Self {
        let ctx = Cx::arbitrary(g);
        let arb = gen_sub(g, ctx);
        SubCx(arb.0, arb.1)
    }
}

struct Eq<T>(T, T);

impl<T: PartialEq + Display + 'static> Testable for Eq<T> {
    fn result(&self, _: &mut Gen) -> TestResult {
        if self.0 == self.1 {
            TestResult::passed()
        } else {
            TestResult::error(format!("{} != {}", self.0, self.1))
        }
    }
}
