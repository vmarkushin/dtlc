use crate::syntax::core::Boxed;
use crate::syntax::surf::*;
use crate::syntax::surf::{Decl, Expr, Prog};
use crate::syntax::token::Token;
use crate::syntax::Plicitness::{Explicit, Implicit};
use crate::syntax::{Ident, Loc};
use crate::syntax::{Plicitness, Universe};
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::prelude::end;
use chumsky::prelude::*;
use chumsky::Parser as _;
use chumsky::Stream;
use codespan_reporting::files::SimpleFile;
use itertools::Itertools;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Formatter;
use std::fmt::{Debug, Display};
use std::fs;
use std::path::PathBuf;
use std::str::FromStr;
use vec1::Vec1;

pub type ParseError<'a> = Simple<Token<'a>, Loc>;
const UNIT: &() = &();

macro_rules! Parser {
    ($O:path) => { impl chumsky::Parser<Token<'static>, $O, Error = ParseError<'static>> + Clone };
    ($O:path: $($bounds:tt)*) => { impl chumsky::Parser<Token<'static>, $O, Error = ParseError<'static>> + $($bounds)* };
    ($I:path, $O:path) => { impl chumsky::Parser<$I, $O, Error = Simple<$I, Loc>> };
}

type BoxedParser<I, O, E> = Box<dyn chumsky::Parser<I, O, Error = E>>;

#[inline]
fn box_parser<I: Clone, O, E>(
    p: impl chumsky::Parser<I, O, Error = E> + 'static,
) -> BoxedParser<I, O, E> {
    Box::new(p)
}

fn err_to_static<'a>(e: ParseError<'a>) -> ParseError<'static> {
    e.map(|x| match x {
        Token::__Unused(_) => Token::__Unused(UNIT),
        Token::Universe(x) => Token::Universe(x),
        Token::Pi => Token::Pi,
        Token::Ident(x) => Token::Ident(x),
        Token::Data => Token::Data,
        Token::Codata => Token::Codata,
        Token::Match => Token::Match,
        Token::At => Token::At,
        Token::Hash => Token::Hash,
        Token::Colon => Token::Colon,
        Token::Comma => Token::Comma,
        Token::Dot => Token::Dot,
        Token::DArrow => Token::DArrow,
        Token::Lam => Token::Lam,
        Token::Fn => Token::Fn,
        Token::Let => Token::Let,
        Token::Pipe => Token::Pipe,
        Token::RArrow => Token::RArrow,
        Token::Underscore => Token::Underscore,
        Token::Bang => Token::Bang,
        Token::Question => Token::Question,
        Token::MetaIdent(x) => Token::MetaIdent(x),
        Token::Nat(x) => Token::Nat(x),
        Token::Str(x) => Token::Str(x),
        Token::LBrace => Token::LBrace,
        Token::RBrace => Token::RBrace,
        Token::LBracket => Token::LBracket,
        Token::RBracket => Token::RBracket,
        Token::LParen => Token::LParen,
        Token::RParen => Token::RParen,
        Token::Assignment => Token::Assignment,
        Token::Whitespace => Token::Whitespace,
        Token::Comment => Token::Comment,
    })
}

const FORBIDDEN: &str = "(){}, \n\t\r";

pub struct Parser {
    file: SimpleFile<String, String>,
    scope: Vec<Ident>,
    should_refine: bool,
}

impl Parser {
    fn parse_using<'inp, T: Display + Debug>(
        &self,
        parser: impl chumsky::Parser<Token<'static>, T, Error = ParseError<'static>>,
        input: &'inp str,
        lexer_ignore_idents: bool,
    ) -> Result<T, ParseError<'inp>> {
        let len = input.chars().count();
        let stream = Stream::<_, Loc, _>::from_iter(
            Loc::new(len, len + 1),
            Box::new(
                input
                    .chars()
                    .enumerate()
                    .map(|(i, c)| (c, Loc::new(i, i + 1))),
            ),
        );
        let additional_tokens = self
            .scope
            .iter()
            .map(|id| id.text.clone())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let (tokens, les) = lexer(additional_tokens, lexer_ignore_idents).parse_recovery(stream);
        let mut out = None;
        let mut err = None;
        let es = if let Some(tokens) = tokens {
            let toks = tokens.iter().map(|t| format!("{}", t.0)).join(" ");
            println!("tokens: {toks}",);
            debug!(target: "parser", "tokens: {tokens:#?}");
            let (e, es) = parser.then_ignore(end()).parse_recovery(Stream::from_iter(
                Loc::new(len, len + 1),
                tokens.into_iter(),
            ));
            out = e;
            err = es.first().cloned();
            es
        } else {
            vec![]
        };

        let errors = les
            .into_iter()
            .map(|e| e.map(|c| c.to_string()))
            .chain(es.into_iter().map(|e| e.map(|tok| tok.to_string())));
        errors.for_each(|e| {
            let report = Report::build(ReportKind::Error, (), e.span().start);
            let report = match e.reason() {
                chumsky::error::SimpleReason::Unclosed { span, delimiter } => report
                    .with_message(format!(
                        "Unclosed delimiter {}",
                        delimiter.fg(Color::Yellow)
                    ))
                    .with_label(
                        Label::new(span.clone())
                            .with_message(format!(
                                "Unclosed delimiter {}",
                                delimiter.fg(Color::Yellow)
                            ))
                            .with_color(Color::Yellow),
                    )
                    .with_label(
                        Label::new(e.span())
                            .with_message(format!(
                                "Must be closed before this {}",
                                e.found()
                                    .unwrap_or(&"end of file".to_string())
                                    .fg(Color::Red)
                            ))
                            .with_color(Color::Red),
                    ),
                chumsky::error::SimpleReason::Unexpected => {
                    let unexpected = if e.found().is_some() {
                        "Unexpected token in input"
                    } else {
                        "Unexpected end of input"
                    };
                    report
                        .with_message(if e.expected().len() != 0 {
                            format!(
                                "{unexpected}, expected {}",
                                e.expected()
                                    .map(|expected| match expected {
                                        Some(expected) => expected.to_string(),
                                        None => "end of input".to_string(),
                                    })
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            )
                        } else {
                            format!("{unexpected}")
                        })
                        .with_label(
                            Label::new(e.span())
                                .with_message(format!(
                                    "Unexpected token {}",
                                    e.found()
                                        .unwrap_or(&"end of file".to_string())
                                        .fg(Color::Red)
                                ))
                                .with_color(Color::Red),
                        )
                }
                chumsky::error::SimpleReason::Custom(msg) => report.with_message(msg).with_label(
                    Label::new(e.span())
                        .with_message(format!("{}", msg.fg(Color::Red)))
                        .with_color(Color::Red),
                ),
            };
            report.finish().print(Source::from(input)).unwrap();
        });

        if let Some(err) = err {
            Err(err)
        } else {
            let out = out.take().unwrap();
            println!("out: {}", out);
            Ok(out)
        }
    }

    pub fn parse_expr<'inp>(&mut self, input: &'inp str) -> Result<Expr, ParseError<'inp>> {
        let mut expr = self.parse_using(self.expr(), input, false)?;
        if self.should_refine {
            self.refine(&mut expr)?;
        }
        Ok(expr)
    }

    pub fn parse_decl<'inp>(&mut self, input: &'inp str) -> Result<Decl, ParseError<'inp>> {
        let mut decl = self.parse_using(self.decl(), input, false)?;
        if self.should_refine {
            let ident = decl.name();
            self.scope.push(ident.clone());
            self.refine_decl(&mut decl)?;
        }
        Ok(decl)
    }

    pub fn parse_prog<'inp>(&mut self, input: &'inp str) -> Result<Prog, ParseError<'inp>> {
        let mut prog = self.parse_using(self.prog(), input, false)?;
        if self.should_refine {
            for decl in &prog.0 {
                self.scope.push(decl.name().clone());
                match &decl {
                    Decl::Data(info) => {
                        for con in &info.cons {
                            self.scope.push(con.name.clone());
                        }
                    }
                    _ => {}
                }
            }
            for decl in prog.0.iter_mut() {
                self.refine_decl(decl)?;
            }
        }
        Ok(prog)
    }

    pub fn parse_prog_with_std<'inp>(
        &mut self,
        input: &'inp str,
        path: Option<PathBuf>,
    ) -> Result<Prog, ParseError<'inp>> {
        let path = path.unwrap_or(PathBuf::from_str("lib").unwrap());
        let content = fs::read_to_string(path.join("prelude.dtl")).unwrap();
        let mut std = self.parse_prog(&content).unwrap();
        let prog = self.parse_prog(input)?;
        std.0.extend(prog.0);
        Ok(std)
    }

    pub fn new() -> Self {
        let file = SimpleFile::new("".to_owned(), "".to_owned());
        Self {
            file,
            scope: vec![],
            should_refine: true,
        }
    }

    pub fn should_refine(self, should_refine: bool) -> Self {
        Self {
            should_refine,
            ..self
        }
    }

    pub fn scoped(self, scope: Vec<Ident>) -> Self {
        Self { scope, ..self }
    }

    pub fn expr(&self) -> Parser!(Expr) {
        recursive(|expr: Recursive<_, Expr, _>| {
            let prim_expr = prim_expr(&expr);
            let pattern = pattern(&prim_expr);
            let case = case(&expr, &pattern);
            let forall_params = forall_params(&expr);
            let param_parser = param(&expr, &prim_expr);
            let pi = (param_parser.clone().then_ignore(just(Token::RArrow)))
                .repeated()
                .at_least(1)
                .debug("parsed pi and waiting for <expr>")
                .then(expr.clone())
                .debug("pi");
            let lam = just(Token::Lam)
                .ignore_then(
                    forall_params.clone().or(forall_params
                        .delimited_by(just(Token::LParen), just(Token::RParen))
                        .repeated()
                        .at_least(1)
                        .map(|v| Vec1::try_from_vec(v.into_iter().flatten().collect()).unwrap())),
                )
                .then_ignore(just(Token::DArrow))
                .then(expr.clone())
                .debug("lam");
            let mat = just(Token::Match)
                .ignore_then(expr.clone().separated_by(just(Token::Comma)).at_least(1))
                .then_ignore(just(Token::LBrace))
                .then(case.clone().repeated())
                .then_ignore(just(Token::RBrace))
                .debug("mat");
            let app = prim_expr
                .clone()
                .then(prim_expr.clone().repeated())
                .debug("app");

            lam.map(|(ps, body)| Expr::Lam(ps, body.boxed()))
                .or(mat
                    .map(|(exprs, cases)| Expr::Match(Vec1::try_from_vec(exprs).unwrap(), cases)))
                .or(pi.map(|(ps, ret)| {
                    let ps = ps.into_iter().flatten().collect::<Vec<_>>();
                    Expr::Pi(Vec1::try_from_vec(ps).unwrap(), ret.boxed())
                }))
                .or(app.map(|(f, args)| {
                    if args.is_empty() {
                        f
                    } else {
                        Expr::App(Box::new(f), Vec1::try_from_vec(args).unwrap())
                    }
                }))
        })
        .debug("expr")
    }

    pub fn decl(&self) -> Parser!(Decl:) {
        let expr = self.expr();
        let prim_expr = prim_expr(&expr);
        let param_parser = param(&expr, &prim_expr);
        let params = params(&param_parser);
        let ident = ident_parser();

        let meta_attrs = meta_attr().repeated();
        let func = meta_attrs
            .clone()
            .then_ignore(just(Token::Fn))
            .then(ident.clone())
            .then(params.clone())
            .then(just(Token::Colon).ignore_then(expr.clone()).or_not())
            .then_ignore(just(Token::Assignment))
            .then(expr.clone());
        let data = meta_attrs
            .then_ignore(just(Token::Data))
            .then(ident.clone())
            .then(params.clone())
            .then(just(Token::Colon).ignore_then(universe_parser()).or_not())
            .then(cons(&params).repeated());
        func.map(|((((meta_attrs, name), params), ret_ty), body)| {
            Decl::from(Func {
                name,
                params: params.into(),
                ret_ty,
                body,
                meta_attrs,
            })
        })
        .or(
            data.map(|((((meta_attrs, name), ty_params), universe), cons)| {
                Decl::from(Data {
                    sig: NamedTele::new(name, ty_params.into()),
                    universe,
                    cons,
                    meta_attrs,
                })
            }),
        )
        .recover_with(skip_then_retry_until([
            Token::Fn,
            Token::Data,
            Token::Codata,
        ]))
    }

    pub fn prog(&self) -> impl chumsky::Parser<Token<'static>, Prog, Error = ParseError<'static>> {
        self.decl().repeated().map(Prog)
    }

    fn push(&mut self, name: Ident) {
        self.scope.push(name);
    }

    fn pop(&mut self) {
        self.scope.pop();
    }

    pub fn refine<'inp>(&mut self, expr: &'inp mut Expr) -> Result<(), ParseError<'static>> {
        debug!(target: "parser", "refining {}", expr);
        self.traverse_scoped(expr, |var, scope| {
            let mut parser = Parser::new().scoped(scope);
            debug!(target: "parser", "Parse scoped: {:?}", var);
            let mut e = parser
                .parse_using(parser.expr(), &var, true)
                .map_err(err_to_static)?;
            debug!(target: "parser", "Parse scoped out: {:?}", e);
            if let Expr::Var(v) = &e {
                if v == var {
                    return Ok(None);
                }
            }
            parser.refine(&mut e)?;
            return Ok(Some(e));
        })
    }

    pub fn refine_decl<'inp>(&mut self, decl: &'inp mut Decl) -> Result<(), ParseError<'static>> {
        match decl {
            Decl::Data(_) => {
                // TODO: refine data
                warn!("Data refinement not implemented");
            }
            Decl::Fn(f) => {
                let mut l = 0;
                for p in &mut f.params.0 {
                    if let Some(e) = &mut p.ty {
                        self.refine(e)?;
                    }
                    if let Some(ident) = &p.name {
                        self.push(ident.clone());
                        l += 1;
                    }
                }
                if let Some(e) = &mut f.ret_ty {
                    self.refine(e)?;
                }
                self.refine(&mut f.body)?;
                for _ in 0..l {
                    self.pop();
                }
            }
        }
        Ok(())
    }

    pub fn traverse_scoped<'a>(
        &mut self,
        expr: &'a mut Expr,
        f: impl for<'b> Fn(&'b Ident, Vec<Ident>) -> Result<Option<Expr>, ParseError<'static>> + Clone,
    ) -> Result<(), ParseError<'static>> {
        match expr {
            Expr::Var(ident) => {
                if let Some(e2) = f(ident, self.scope.clone()).map_err(err_to_static)? {
                    *expr = e2;
                }
            }
            Expr::Lam(ps, e) => {
                let mut l = 0;
                for p in ps {
                    if let Some(ty) = &mut p.ty {
                        self.traverse_scoped(ty, f.clone())?;
                    }
                    if let Some(name) = &p.name {
                        self.push(name.clone());
                        l += 1;
                    }
                }
                self.traverse_scoped(e, f.clone())?;
                for _ in 0..l {
                    self.pop();
                }
            }
            Expr::App(ff, args) => {
                self.traverse_scoped(ff, f.clone())?;
                for arg in args {
                    self.traverse_scoped(arg, f.clone())?;
                }
            }
            Expr::Universe(_, _) => {}
            Expr::Pi(ps, e) => {
                let mut l = 0;
                for p in ps {
                    if let Some(ty) = &mut p.ty {
                        self.traverse_scoped(ty, f.clone())?;
                    }
                    if let Some(name) = &p.name {
                        self.push(name.clone());
                        l += 1;
                    }
                }
                self.traverse_scoped(e, f.clone())?;
                for _ in 0..l {
                    self.pop();
                }
            }
            Expr::Tuple(_, es) => {
                for e in es {
                    self.traverse_scoped(e, f.clone())?;
                }
            }
            Expr::Hole(_) => {}
            Expr::Match(es, cases) => {
                for e in es {
                    self.traverse_scoped(e, f.clone())?;
                }
                for c in cases {
                    let mut l = 0;
                    for p in &mut c.patterns {
                        let vec = p.vars();
                        match p {
                            Pat::Var(_) => {} // TODO: refine pattern var
                            Pat::Wildcard => {}
                            Pat::Absurd => {}
                            Pat::Cons(_, _, _) => {}
                            Pat::Forced(e) => {
                                self.traverse_scoped(e, f.clone())?;
                            }
                        }
                        for var in vec {
                            self.push(var.clone());
                            l += 1;
                        }
                    }
                    if let Some(e) = &mut c.body {
                        self.traverse_scoped(e, f.clone())?;
                    }
                    for _ in 0..l {
                        self.pop();
                    }
                }
            }
            Expr::Lit(_, _) => {}
        }
        Ok(())
    }

    fn funcs_parser(&self) -> Parser!(HashMap<Ident, Operator>) {
        let expr = self.expr();
        let prim_expr = prim_expr(&expr);
        let param_parser = param(&expr, &prim_expr);
        let params = params(&param_parser);
        let ident = ident_parser();

        let func = just(Token::Fn)
            .ignore_then(
                ident
                    .map_with_span(|name, span| (name, span))
                    .labelled("function name"),
            )
            .then(params)
            .map(|((name, name_span), params)| {
                let params_num = params.len();
                let def = Operator::from_ident(Associativity::None, 10, &name, params_num);
                ((name, name_span), def)
            })
            .then_ignore(take_until(just(Token::Fn).rewind().ignored().or(end())))
            .labelled("function");

        func.repeated()
            .try_map(|fs, _| {
                let mut funcs = HashMap::new();
                for ((name, name_span), f) in fs {
                    if funcs.insert(name.clone(), f).is_some() {
                        return Err(Simple::custom(
                            name_span.clone(),
                            format!("Function '{}' already exists", name),
                        ));
                    }
                }
                Ok(funcs)
            })
            .then_ignore(end())
    }
}

fn prim_expr(expr: &(Parser!(Expr))) -> Parser!(Expr) {
    {
        let ident = ident_parser().debug("ident");
        let universe = universe_parser().debug("universe");
        let literal = literal_parser().debug("literal");
        let tuple = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .at_least(2)
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .debug("tuple");

        let very_prim_expr = select! {
            Token::Underscore, loc => Expr::Hole(loc),
            Token::MetaIdent(..), loc => Expr::Hole(loc),
        }
        .debug("very prim expr");
        universe
            .map_with_span(|uni, loc| Expr::Universe(loc, uni))
            .or(literal.map_with_span(|literal, loc| Expr::Lit(loc, literal)))
            .or(ident.map(Expr::Var))
            .or(tuple.map_with_span(|es, loc| Expr::Tuple(loc, es)))
            .or(expr
                .clone()
                .delimited_by(just(Token::LParen), just(Token::RParen)))
            .or(very_prim_expr)
    }
    .debug("prim_expr")
}

pub fn lexer(
    mut additional_tokens: Vec<String>,
    refine: bool,
) -> Parser!(char, Vec<(Token<'static>, Loc)>) {
    additional_tokens.sort_by(|a, b| b.len().cmp(&a.len()));
    let ident = none_of(FORBIDDEN)
        .repeated()
        .at_least(1)
        .collect::<String>();

    let universe = just("Type").ignore_then(
        text::digits::<char, _>(10)
            .or_not()
            .map(|opt| opt.unwrap_or_default()),
    );
    let meta = just("?").ignore_then(ident.clone());
    let str = just('"')
        .ignore_then(filter(|c| *c != '"').repeated())
        .then_ignore(just('"'))
        .collect::<String>();

    let braces = just("(").to(Token::LParen).or(just(")").to(Token::RParen));
    let base_token = universe
        .map(Token::Universe)
        .or(meta.map(|s| Token::MetaIdent(s)))
        .or(str.map(Token::Str))
        .or(just("forall").to(Token::Pi))
        .or(just("data").padded().to(Token::Data))
        .or(just("codata").to(Token::Codata))
        .or(just("match").to(Token::Match))
        .or(just("@").to(Token::At))
        .or(just("#").to(Token::Hash))
        .or(just(":=").to(Token::Assignment))
        .or(just(":").to(Token::Colon))
        .or(just(",").to(Token::Comma))
        .or(just(".").to(Token::Dot))
        .or(just("=>").to(Token::DArrow))
        .or(just("lam").to(Token::Lam))
        .or(just("fn").to(Token::Fn))
        .or(just("let").to(Token::Let))
        .or(just("|").to(Token::Pipe))
        .or(just("->").to(Token::RArrow))
        .or(just("_").to(Token::Underscore))
        .or(just("!").to(Token::Bang))
        .or(just("?").to(Token::Question))
        .or(just("{").to(Token::LBrace))
        .or(just("}").to(Token::RBrace))
        .or(just("[").to(Token::LBracket))
        .or(just("]").to(Token::RBracket))
        .or(braces);

    let token = if additional_tokens.is_empty() {
        box_parser(base_token)
    } else {
        let first = additional_tokens.remove(0);
        let init = just(first).map(|s| Token::Ident(s));
        let add_tokens_ref = additional_tokens
            .into_iter()
            .map(|s| just(s).map(|s| Token::Ident(s)))
            .fold(box_parser(init), |acc, x| {
                let or = acc.or(x);
                box_parser(or)
            });

        if refine {
            let p = add_tokens_ref.or(base_token);
            box_parser(p)
        } else {
            let p = base_token.or(add_tokens_ref);
            box_parser(p)
        }
    };
    let token = if !refine {
        box_parser(token.or(ident.clone().map(|x| Token::Ident(x))))
    } else {
        box_parser(token)
    };
    let token = token.or(text::digits(10).map(|s| Token::Nat(s)));
    let token = if refine {
        box_parser(token.or(ident.map(|x| Token::Ident(x))))
    } else {
        box_parser(token)
    };
    let comment = just("--").then(take_until(just('\n'))).ignored().padded();
    let block_comment = just("/*")
        .then(take_until(just("*/")))
        .then(just("*/"))
        .ignored()
        .padded();
    let whitespace = text::whitespace().at_least(1).ignored();
    token
        .map_with_span(|tok, span| (tok, span))
        .padded_by(whitespace.or(comment).or(block_comment).repeated())
        .repeated()
}

fn ident_parser() -> Parser!(Ident) {
    select! {
        Token::Ident(ident), loc => Ident::located(ident, loc)
    }
}

fn universe_parser() -> Parser!(Universe) {
    select! {
        Token::Universe(lvl) => Universe(
            if lvl.is_empty() {
                0
            } else {
            lvl.parse()
                .expect("the number is always valid, because we've used `digits`; qed")
            }
        )
    }
}

fn str_parser() -> Parser!(String) {
    select! {
        Token::Str(s) => s
    }
}

fn nat_parser() -> Parser!(Nat) {
    select! {
        Token::Nat(n) =>
            n.parse::<Nat>()
                .expect("the number is always valid, because we've used `digits`; qed"),
    }
}

fn literal_parser() -> Parser!(Literal) {
    nat_parser()
        .map(Literal::Nat)
        .or(str_parser().map(Literal::Str))
}

fn params(
    param_parser: &(impl chumsky::Parser<Token<'static>, Vec<Param>, Error = ParseError<'static>>
          + Clone),
) -> Parser!(Vec<Param>) {
    param_parser
        .clone()
        .repeated()
        .flatten()
        .labelled("params_parser")
}

fn param(expr: &Parser!(Expr), prim_expr: &Parser!(Expr)) -> Parser!(Vec<Param>) {
    {
        let ident = ident_parser();

        let params = ident
            .clone()
            .repeated()
            .at_least(1)
            .then_ignore(just(Token::Colon))
            .then(expr.clone());

        fn build_params(ps: Vec<Ident>, ty: Expr, plicit: Plicitness) -> Vec<Param> {
            ps.into_iter()
                .map(|ident| {
                    let p = Param::new(ident, ty.clone(), plicit);
                    // debug!(target: "parser", "parsed explicit param: {p}");
                    p
                })
                .collect()
        }

        let paramss = (params
            .clone()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(|(ps, ty)| build_params(ps, ty, Explicit)))
        .or(params
            .clone()
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .map(|(ps, ty)| build_params(ps, ty, Implicit)))
        .or(prim_expr.clone().map(|e| {
            let param = Param::from_type(e, Explicit);
            // debug!(target: "parser", "parsed explicit param: {param}");
            vec![param]
        }))
        .labelled("param_parser");
        paramss
    }
    .debug("param_parser")
}

fn forall_params(expr: &Parser!(Expr)) -> Parser!(Vec1<Param>) {
    {
        ident_parser()
            .clone()
            .repeated()
            .at_least(1)
            .then_ignore(just(Token::Colon))
            .then(expr.clone())
            .map(|(idents, ty)| {
                Vec1::try_from_vec(
                    idents
                        .into_iter()
                        .map(|ident| Param::new(ident, ty.clone(), Explicit))
                        .collect(),
                )
                .unwrap()
            })
    }
    .debug("forall params")
}

fn case(expr: &Parser!(Expr), pattern: &(Parser!(Pat))) -> Parser!(Case) {
    just(Token::Pipe)
        .ignore_then(pattern.clone().separated_by(just(Token::Comma)))
        .then(
            just(Token::DArrow)
                .ignore_then(expr.clone())
                .or_not()
                .debug("=> ..."),
        )
        .map(|(pats, body)| Case::new(pats, body))
        .debug("case")
}

fn pattern(
    prim_expr: &(impl chumsky::Parser<Token<'static>, Expr, Error = ParseError<'static>>
          + Clone
          + 'static),
) -> Parser!(Pat: Clone + 'static) {
    fn pat_rest(
        prim_expr: &(impl chumsky::Parser<Token<'static>, Expr, Error = ParseError<'static>>
              + Clone
              + 'static),
        rec_pattern: &(impl chumsky::Parser<Token<'static>, Pat, Error = ParseError<'static>>
              + Clone
              + 'static),
    ) -> Parser!(Pat: Clone + 'static) {
        just(Token::Underscore)
            .to(Pat::Wildcard)
            .or(rec_pattern
                .clone()
                .delimited_by(just(Token::LParen), just(Token::RParen)))
            .or(just(Token::Bang).to(Pat::Absurd))
            .or(just(Token::Dot)
                .ignore_then(prim_expr.clone())
                .map(Pat::Forced))
    }

    let var_pat = ident_parser().map(Pat::Var);
    let pat_cons_start = just(Token::Dot).or_not().then(ident_parser());
    let sub_pat = recursive(|prim_pattern: Recursive<_, Pat, _>| {
        var_pat
            .clone()
            .or(pat_cons_start
                .clone()
                .then(prim_pattern.clone().repeated().at_least(1))
                .map(|((dot, con), args)| Pat::cons_surf(dot.is_some(), con, args)))
            .or(pat_rest(prim_expr, &prim_pattern))
    });
    recursive(|top_pat| {
        pat_cons_start
            .then(sub_pat.clone().repeated().at_least(1))
            .map(|((dot, con), args)| Pat::cons_surf(dot.is_some(), con, args))
            .or(var_pat)
            .or(pat_rest(prim_expr, &top_pat))
    })
    .debug("pattern")
}

fn meta_attr() -> Parser!(MetaAttr) {
    let prim_meta_attr = recursive(|prim_meta_attr: Recursive<_, MetaAttr, _>| {
        let ident = ident_parser();
        let meta_field = ident
            .clone()
            .then_ignore(just(Token::Assignment))
            .then(str_parser())
            .map(|(name, value)| (name, value));

        let meta_attr_app =
            ident
                .clone()
                .then(prim_meta_attr.clone().repeated())
                .map(|(f, args)| {
                    if args.is_empty() {
                        MetaAttr::Ident(f)
                    } else {
                        MetaAttr::App(f, Vec1::try_from_vec(args).unwrap())
                    }
                });

        meta_attr_app
            .clone()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .or(meta_field
                .clone()
                .map(|field| MetaAttr::Struct(Vec1::new(field))))
            .or(meta_field
                .clone()
                .separated_by(just(Token::Comma))
                .at_least(1)
                .map(|fields| MetaAttr::Struct(Vec1::try_from_vec(fields).unwrap())))
            .or(ident.map(MetaAttr::Ident))
    });

    just(Token::Hash)
        .ignore_then(just(Token::LParen))
        .ignore_then(prim_meta_attr)
        .then_ignore(just(Token::RParen))
}

pub fn cons(
    params: &(Parser!(Vec<Param>)),
) -> impl chumsky::Parser<Token<'static>, NamedTele, Error = ParseError<'static>> {
    let ident = ident_parser();
    just(Token::Pipe)
        .ignore_then(ident)
        .then(params.clone())
        .map(|(name, params)| NamedTele::new(name, params.into()))
}

impl Default for Parser {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Ord)]
enum Associativity {
    Left,
    Right,
    None,
}

impl PartialOrd for Associativity {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        use Associativity::*;
        Some(match (self, other) {
            (Left, _) => Ordering::Less,
            (_, Left) => Ordering::Greater,
            (None, _) => Ordering::Greater,
            (_, None) => Ordering::Less,
            _ => Ordering::Equal,
        })
    }
}

type Precedence = u8;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum OperatorPattern {
    Tok(String),
    Expr,
}

impl OperatorPattern {
    pub(crate) fn as_token(&self) -> Token {
        match self {
            OperatorPattern::Tok(s) => Token::Ident(s.clone()),
            OperatorPattern::Expr => unreachable!(),
        }
    }
}

impl Display for OperatorPattern {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            OperatorPattern::Tok(s) => write!(f, "{}", s),
            OperatorPattern::Expr => write!(f, "<expr>"),
        }
    }
}

impl PartialOrd<Self> for OperatorPattern {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OperatorPattern {
    fn cmp(&self, other: &Self) -> Ordering {
        use OperatorPattern::*;
        match (self, other) {
            (Tok(s1), Tok(s2)) => s1.cmp(s2),
            (Tok(_), Expr) => Ordering::Greater,
            (Expr, Tok(_)) => Ordering::Less,
            (Expr, Expr) => Ordering::Equal,
        }
    }
}

impl OperatorPattern {
    pub fn from_token(s: String) -> Self {
        assert!(FORBIDDEN.chars().all(|c| !s.contains(c)));
        OperatorPattern::Tok(s)
    }

    pub fn is_expr(&self) -> bool {
        match self {
            OperatorPattern::Expr => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct OperatorPatterns(Vec<OperatorPattern>);

impl OperatorPatterns {
    pub fn is_unary(&self) -> bool {
        self.0.len() == 2
    }

    pub fn is_binary(&self) -> bool {
        self.0.len() == 3
    }

    pub fn is_prefix(&self) -> bool {
        self.is_unary() && self.0[1].is_expr()
    }

    pub fn is_postfix(&self) -> bool {
        self.is_unary() && self.0[0].is_expr()
    }

    pub fn new(patterns: Vec<OperatorPattern>) -> Self {
        let mut is_expr = patterns[0].is_expr();
        assert!(
            patterns.iter().all(|p| {
                is_expr = !is_expr;
                p.is_expr() != is_expr
            }),
            "can't have consecutive patterns of the same kind"
        );
        Self(patterns)
    }
}

impl PartialOrd<Self> for OperatorPatterns {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OperatorPatterns {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .len()
            .cmp(&other.0.len())
            .reverse()
            .then(self.0.cmp(&other.0))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Operator {
    associativity: Associativity,
    precedence: Precedence,
    patterns: OperatorPatterns,
}

impl Operator {
    fn from_ident(
        associativity: Associativity,
        precedence: Precedence,
        ident: &str,
        params_num: usize,
    ) -> Self {
        let mut patterns = Vec::new();
        let parts = ident.split('_');
        let mut expr_num = 0;
        let starts_with_underscore = ident.starts_with('_');
        for (i, part) in parts.enumerate() {
            if !part.is_empty() {
                let offset = if starts_with_underscore { 1 } else { 0 };
                if i > offset {
                    patterns.push(OperatorPattern::Expr);
                    expr_num += 1;
                }
                patterns.push(OperatorPattern::from_token(part.to_string()));
            } else {
                patterns.push(OperatorPattern::Expr);
                expr_num += 1;
            }
        }
        if expr_num > params_num {
            panic!("Too many underscores in {}", ident);
        }
        Self::new(associativity, precedence, patterns)
    }

    fn new(
        mut associativity: Associativity,
        precedence: Precedence,
        patterns: Vec<OperatorPattern>,
    ) -> Self {
        let patterns = OperatorPatterns::new(patterns);
        match associativity {
            Associativity::Left | Associativity::Right => {
                assert!(patterns.is_binary());
            }
            Associativity::None => {
                if patterns.is_binary() {
                    associativity = Associativity::Left;
                }
            }
        }
        Self {
            associativity,
            precedence,
            patterns,
        }
    }
}

struct State {
    n: usize,
    def_map: HashMap<String, Operator>,
}

#[cfg(test)]
mod tests {
    use crate::syntax::parser::Parser;
    use crate::syntax::surf::Expr::{self};
    use crate::syntax::token::Token;
    use crate::syntax::{Ident, Loc};
    use chumsky::error::Simple;
    use chumsky::Error;

    #[test]
    fn parse_pi() {
        let _ = env_logger::try_init();

        let mut parser = Parser::default();

        assert_eq!(
            parser.parse_expr("(T : A) -> T").unwrap(),
            Expr::pi_many(
                vec![(Ident::new("T"), Expr::var("A"))].into_iter(),
                Expr::var("T"),
            )
        );

        assert_eq!(
            parser.parse_expr("(T U V : A) -> T").unwrap(),
            Expr::pi_many(
                vec![
                    (Ident::new("T"), Expr::var("A")),
                    (Ident::new("U"), Expr::var("A")),
                    (Ident::new("V"), Expr::var("A")),
                ]
                .into_iter(),
                Expr::var("T"),
            )
        );

        assert_eq!(
            parser.parse_expr("(T U : A) -> (V : B) -> T").unwrap(),
            Expr::pi_many(
                vec![
                    (Ident::new("T"), Expr::var("A")),
                    (Ident::new("U"), Expr::var("A")),
                    (Ident::new("V"), Expr::var("B")),
                ]
                .into_iter(),
                Expr::var("T"),
            )
        );

        assert_eq!(
            parser.parse_expr("(T U : A) -> X : A -> T").unwrap_err(),
            Simple::expected_input_found(
                Loc::new(17, 19),
                vec![None, Some(Token::LParen), Some(Token::RArrow)],
                Some(Token::Colon),
            )
        );
        assert_eq!(
            parser.parse_expr("T U : A -> T").unwrap_err(),
            Simple::expected_input_found(
                Loc::new(4, 5),
                vec![Some(Token::LParen), None],
                Some(Token::Colon),
            )
        );
    }

    #[test]
    fn parse_lam() {
        let mut parser = Parser::default();

        assert_eq!(
            parser.parse_expr("lam x : T => x").unwrap(),
            Expr::lam_many(
                Expr::var("x"),
                vec![(Ident::new("x"), Expr::var("T"))].into_iter()
            )
        );

        assert_eq!(
            parser.parse_expr("lam (x : T) => x").unwrap(),
            Expr::lam_many(
                Expr::var("x"),
                vec![("x".into(), Expr::var("T"))].into_iter(),
            )
        );

        assert_eq!(
            parser.parse_expr("lam x y z : T => x").unwrap(),
            Expr::lam_many(
                Expr::var("x"),
                vec![
                    ("x".into(), Expr::var("T")),
                    ("y".into(), Expr::var("T")),
                    ("z".into(), Expr::var("T")),
                ]
                .into_iter(),
            )
        );

        assert_eq!(
            parser.parse_expr("lam (x y : T) (z : U) => x").unwrap(),
            Expr::lam_many(
                Expr::var("x"),
                vec![
                    ("x".into(), Expr::var("T")),
                    ("y".into(), Expr::var("T")),
                    ("z".into(), Expr::var("U"))
                ]
                .into_iter(),
            )
        );
        assert!(parser.parse_expr("lam x y : T => x").is_ok());

        assert!(parser.parse_expr("lam (a b : T) c : U => a").is_err());
    }
}
