use crate::error::Error::Parse;
use crate::syntax::core::Boxed as _;
use crate::syntax::surf::*;
use crate::syntax::surf::{Decl, Expr, Prog};
use crate::syntax::token::Token;
use crate::syntax::Plicitness::{Explicit, Implicit};
use crate::syntax::{Ident, Loc};
use crate::syntax::{Plicitness, Universe};
use ariadne::{Color, Fmt, Label, Report, ReportBuilder, ReportKind, Source};
use chumsky::extra::Full;
use chumsky::input::{MapExtra, SpannedInput, Stream};
use chumsky::label::LabelError;
use chumsky::prelude::end;
use chumsky::prelude::*;
use chumsky::recursive::Direct;
use chumsky::text::newline;
use chumsky::util::MaybeRef;
use chumsky::Parser as _;
use codespan_reporting::files::SimpleFile;
use derive_more::{Deref, From};
use itertools::Itertools;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Formatter;
use std::fmt::{Debug, Display};
use std::path::PathBuf;
use std::str::FromStr;
use std::{fs, iter};
use vec1::{vec1, Vec1};

#[derive(From, PartialEq, Eq, Clone, Deref)]
pub struct ParseError<'a, T = Token<'a>, S = SimpleSpan>(
    #[from]
    #[deref]
    pub Rich<'a, T, S>,
);

impl<'a, T, S> ParseError<'a, T, S> {
    /// Transform this error's tokens using the given function.
    ///
    /// This is useful when you wish to combine errors from multiple compilation passes (lexing and parsing, say) where
    /// the token type for each pass is different (`char` vs `MyToken`, say).
    pub fn map_token<U, F: FnMut(T) -> U>(self, f: F) -> ParseError<'a, U, S>
    where
        T: Clone,
    {
        ParseError(self.0.map_token(f))
    }

    pub fn into_owned<'b>(self) -> ParseError<'b, T, S>
    where
        T: Clone,
    {
        ParseError(self.0.into_owned())
    }
}

impl<'a, I: Input<'a>> chumsky::error::Error<'a, I> for ParseError<'a, I::Token, I::Span>
where
    I::Token: PartialEq,
    Rich<'a, I::Token, I::Span, &'static str>: chumsky::error::Error<'a, I>,
{
    fn expected_found<E: IntoIterator<Item=Option<MaybeRef<'a, I::Token>>>>(
        expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        Self(Rich::expected_found(expected, found, span))
    }

    fn merge(self, other: Self) -> Self {
        Self(self.0.merge(other.0))
    }

    fn merge_expected_found<E: IntoIterator<Item=Option<MaybeRef<'a, I::Token>>>>(
        self,
        expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        Self(self.0.merge_expected_found(expected, found, span))
    }

    fn replace_expected_found<E: IntoIterator<Item=Option<MaybeRef<'a, I::Token>>>>(
        self,
        expected: E,
        found: Option<MaybeRef<'a, I::Token>>,
        span: I::Span,
    ) -> Self {
        Self(self.0.replace_expected_found(expected, found, span))
    }
}

impl<'a, I: Input<'a>> LabelError<'a, I, &'static str> for ParseError<'a, I::Token, I::Span>
where
    I::Token: PartialEq,
    Rich<'a, I::Token, I::Span, &'static str>: LabelError<'a, I, &'static str>,
{
    fn label_with(&mut self, label: &'static str) {
        self.0.label_with(label)
    }

    fn in_context(&mut self, label: &'static str, span: I::Span) {
        self.0.in_context(label, span)
    }
}

impl<'a, T: Display, S: Display> Display for ParseError<'a, T, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'a, T: Debug, S: Debug> Debug for ParseError<'a, T, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl<'a, T: Display + Debug, S: Display + Debug> std::error::Error for ParseError<'a, T, S> {}

pub type TokenTreeInput<'tokens, 'src> =
SpannedInput<Token<'src>, SimpleSpan, &'tokens [(Token<'src>, SimpleSpan)]>;
pub type ParserExtra<'a, T, S = SimpleSpan> = Full<ParseError<'a, T, S>, (), ()>;

const UNIT: &() = &();

macro_rules! Parser {
    ($tl:lifetime, $sl:lifetime, $O:path) => { impl chumsky::Parser<$tl, TokenTreeInput<$tl, $sl>, $O, ParserExtra<$tl, Token<$sl>>> + Clone };
    ($tl:lifetime, $sl:lifetime, $O:path: $($bounds:tt)*) => { impl chumsky::Parser<$tl, TokenTreeInput<$tl, $sl>, $O, ParserExtra<$tl, Token<$sl>>> + $($bounds)* };
    ($tl:lifetime, $sl:lifetime, $I:ty, $O:path) => { impl chumsky::Parser<$tl, $I, $O, Full<Rich<$tl, $I, SimpleSpan>, (), ()>> };
    ($O:path) => { impl chumsky::Parser<'static, TokenTreeInput<'static, 'static>, $O, ParserExtra<'static>> + Clone };
    ($O:path: $($bounds:tt)*) => { impl chumsky::Parser<'static, TokenTreeInput<'static, 'static>, $O, ParserExtra<'static>> + $($bounds)* };
    ($I:ty, $O:path) => { impl chumsky::Parser<'static, $I, $O, Full<Rich<'static, $I, SimpleSpan>, (), ()>> };
}

type BoxedParser<'a, 'b, I, O, E> = Boxed<'a, 'b, I, O, E>;

#[inline]
fn box_parser<'a, I: Clone + Input<'a>, O, E: extra::ParserExtra<'a, I>>(
    p: impl chumsky::Parser<'a, I, O, E> + 'a,
) -> BoxedParser<'a, 'a, I, O, E> {
    chumsky::Parser::boxed(p)
}

const FORBIDDEN: &str = "(){}, \n\t\r";
const DEBUG_LEXER: bool = false;

pub struct Parser {
    file: SimpleFile<String, String>,
    scope: Vec<Ident>,
    should_refine: bool,
}

impl Parser {
    fn tokenize<'src>(
        &self,
        input: &'src str,
        lexer_ignore_idents: bool,
    ) -> ParseResult<Vec<(Token<'src>, SimpleSpan)>, ParseError<'src, char>> {
        let additional_tokens = self
            .scope
            .iter()
            .map(|id| id.text.clone())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let results = if DEBUG_LEXER {
            unimplemented!()
        } else {
            lexer(additional_tokens, lexer_ignore_idents).parse(input)
        };
        results
    }

    fn parse_using<'tok, 'src: 'tok, T: Display + Debug>(
        &self,
        parser: impl chumsky::Parser<
            'tok,
            TokenTreeInput<'tok, 'src>,
            T,
            ParserExtra<'tok, Token<'src>>,
        >,
        tokens: TokenTreeInput<'tok, 'src>,
    ) -> ParseResult<T, ParseError<'tok, Token<'src>>>
    where
            for<'a> &'a T: Display,
    {
        parser.then_ignore(end()).parse(tokens)
    }

    fn handle_errors<'src, T: Clone + ToString>(
        errors: Vec1<ParseError<'src, T>>,
        input: &'src str,
    ) -> ParseError<'static, String> {
        let err = errors.first().clone();

        let errors = errors.into_iter().map(|e| e.map_token(|c| c.to_string()));
        errors.for_each(|e| {
            let report = Report::build(ReportKind::Error, (), e.span().start);
            let report = Self::handle_error(e, report);
            report.finish().print(Source::from(input)).unwrap();
        });

        err.map_token(move |x| x.to_string()).into_owned()
    }

    fn handle_error<'a>(e: ParseError<String>, report: ReportBuilder<'a, Loc>) -> ReportBuilder<'a, Loc> {
        let builder = match e.0.reason() {
            chumsky::error::RichReason::ExpectedFound { expected, found } => {
                let unexpected = if found.is_some() {
                    "Unexpected token in input"
                } else {
                    "Unexpected end of input"
                };
                report
                    .with_message(if expected.len() != 0 {
                        format!(
                            "{unexpected}, expected {}",
                            expected
                                .into_iter()
                                .map(|expected| expected.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    } else {
                        format!("{unexpected}")
                    })
                    .with_label(
                        Label::new(Loc::from(*e.span()))
                            .with_message(format!(
                                "Unexpected token {}",
                                found
                                    .as_deref()
                                    .unwrap_or((&"end of file".to_string()).into())
                                    .fg(Color::Red)
                            ))
                            .with_color(Color::Red),
                    )
            }
            chumsky::error::RichReason::Custom(msg) => report.with_message(msg).with_label(
                Label::new(Loc::from(*e.span()))
                    .with_message(format!("{}", msg.fg(Color::Red)))
                    .with_color(Color::Red),
            ),
            chumsky::error::RichReason::Many(es) => {
                let mut msg = String::new();
                for e in es {
                    msg.push_str(&format!("{}\n", e));
                }
                report.with_message("Other errors").with_label(
                    Label::new(Loc::from(*e.span()))
                        .with_message(format!("{}", msg.fg(Color::Red)))
                        .with_color(Color::Red),
                )
            }
        };
        builder
    }

    pub fn parse_expr<'inp>(
        &mut self,
        input: &'inp str,
    ) -> Result<Expr, ParseError<'static, String>> {
        let res = self.tokenize(input, false).into_result();
        match res {
            Ok(tokens) => {
                let spanned = tokens.as_slice().spanned((input.len()..input.len()).into());
                match self.parse_using(self.expr(), spanned).into_result() {
                    Ok(mut expr) => {
                        if self.should_refine {
                            self.refine(&mut expr)
                                .map_err(|e| e.map_token(|t| t.to_string()).into_owned())?;
                        }
                        Ok(expr)
                    }
                    Err(es) => Err(Self::handle_errors(Vec1::try_from_vec(es).unwrap(), input)),
                }
            }
            Err(es) => Err(Self::handle_errors(Vec1::try_from_vec(es).unwrap(), input)),
        }
    }

    pub fn parse_decl<'inp>(
        &mut self,
        input: &'inp str,
    ) -> Result<Decl, ParseError<'static, String>> {
        let res = self.tokenize(input, false).into_result();
        match res {
            Ok(tokens) => {
                let spanned = tokens.as_slice().spanned((input.len()..input.len()).into());
                match self.parse_using(self.decl(), spanned).into_result() {
                    Ok(mut decl) => {
                        if self.should_refine {
                            let ident = decl.name();
                            self.scope.push(ident.clone());
                            self.refine_decl(&mut decl)
                                .map_err(|e| e.map_token(|t| t.to_string()).into_owned())?;
                        }
                        Ok(decl)
                    }
                    Err(es) => Err(Self::handle_errors(Vec1::try_from_vec(es).unwrap(), input)),
                }
            }
            Err(es) => Err(Self::handle_errors(Vec1::try_from_vec(es).unwrap(), input)),
        }
    }

    pub fn parse_prog<'inp>(
        &mut self,
        input: &'inp str,
    ) -> Result<Prog, ParseError<'static, String>> {
        let res = self.tokenize(input, false).into_result();
        match res {
            Ok(tokens) => {
                let spanned = tokens.as_slice().spanned((input.len()..input.len()).into());
                match self.parse_using(self.prog(), spanned).into_result() {
                    Ok(mut prog) => {
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
                                self.refine_decl(decl)
                                    .map_err(|e| e.map_token(|t| t.to_string()).into_owned())?;
                            }
                        }
                        Ok(prog)
                    }
                    Err(es) => Err(Self::handle_errors(Vec1::try_from_vec(es).unwrap(), input)),
                }
            }
            Err(es) => Err(Self::handle_errors(Vec1::try_from_vec(es).unwrap(), input)),
        }
    }

    pub fn parse_prog_with_std<'inp>(
        &mut self,
        input: &'inp str,
        path: Option<PathBuf>,
    ) -> Result<Prog, ParseError<'static, String>> {
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

    pub fn expr<'t, 's: 't>(&self) -> Parser!('t, 's, Expr) {
        recursive(|expr: Recursive<Direct<_, Expr, _>>| {
            let prim_expr = prim_expr(&expr);
            let pattern = pattern(&prim_expr);
            let case = case(&expr, &pattern);
            let forall_params = forall_params(&expr);
            let param_parser = param(&expr, &prim_expr);
            let pi = (param_parser.clone().then_ignore(just(Token::RArrow)))
                .repeated()
                .at_least(1)
                .collect::<Vec<_>>()
                .labelled("parsed pi and waiting for <expr>")
                .then(expr.clone())
                .labelled("pi");
            let lam = just(Token::Lam)
                .ignore_then(
                    forall_params.clone().or(forall_params
                        .clone()
                        .delimited_by(just(Token::LParen), just(Token::RParen))
                        .repeated()
                        .at_least(1)
                        .collect()
                        .map(|v: Vec<_>| {
                            Vec1::try_from_vec(v.into_iter().flatten().collect()).unwrap()
                        })),
                )
                .then_ignore(just(Token::DArrow))
                .then(expr.clone())
                .labelled("lam");
            let mat = just(Token::Match)
                .ignore_then(
                    expr.clone()
                        .separated_by(just(Token::Comma))
                        .at_least(1)
                        .collect::<Vec<_>>(),
                )
                .then_ignore(just(Token::LBrace))
                .then(case.clone().repeated().collect::<Vec<_>>())
                .then_ignore(just(Token::RBrace))
                .labelled("mat");
            let app = prim_expr
                .clone()
                .then(prim_expr.clone().repeated().collect::<Vec<_>>())
                .labelled("app");

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
            .labelled("expr")
    }

    pub fn decl<'t, 's: 't>(&self) -> Parser!('t, 's, Decl:) {
        let expr = self.expr();
        let prim_expr = prim_expr(&expr);
        let param_parser = param(&expr, &prim_expr);
        let params = params(&param_parser);
        let ident = ident_parser();

        let meta_attrs = meta_attr().repeated().collect::<Vec<_>>();
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
            .then(cons(&params).repeated().collect::<Vec<_>>());
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
            .recover_with(skip_then_retry_until(
                any().ignored(),
                just(Token::Fn)
                    .or(just(Token::Data))
                    .or(just(Token::Codata))
                    .ignored(),
            ))
    }

    pub fn prog<'t, 's: 't>(
        &self,
    ) -> impl chumsky::Parser<'t, TokenTreeInput<'t, 's>, Prog, ParserExtra<'t, Token<'s>>> {
        self.decl().repeated().collect::<Vec<_>>().map(Prog)
    }

    fn push(&mut self, name: Ident) {
        self.scope.push(name);
    }

    fn pop(&mut self) {
        self.scope.pop();
    }

    pub fn refine<'inp>(
        &mut self,
        expr: &'inp mut Expr,
    ) -> Result<(), ParseError<'static, String>> {
        debug!(target: "parser", "refining {}", expr);
        self.traverse_scoped(expr, |var, scope| {
            let mut parser = Parser::new().scoped(scope);
            debug!(target: "parser", "Parse scoped: {:?}", var);
            parser.should_refine = false;
            let mut e = parser.parse_expr(&var)?; // .map_err(err_to_static)?;
            debug!(target: "parser", "Parse scoped out: {:?}", e);
            if let Expr::Var(v) = &e {
                if v == var {
                    return Ok(None);
                }
            }
            if e != Expr::Var(var.clone()) {
                parser.refine(&mut e)?;
            }
            return Ok(Some(e));
        })
    }

    pub fn refine_decl<'inp>(
        &mut self,
        decl: &'inp mut Decl,
    ) -> Result<(), ParseError<'static, String>> {
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
        f: impl for<'b> Fn(&'b Ident, Vec<Ident>) -> Result<Option<Expr>, ParseError<'static, String>>
        + Clone,
    ) -> Result<(), ParseError<'static, String>> {
        match expr {
            Expr::Var(ident) => {
                if let Some(e2) = f(ident, self.scope.clone())? {
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
            Expr::Braced(e) => {
                self.traverse_scoped(e, f.clone())?;
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

    fn funcs_parser<'t, 's: 't>(&self) -> Parser!('t, 's, HashMap<Ident, Operator>) {
        let expr = self.expr();
        let prim_expr = prim_expr(&expr);
        let param_parser = param(&expr, &prim_expr);
        let params = params(&param_parser);
        let ident = ident_parser();

        let func = just(Token::Fn)
            .ignore_then(
                ident
                    .map_with(|name, e| (name, e.span()))
                    .labelled("function name"),
            )
            .then(params)
            .map(|((name, name_span), params)| {
                let params_num = params.len();
                let def = Operator::from_ident(Associativity::None, 10, &name, params_num);
                ((name, name_span), def)
            })
            // .then_ignore(take_until(just(Token::Fn).rewind().ignored().or(end())))
            .labelled("function");

        func.repeated()
            .collect::<Vec<_>>()
            .try_map(|fs, _| {
                let mut funcs = HashMap::new();
                for ((name, name_span), f) in fs {
                    if funcs.insert(name.clone(), f).is_some() {
                        return Err(Rich::custom(
                            name_span.clone(),
                            format!("Function '{}' already exists", name),
                        )
                            .into());
                    }
                }
                Ok(funcs)
            })
            .then_ignore(end())
    }
}

fn prim_expr<'t, 's: 't>(expr: &(Parser!('t, 's, Expr))) -> Parser!('t, 's, Expr) {
    {
        let ident = ident_parser().labelled("ident");
        let universe = universe_parser().labelled("universe");
        let literal = literal_parser().labelled("literal");
        let tuple = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .at_least(2)
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .labelled("tuple");

        let very_prim_expr = select! {
            Token::Underscore = e => { let s: SimpleSpan = e.span(); Expr::Hole(s.into())},
            Token::MetaIdent(..) = e => { let s: SimpleSpan = e.span(); Expr::Hole(s.into()) },
        }
            .labelled("very prim expr");
        universe
            .map_with(|uni, e| Expr::Universe(e.span().into(), uni))
            .or(literal.map_with(|literal, e| Expr::Lit(e.span().into(), literal)))
            .or(ident.map(Expr::Var))
            .or(tuple.map_with(|es, e| Expr::Tuple(e.span().into(), es)))
            .or(expr
                .clone()
                .delimited_by(just(Token::LParen), just(Token::RParen)))
            .or(expr
                .clone()
                .delimited_by(just(Token::LBrace), just(Token::RBrace))
                .map(|e| e))
            .or(very_prim_expr)
    }
        .labelled("prim_expr")
}

pub fn lexer<'a>(
    mut additional_tokens: Vec<String>,
    refine: bool,
) -> impl chumsky::Parser<'a, &'a str, Vec<(Token<'a>, SimpleSpan)>, ParserExtra<'a, char>> {
    additional_tokens.sort_by(|a, b| b.len().cmp(&a.len()));

    let ident = none_of(FORBIDDEN)
        .repeated()
        .at_least(1)
        .collect::<String>();

    let universe = just("Type").ignore_then(
        text::int::<&str, _, _>(10)
            .map(ToString::to_string)
            .or_not()
            .map(|opt| opt.unwrap_or_default()),
    );
    let meta = just("?").ignore_then(ident.clone());

    let escape = just('\\')
        .then(choice((
            just('\\'),
            just('/'),
            just('"'),
            just('b').to('\x08'),
            just('f').to('\x0C'),
            just('n').to('\n'),
            just('r').to('\r'),
            just('t').to('\t'),
            just('u').ignore_then(text::digits(16).exactly(4).to_slice().validate(
                |digits, e, emitter| {
                    char::from_u32(u32::from_str_radix(digits, 16).unwrap()).unwrap_or_else(|| {
                        emitter.emit(Rich::custom(e.span(), "invalid unicode character").into());
                        '\u{FFFD}' // unicode replacement character
                    })
                },
            )),
        )))
        .ignored();
    let str = none_of("\\\"")
        .ignored()
        .or(escape)
        .repeated()
        .to_slice()
        .map(ToString::to_string)
        .delimited_by(just('"'), just('"'));

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
        .or(text::int::<&str, _, _>(10).map(|s| Token::Nat(s.to_string())))
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
    let token = if refine {
        box_parser(token.or(ident.map(|x| Token::Ident(x))))
    } else {
        box_parser(token)
    };

    let span1 = token
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .map_with(|tok, e| (tok, e.span()));
    commented_parser(span1)
}

fn commented_parser<'a>(
    token: impl chumsky::Parser<'a, &'a str, (Token<'a>, SimpleSpan), ParserExtra<'a, char>>,
) -> impl chumsky::Parser<'a, &'a str, Vec<(Token<'a>, SimpleSpan)>, ParserExtra<'a, char>> {
    // Single-line comment
    let comment = just("--")
        .then(any().and_is(newline().or(end()).not()).repeated())
        .padded()
        .ignored()
        .labelled("comment");

    // Recursive block comment parser
    let block_comment = recursive(|block_comment| {
        just("/*")
            .ignore_then(
                none_of("*/")
                    .or(just('*').then_ignore(none_of('/')))
                    .or(just('/').then_ignore(none_of('*')))
                    .or(block_comment.clone().map(|_| ' ')),
            )
            .repeated()
            .then_ignore(just("*/"))
            .padded()
            .ignored()
    })
        .labelled("block_comment");

    // Whitespace
    let whitespace = text::whitespace()
        .at_least(1)
        .ignored()
        .labelled("whitespace");

    // Ignored elements (comments or whitespace)
    let ignored = choice((comment, block_comment, whitespace)).repeated();

    // Full parser
    token
        .padded_by(ignored.clone())
        .repeated()
        .collect()
        .then_ignore(ignored)
        .then_ignore(end().or_not().to(())) // Make the end optional
}

fn create_parser() -> impl chumsky::Parser<'static, &'static str, Vec<&'static str>, ParserExtra<'static, char>> {
    // Single-line comment
    let comment = just("--")
        .then(any().and_is(newline().or(end()).not()).repeated())
        .padded()
        .ignored()
        .labelled("comment");

    // Recursive block comment parser
    let block_comment = recursive(|block_comment| {
        just("/*")
            .ignore_then(
                none_of("*/")
                    .or(just('*').then_ignore(none_of('/')))
                    .or(just('/').then_ignore(none_of('*')))
                    .or(block_comment.clone().map(|_| ' ')),
            )
            .repeated()
            .then_ignore(just("*/"))
            .padded()
            .ignored()
    })
        .labelled("block_comment");

    // Whitespace
    let whitespace = text::whitespace()
        .at_least(1)
        .ignored()
        .labelled("whitespace");

    // Identifier
    let identifier = text::ident().labelled("identifier");

    // Ignored elements (comments or whitespace)
    let ignored = choice((comment, block_comment, whitespace)).repeated();

    // Full parser
    identifier
        .padded_by(ignored.clone())
        .repeated()
        .collect()
        .then_ignore(ignored)
        .then_ignore(end().or_not().to(())) // Make the end optional
}

#[test]
fn test_comments_parsing() {
    let parser = create_parser();

    // Example usage
    let input = "x y -- This is a comment\n z /* This is a \n block comment */ w";
    match parser.parse(input).into_result() {
        Ok(result) => println!("Parsed identifiers: {:?}", result),
        Err(e) => println!("Error: {:?}", e),
    }
}

#[test]
fn test_commented_parser() {
    let p2 = create_parser();
    let parse = |text, expected| {
        println!("Parsing: {:?}", text);
        let res = p2.parse(text);
        let x = res.output().map(|x| x.to_vec());
        let y = res.into_errors();
        println!("{:?}", y);
        assert_eq!(x, expected);
    };

    parse("hello", Some(vec!["hello"]));
    parse("--hello\n", Some(vec![]));
    parse("--hello", Some(vec![]));
    parse("", Some(vec![]));
    parse("--", Some(vec![]));
    // parse("/* /* sad */ */", Some(vec![]));
    parse("hello -- asd", Some(vec!["hello"]));
    parse("hello asd -- ", Some(vec!["hello", "asd"]));
    parse("hello asd -- ", Some(vec!["hello", "asd"]));
}

fn ident_parser<'t, 's: 't>() -> Parser!('t, 's, Ident) {
    select! {
        Token::Ident(ident) = e => Ident::located(ident, e.span())
    }
}

fn universe_parser<'t, 's: 't>() -> Parser!('t, 's, Universe) {
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

fn str_parser<'t, 's: 't>() -> Parser!('t, 's, String) {
    select! {
        Token::Str(s) => s
    }
}

fn nat_parser<'t, 's: 't>() -> Parser!('t, 's, Nat) {
    select! {
        Token::Nat(n) =>
            n.parse::<Nat>()
                .expect("the number is always valid, because we've used `digits`; qed"),
    }
}

fn literal_parser<'t, 's: 't>() -> Parser!('t, 's, Literal) {
    nat_parser()
        .map(Literal::Nat)
        .or(str_parser().map(Literal::Str))
}

fn params<'t, 's: 't, 'p>(
    param_parser: &'p (impl chumsky::Parser<'t, TokenTreeInput<'t, 's>, Vec<Param>, ParserExtra<'t, Token<'s>>>
    + Clone),
) -> Parser!('t, 's, Vec<Param>) {
    param_parser
        .clone()
        .repeated()
        // .to_slice()
        .collect::<Vec<Vec<Param>>>()
        .map(|v| v.into_iter().flatten().collect::<Vec<_>>())
        .labelled("params_parser")
}

fn param<'t, 's: 't>(
    expr: &Parser!('t, 's, Expr),
    prim_expr: &Parser!('t, 's, Expr),
) -> Parser!('t, 's, Vec<Param>) {
    {
        let ident = ident_parser();

        let params = ident
            .clone()
            .repeated()
            .at_least(1)
            .collect::<Vec<_>>()
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
        .labelled("param_parser")
}

/// x1 x2 ... xn : A
fn forall_params<'t, 's: 't>(expr: &Parser!('t, 's, Expr)) -> Parser!('t, 's, Vec1<Param>) {
    {
        ident_parser()
            .clone()
            .repeated()
            .at_least(1)
            .collect::<Vec<_>>()
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
        .labelled("forall params")
}

fn case<'t, 's: 't>(
    expr: &Parser!('t, 's, Expr),
    pattern: &(Parser!('t, 's, Pat)),
) -> Parser!('t, 's, Case) {
    just(Token::Pipe)
        .ignore_then(pattern.clone().separated_by(just(Token::Comma)).collect())
        .then(
            just(Token::DArrow)
                .ignore_then(expr.clone())
                .or_not()
                .labelled("=> ..."),
        )
        .map(|(pats, body)| Case::new(pats, body))
        .labelled("case")
}

fn pattern<'t, 'p, 's: 't>(
    prim_expr: &'p (impl chumsky::Parser<'t, TokenTreeInput<'t, 's>, Expr, ParserExtra<'t, Token<'s>>>
    + Clone
    + 't),
) -> Parser!('t, 's, Pat: Clone + 't) {
    fn pat_rest<'t, 'p, 's: 't>(
        prim_expr: &'p (impl chumsky::Parser<'t, TokenTreeInput<'t, 's>, Expr, ParserExtra<'t, Token<'s>>>
        + Clone
        + 't),
        rec_pattern: &'p (impl chumsky::Parser<'t, TokenTreeInput<'t, 's>, Pat, ParserExtra<'t, Token<'s>>>
        + Clone
        + 't),
    ) -> Parser!('t, 's, Pat: Clone + 't) {
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
    let sub_pat = recursive(|prim_pattern: Recursive<Direct<_, Pat, _>>| {
        var_pat
            .clone()
            .or(pat_cons_start
                .clone()
                .then(prim_pattern.clone().repeated().at_least(1).collect())
                .map(|((dot, con), args)| Pat::cons_surf(dot.is_some(), con, args)))
            .or(pat_rest(prim_expr, &prim_pattern))
    });
    recursive(|top_pat| {
        pat_cons_start
            .then(sub_pat.clone().repeated().at_least(1).collect())
            .map(|((dot, con), args)| Pat::cons_surf(dot.is_some(), con, args))
            .or(var_pat)
            .or(pat_rest(prim_expr, &top_pat))
    })
        .labelled("pattern")
}

fn meta_attr<'t, 's: 't>() -> Parser!('t, 's, MetaAttr) {
    let prim_meta_attr = recursive(|prim_meta_attr: Recursive<Direct<_, MetaAttr, _>>| {
        let ident = ident_parser();
        let meta_field = ident
            .clone()
            .then_ignore(just(Token::Assignment))
            .then(str_parser())
            .map(|(name, value)| (name, value));

        let meta_attr_app = ident
            .clone()
            .then(prim_meta_attr.clone().repeated().collect::<Vec<_>>())
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
                .collect::<Vec<_>>()
                .map(|fields| MetaAttr::Struct(Vec1::try_from_vec(fields).unwrap())))
            .or(ident.map(MetaAttr::Ident))
    });

    just(Token::Hash)
        .ignore_then(just(Token::LParen))
        .ignore_then(prim_meta_attr)
        .then_ignore(just(Token::RParen))
}

pub fn cons<'t, 's: 't>(
    params: &(Parser!('t, 's, Vec<Param>)),
) -> impl chumsky::Parser<'t, TokenTreeInput<'t, 's>, NamedTele, ParserExtra<'t, Token<'s>>> {
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
    use chumsky::error::Error;
    use crate::syntax::parser::{ParseError, Parser};
    use crate::syntax::surf::Expr::{self};
    use crate::syntax::{Ident, Loc};
    use crate::syntax::token::Token;

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

        // TODO: errors are not very helpful anymore. Refactor the parser
        // assert_eq!(
        //     parser.parse_expr("(T U : A) -> X : A -> T").unwrap_err(),
        //     <ParseError<_> as Error<&[Token<'static>]>>::expected_found(
        //         vec![None, Some(Token::LParen.into()), Some(Token::RArrow.into())],
        //         Some(Token::Colon.into()),
        //         Loc::new(17, 19).into(),
        //     ).map_token(|t| t.to_string())
        // );
        //
        // assert_eq!(
        //     parser.parse_expr("T U : A -> T").unwrap_err(),
        //     <ParseError<_> as Error<&[Token<'static>]>>::expected_found(
        //         vec![Some(Token::LParen.into()), None],
        //         Some(Token::Colon.into()),
        //         Loc::new(4, 5).into(),
        //     ).map_token(|t| t.to_string())
        // );
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
