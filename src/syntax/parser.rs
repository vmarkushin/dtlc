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
use dyn_clone::DynClone;
use itertools::{Either, Itertools};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Formatter;
use std::fmt::{Debug, Display};
use std::fs;
use std::iter::once;
use std::path::PathBuf;
use std::str::FromStr;
use vec1::Vec1;

pub type ParseError<'a> = Simple<Token<'a>, Loc>;
const UNIT: &() = &();

macro_rules! Parser {
    ($O:path) => { impl chumsky::Parser<Token<'static>, $O, Error = ParseError<'static>> + Clone + 'static };
    ($O:path: $($bounds:tt)*) => { impl chumsky::Parser<Token<'static>, $O, Error = ParseError<'static>> + $($bounds)* };
    ($I:path, $O:path) => { impl chumsky::Parser<$I, $O, Error = Simple<$I, Loc>> };
}

trait ParserExt<I: Clone, O, E>: chumsky::Parser<I, O, Error = E> + DynClone + 'static {}

dyn_clone::clone_trait_object!(<I: Clone, O, E> ParserExt<I, O, E>);

impl<T, I: Clone, O, E> ParserExt<I, O, E> for T where
    T: chumsky::Parser<I, O, Error = E> + DynClone + 'static
{
}

type BoxedParser<I, O, E = ParseError<'static>> = Box<dyn chumsky::Parser<I, O, Error = E>>;
type BoxedParserCloned<I, O, E = ParseError<'static>> = Box<dyn ParserExt<I, O, E>>;

#[inline]
fn box_parser<I: Clone, O, E>(
    p: impl chumsky::Parser<I, O, Error = E> + 'static,
) -> BoxedParser<I, O, E> {
    Box::new(p)
}

#[inline]
fn box_parser_cloned<I: Clone, O, E>(
    p: impl ParserExt<I, O, E> + 'static,
) -> BoxedParserCloned<I, O, E> {
    Box::new(p)
}

fn err_to_static<'a>(e: ParseError<'a>) -> ParseError<'static> {
    e.map(|x| match x {
        Token::__Unused(_) => Token::__Unused(UNIT),
        Token::Universe(x) => Token::Universe(x),
        Token::Pi => Token::Pi,
        Token::Ident(x) => Token::Ident(x),
        Token::IdentOp(x) => Token::IdentOp(x),
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

fn fail<I: Clone + PartialEq + 'static, O, E: chumsky::Error<I> + 'static>(
) -> impl chumsky::Parser<I, O, Error = E> + Clone + 'static {
    one_of(vec![]).map(|_| unreachable!())
}

#[derive(Debug)]
struct OperatorsAndFunctions(Operators, Vec<Ident>);

impl Display for OperatorsAndFunctions {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ops = self.0 .0.iter().collect::<Vec<_>>();
        ops.sort_by(|(a, _), (b, _)| a.cmp(b));
        let mut ops = ops
            .into_iter()
            .map(|(a, b)| format!("{} ({})", a, b))
            .join(", ");
        if !ops.is_empty() {
            ops = format!("operators: {}", ops);
        }
        let mut fns = self.1.iter().map(|x| x.to_string()).join(", ");
        if !fns.is_empty() {
            fns = format!("functions: {}", fns);
        }
        if ops.is_empty() {
            write!(f, "{}", fns)
        } else if fns.is_empty() {
            write!(f, "{}", ops)
        } else {
            write!(f, "{}, {}", ops, fns)
        }
    }
}

pub struct Parser {
    file: SimpleFile<String, String>,
    scope: Vec<Ident>,
    should_refine: bool,
    operators: Operators,
    debug: bool,
}

impl Parser {
    pub fn debug(&mut self, flag: bool) {
        self.debug = flag;
    }

    fn parse_using<'inp, T: Display + Debug>(
        &self,
        parser: Parser!(T:),
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
        let mut additional_tokens = self
            .scope
            .iter()
            .map(|id| id.text.clone())
            .collect::<HashSet<_>>()
            .into_iter()
            .map(|t| (t, false))
            .collect::<Vec<_>>();
        let op_tokens = self
            .operators
            .0
            .iter()
            .flat_map(|(name, f)| {
                f.patterns
                    .0
                    .iter()
                    .filter_map(|p| match p {
                        OperatorPattern::Tok(s) => Some((s.clone(), true)),
                        OperatorPattern::Expr => None,
                    })
                    .chain(once((name.text.clone(), false)))
            })
            .collect::<Vec<_>>();
        additional_tokens.extend(op_tokens);

        debug!(target: "parser", "parsing using operators: {}", self.operators);
        let (tokens, les) = lexer(additional_tokens, lexer_ignore_idents).parse_recovery(stream);
        let mut out = None;
        let mut err = None;
        let es = if let Some(tokens) = tokens {
            let tokens_formatted = tokens
                .iter()
                .map(|(t, _)| {
                    let mut delim = "";
                    if matches!(t, Token::Fn | Token::Data | Token::Hash) {
                        delim = "\n";
                    }
                    format!("{delim}{t:?}")
                })
                .join(" ");
            debug!(target: "parser", "tokens: {}", tokens_formatted);

            let f = if self.debug {
                chumsky::Parser::parse_recovery_verbose
            } else {
                chumsky::Parser::parse_recovery
            };
            let (e, es) = f(
                &parser.then_ignore(end()),
                Stream::from_iter(Loc::new(len, len + 1), tokens.into_iter()),
            );
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
        let OperatorsAndFunctions(ops, _funcs) =
            self.parse_using(self.operators_parser(), input, false)?;
        self.operators.0.extend(ops.0);
        let mut decl = self.parse_using(self.decl(), input, false)?;
        if self.should_refine {
            let ident = decl.name();
            self.scope.push(ident.clone());
            self.refine_decl(&mut decl)?;
        }
        Ok(decl)
    }

    pub fn parse_prog<'inp>(&mut self, input: &'inp str) -> Result<Prog, ParseError<'inp>> {
        debug!(target: "parser", "Parsing operators...");
        let OperatorsAndFunctions(ops, _funcs) =
            self.parse_using(self.operators_parser(), input, false)?;
        self.operators.0.extend(ops.0);
        debug!(target: "parser", "Parsing prog...");
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
            should_refine: false,
            operators: Operators(Default::default()),
            debug: false,
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

            let mut operators = self.operators.0.iter().collect::<Vec<_>>();
            operators.sort_by(|(_n1, f1), (_n2, f2)| {
                let prec_ord = f1.precedence.cmp(&f2.precedence).reverse();
                let kind_ord = || f1.fixity().cmp(&f2.fixity());
                let pattern_ord = || f1.patterns.cmp(&f2.patterns);
                let assoc_ord = || f1.associativity.cmp(&f2.associativity);

                prec_ord
                    .then_with(kind_ord)
                    .then_with(pattern_ord)
                    .then_with(assoc_ord)
            });
            let operators: Vec<_> = operators
                .into_iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();

            let prim_expr_cl = prim_expr.clone();
            let app = prim_expr
                .clone()
                .then_with(move |f| {
                    let args = prim_expr_cl.clone().repeated().map(move |args| {
                        if args.is_empty() {
                            f.clone()
                        } else {
                            Expr::App(Box::new(f.clone()), Vec1::try_from_vec(args).unwrap())
                        }
                    });

                    box_parser(args)
                })
                .debug("app");

            // a parser with the next higher precedence level
            let mut tighter_parser: Option<BoxedParserCloned<_, Expr, _>> =
                Some(box_parser_cloned(app.clone()));

            let leveled_operators = operators.into_iter().group_by(|(_ident, op)| op.precedence);
            for (_, op_lvl) in &leveled_operators {
                let group = op_lvl.collect::<Vec<_>>();
                let fixity_operators = group.into_iter().group_by(|(_ident, op)| op.fixity());
                let mut fixity_to_operator = fixity_operators
                    .into_iter()
                    .map(|(kind, g)| (kind, g.collect::<Vec<_>>()))
                    .collect::<HashMap<_, _>>();

                let next_parser = tighter_parser.take().unwrap();

                let make_kind_op_parser = |ops: Vec<(Ident, Operator)>| {
                    ops.into_iter()
                        .fold(box_parser_cloned(fail()), |acc, (f, op)| {
                            let (p, _) = op.to_parser(&expr, &prim_expr, &next_parser);
                            box_parser_cloned(acc.or(p.map(move |x| (f.clone(), x))))
                        })
                };

                let closed_ops = fixity_to_operator
                    .remove(&Fixity::Closed)
                    .unwrap_or_default();
                let prefix_ops = fixity_to_operator
                    .remove(&Fixity::Prefix)
                    .unwrap_or_default();
                let postfix_ops = fixity_to_operator
                    .remove(&Fixity::Postfix)
                    .unwrap_or_default();
                let infix_ops = fixity_to_operator
                    .remove(&Fixity::Infix)
                    .unwrap_or_default();

                let lvl_op_sig = closed_ops
                    .iter()
                    .chain(postfix_ops.iter())
                    .chain(prefix_ops.iter())
                    .chain(infix_ops.iter())
                    .map(|(ident, _)| ident.text.clone())
                    .fold(String::new(), |acc, s| {
                        if acc.is_empty() {
                            s
                        } else {
                            format!("{} | {}", acc, s)
                        }
                    });

                let closed_ops_parser = make_kind_op_parser(closed_ops);
                let prefix_ops_parser = make_kind_op_parser(prefix_ops);
                let postfix_ops_parser = make_kind_op_parser(postfix_ops);
                let infix_ops_parser = make_kind_op_parser(infix_ops);

                // lvl_op = closed | prefix* next (infix | postfix)*

                // TODO: parse open and open left separately?
                let infix_or_postfix = infix_ops_parser
                    .labelled("open_ops_parser")
                    .or(postfix_ops_parser.labelled("open_left_ops_parser"));
                let infix = prefix_ops_parser
                    .debug("open_right")
                    .clone()
                    .repeated()
                    .then(
                        next_parser.clone().then(
                            infix_or_postfix
                                .clone()
                                .debug("open_left")
                                .repeated()
                                .labelled("open_rpt"),
                        ),
                    )
                    .debug("open");

                let lvl_op_parser = closed_ops_parser
                    .labelled("closed_ops_parser")
                    .debug("closed")
                    .map(|(f, (es, _, _))| {
                        if es.is_empty() {
                            Expr::Var(f)
                        } else {
                            Expr::App(Expr::Var(f).boxed(), Vec1::try_from_vec(es).unwrap())
                        }
                    })
                    .or(infix.map(|(prefs, (e, postfs))| {
                        // ! if C then A else * x => !_ (if_then_else_ C A (*_ x))
                        let e = prefs.into_iter().rev().fold(e, |e, (f, (mut es, _, _))| {
                            es.push(e);
                            Expr::App(Expr::Var(f).boxed(), Vec1::try_from_vec(es).unwrap())
                        });

                        if postfs.is_empty() {
                            return e;
                        }
                        let assoc = postfs.get(0).expect("one of the arrays is no-empty").1 .1;
                        if assoc == Associativity::None {
                            if postfs.len() > 2 {
                                panic!("ambiguous associativity");
                            }
                        }

                        // x + y ! + z      =  x [+ y] [!] [+ z]  =  (x + y) + z            =>  _+_ (_+_ x y) z
                        // x + y + z        =  x [+ y] [+ z]      =  (x + y) + z            =>  _+_ (_+_ x y) z
                        // x ^ y ^ z        =  x [^ y] [^ z]      =  x ^ (y ^ z)            =>  _^_ x (_^_ y z)
                        // e + x / y + z !  =                     =  (e + (x / y)) + (z !)  =>  _+_ (_+_ e (_/_ x y)) (_! z)

                        match assoc {
                            // TODO: handle Associativity::None case?
                            Associativity::Left | Associativity::None => {
                                postfs.into_iter().fold(e, |e, (f, (mut es, _, _))| {
                                    es.insert(0, e);
                                    Expr::App(Expr::Var(f).boxed(), Vec1::try_from_vec(es).unwrap())
                                })
                            }
                            Associativity::Right => {
                                fn go(
                                    e: Expr,
                                    mut postfs: Vec<(Ident, OpParserWithAssoc)>,
                                ) -> Expr {
                                    let (f, (mut es, _, _)) = postfs.remove(0);
                                    let mut args = Vec1::new(e);
                                    if !es.is_empty() {
                                        let mut e = es.remove(0);
                                        if !postfs.is_empty() {
                                            e = go(e, postfs);
                                        }
                                        args.push(e);
                                    }
                                    Expr::App(Expr::Var(f).boxed(), args)
                                }
                                go(e, postfs)
                            }
                        }
                    }))
                    .debug(lvl_op_sig);

                tighter_parser = Some(box_parser_cloned(lvl_op_parser));
            }
            let op_parser = tighter_parser.take().unwrap();

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

            lam.map(|(ps, body)| Expr::Lam(ps, body.boxed()))
                .or(mat
                    .map(|(exprs, cases)| Expr::Match(Vec1::try_from_vec(exprs).unwrap(), cases)))
                .or(pi.map(|(ps, ret)| {
                    let ps = ps.into_iter().flatten().collect::<Vec<_>>();
                    Expr::Pi(Vec1::try_from_vec(ps).unwrap(), ret.boxed())
                }))
                .or(op_parser)
        })
        .debug("expr")
    }

    pub fn decl(&self) -> Parser!(Decl:) {
        let expr = self.expr();
        let prim_expr = prim_expr(&expr);
        let param_parser = param(&expr, &prim_expr);
        let params = params(&param_parser);
        let ident = ident_parser().or(ident_op_parser());

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

    pub fn prog(&self) -> Parser!(Prog:) {
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

    fn operators_parser(&self) -> Parser!(OperatorsAndFunctions) {
        fn parse_op_attr(
            meta_attrs: &[MetaAttr],
        ) -> (bool, Option<Associativity>, Option<Precedence>) {
            let mut assoc = None;
            let mut prec = None;
            let mut has_attr = false;

            for attr in meta_attrs {
                match attr {
                    MetaAttr::Ident(ident) if &ident.text == "operator" => {
                        has_attr = true;
                    }
                    MetaAttr::App(f, args) if &**f == "operator" => {
                        has_attr = true;
                        for arg in args {
                            match arg {
                                MetaAttr::Struct(fields) => {
                                    for (key, val) in fields {
                                        match &***key {
                                            "associativity" => {
                                                assert!(assoc.is_none(), "assoc already set");
                                                assoc = Some(match &**val {
                                                    "left" => Associativity::Left,
                                                    "right" => Associativity::Right,
                                                    "none" => Associativity::None,
                                                    _ => panic!("Invalid associativity"),
                                                });
                                            }
                                            "precedence" => {
                                                assert!(prec.is_none(), "prec already set");
                                                prec = Some(val.parse().unwrap());
                                            }
                                            _ => panic!("Invalid operator attribute"),
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }
            }
            (has_attr, assoc, prec)
        }
        let expr = self.expr();
        let prim_expr = prim_expr(&expr);
        let param_parser = param(&expr, &prim_expr);
        let params = params(&param_parser);
        let ident = ident_parser().or(ident_op_parser());

        let meta_attrs = meta_attr().repeated();
        let skip = take_until(
            just(Token::Hash)
                .or(just(Token::Fn))
                .rewind()
                .ignored()
                .to(false)
                .or(end().to(true)),
        );
        let func = meta_attrs
            .clone()
            .then_ignore(just(Token::Fn))
            .then(
                ident
                    .clone()
                    .map_with_span(|name, span| (name, span))
                    .labelled("function name"),
            )
            .then(params.clone())
            .map(|((attrs, (name, name_span)), params)| {
                let params_num = params.len();
                let (is_op, assoc, prec) = parse_op_attr(&attrs);
                debug!(target: "parser", "operator properties: {} {:?} {:?}", name, assoc, prec);
                let def = is_op
                    .then(|| {
                        Operator::from_ident(
                            assoc.unwrap_or(Associativity::None),
                            prec.unwrap_or(10),
                            &name,
                            params_num,
                        )
                    })
                    .flatten();
                (name, name_span, def)
            })
            .then_ignore(skip.clone())
            .labelled("function");
        let data = meta_attrs
            .clone()
            .then_ignore(just(Token::Data))
            .then(
                ident
                    .map_with_span(|name, span| (name, span))
                    .labelled("data name"),
            )
            .then(params)
            .map(|((_attrs, (name, name_span)), _params)| (name, name_span, None))
            .then_ignore(skip.clone())
            .labelled("data");

        skip.then_with(move |(_, ended)| {
            if ended {
                box_parser(
                    end().map(|_| OperatorsAndFunctions(Operators(Default::default()), Vec::new())),
                )
            } else {
                box_parser(func.clone().or(data.clone()).repeated().try_map(|fs, _| {
                    let mut operators = HashMap::new();
                    let mut basic_funcs = Vec::new();
                    for (name, name_span, f) in fs {
                        let Some(f) = f else {
                            debug!(target: "parser", "skipped operator: {}", name);
                            basic_funcs.push(name);
                            continue;
                        };
                        if operators.insert(name.clone(), f).is_some() {
                            return Err(Simple::custom(
                                name_span.clone(),
                                format!("Function '{}' already exists", name),
                            ));
                        }
                    }
                    Ok(OperatorsAndFunctions(Operators(operators), basic_funcs))
                }))
            }
        })
        .then_ignore(end())
    }
}

fn prim_expr(expr: &Parser!(Expr)) -> Parser!(Expr) {
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
    mut additional_tokens: Vec<(String, bool)>,
    refine: bool,
) -> Parser!(char, Vec<(Token<'static>, Loc)>) {
    additional_tokens.sort_by(|(a, _), (b, _)| b.len().cmp(&a.len()));
    debug!(target: "parser", "additional tokens {additional_tokens:?}, refining: {refine}");
    let ident = filter(|c| is_ident_char(*c))
        .repeated()
        .at_least(1)
        .collect::<String>();
    let ident_op = filter(|c| is_ident_op_char(*c))
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
        .or(just("@").to(Token::At))
        .or(just("#").to(Token::Hash))
        .or(just(":=").to(Token::Assignment))
        .or(just(":").to(Token::Colon))
        .or(just(",").to(Token::Comma))
        .or(just(".").to(Token::Dot))
        .or(just("=>").to(Token::DArrow))
        .or(just("->").to(Token::RArrow))
        .or(just("?").to(Token::Question))
        .or(just("{").to(Token::LBrace))
        .or(just("}").to(Token::RBrace))
        .or(just("[").to(Token::LBracket))
        .or(just("]").to(Token::RBracket))
        .or(braces);

    let token = if additional_tokens.is_empty() {
        box_parser(base_token)
    } else {
        let init = fail();
        let add_tokens_ref = additional_tokens
            .into_iter()
            .map(|(s, is_op)| {
                just(s).map(move |s| {
                    if is_op {
                        Token::IdentOp(s)
                    } else {
                        Token::Ident(s)
                    }
                })
            })
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
    let maybe_not_quite_ident = |s: String| {
        let tok = match s.as_str() {
            "_" => Token::Underscore,
            "|" => Token::Pipe,
            "!" => Token::Bang,
            "lam" => Token::Lam,
            "fn" => Token::Fn,
            "let" => Token::Let,
            "forall" => Token::Pi,
            "data" => Token::Data,
            "codata" => Token::Codata,
            "match" => Token::Match,
            _ => {
                if s.chars().all(char::is_numeric) {
                    Token::Nat(s)
                } else {
                    return Either::Right(s);
                }
            }
        };
        Either::Left(tok)
    };
    let ident_mapped = ident_op
        .map(move |s| maybe_not_quite_ident(s).left_or_else(|s| Token::IdentOp(s)))
        .or(ident.map(move |s| maybe_not_quite_ident(s).left_or_else(|s| Token::Ident(s))));
    let token = if !refine {
        box_parser(token.or(ident_mapped.clone()))
    } else {
        box_parser(token)
    };
    let token = token
        .or(text::digits(10).map(|s| Token::Nat(s)))
        .or(just("|").to(Token::Pipe))
        .or(just("!").to(Token::Bang))
        .or(just("_").to(Token::Underscore));
    let token = if refine {
        box_parser(token.or(ident_mapped))
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

fn ident_op_parser() -> Parser!(Ident) {
    select! {
        Token::IdentOp(ident), loc => Ident::located(ident, loc)
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

fn params(param_parser: &Parser!(Vec<Param>)) -> Parser!(Vec<Param>) {
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
                .map(|ident| Param::new(ident, ty.clone(), plicit))
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

fn case(expr: &Parser!(Expr), pattern: &Parser!(Pat)) -> Parser!(Case) {
    just(Token::Pipe)
        .ignore_then(pattern.clone().separated_by(just(Token::Comma)))
        .then(
            just(Token::DArrow)
                .ignore_then(expr.clone())
                .or_not()
                .debug("=> <expr>?"),
        )
        .map(|(pats, body)| Case::new(pats, body))
        .debug("case")
}

fn pattern(prim_expr: &Parser!(Expr)) -> Parser!(Pat) {
    fn pat_rest(
        prim_expr: &Parser!(Expr),
        rec_pattern: &Parser!(Pat),
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
        let ident = ident_parser().debug("meta_ident");
        let meta_field = ident
            .clone()
            .then_ignore(just(Token::Assignment))
            .then(str_parser())
            .map(|(name, value)| (name, value))
            .debug("meta_field");

        let meta_attr_app = ident
            .clone()
            .then(prim_meta_attr.clone().repeated())
            .map(|(f, args)| {
                if args.is_empty() {
                    MetaAttr::Ident(f)
                } else {
                    MetaAttr::App(f, Vec1::try_from_vec(args).unwrap())
                }
            })
            .debug("meta_attr_app");

        meta_field
            .clone()
            .separated_by(just(Token::Comma))
            .at_least(1)
            .map(|fields| MetaAttr::Struct(Vec1::try_from_vec(fields).unwrap()))
            .or(meta_field
                .clone()
                .map(|field| MetaAttr::Struct(Vec1::new(field))))
            .or(meta_attr_app.clone())
            .debug("prim_meta_attr")
    });

    just(Token::Hash)
        .ignore_then(just(Token::LParen))
        .ignore_then(prim_meta_attr)
        .then_ignore(just(Token::RParen))
}

pub fn cons(params: &Parser!(Vec<Param>)) -> Parser!(NamedTele:) {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Ord)]
enum Associativity {
    Left,
    Right,
    None,
}

impl Display for Associativity {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Associativity::Left => write!(f, "left"),
            Associativity::Right => write!(f, "right"),
            Associativity::None => write!(f, "none"),
        }
    }
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
    pub(crate) fn as_token(&self) -> String {
        match self {
            OperatorPattern::Tok(s) => s.clone(),
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

    pub fn is_token(&self) -> bool {
        match self {
            OperatorPattern::Tok(_) => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct OperatorPatterns(Vec<OperatorPattern>);

impl Display for OperatorPatterns {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.iter().join(" "))
    }
}

impl OperatorPatterns {
    pub fn fixity(&self) -> Fixity {
        let is_first_expr = self.0.first().unwrap().is_expr();
        let is_last_expr = self.0.last().unwrap().is_expr();
        match (is_first_expr, is_last_expr) {
            (false, false) => Fixity::Closed,
            (true, true) => Fixity::Infix,
            (true, false) => Fixity::Postfix,
            (false, true) => Fixity::Prefix,
        }
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
        self.0.len().cmp(&other.0.len()).reverse().then_with(|| {
            let is_expr_self = self.0[0].is_expr();
            let is_expr_other = other.0[0].is_expr();
            match (is_expr_self, is_expr_other) {
                (true, false) => Ordering::Greater,
                (false, true) => Ordering::Less,
                _ => Ordering::Equal,
            }
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Operator {
    associativity: Associativity,
    precedence: Precedence,
    fixity: Fixity,
    patterns: OperatorPatterns,
}

impl Display for Operator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} {}",
            self.associativity, self.precedence, self.patterns
        )
    }
}

#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
enum Fixity {
    Closed,
    Infix,
    Postfix,
    Prefix,
}

impl Ord for Fixity {
    fn cmp(&self, other: &Self) -> Ordering {
        use Fixity::*;
        match (self, other) {
            (Closed, Prefix) => Ordering::Less,
            (Prefix, Closed) => Ordering::Greater,
            (Prefix, _) => Ordering::Less,
            (Infix, Postfix) => Ordering::Less,
            (Postfix, Infix) => Ordering::Greater,
            (Infix, _) => Ordering::Greater,
            (Postfix, _) => Ordering::Greater,
            (Closed, Closed) => Ordering::Equal,
            (Closed, Infix) => Ordering::Less,
            (Closed, Postfix) => Ordering::Less,
        }
    }
}

impl PartialOrd<Self> for Fixity {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

type OpParserWithAssoc = (Vec<Expr>, Associativity, Fixity);
static mut N: usize = 0;

fn is_ident_char(c: char) -> bool {
    char::is_alphanumeric(c) || c == '_' || c == '\''
}

fn is_ident_op_char(c: char) -> bool {
    c == '_' || (!is_ident_char(c) && !FORBIDDEN.contains(c))
}

impl Operator {
    fn fixity(&self) -> Fixity {
        self.fixity
    }

    pub fn first_token(&self) -> String {
        self.patterns
            .0
            .iter()
            .find(|p| p.is_token())
            .unwrap()
            .as_token()
    }

    fn to_parser(
        &self,
        expr: &Parser!(Expr),
        _prim_expr: &Parser!(Expr),
        higher_parser: &Parser!(Expr),
    ) -> (Parser!(OpParserWithAssoc), Fixity) {
        let kind = self.fixity();

        let pats = match kind {
            Fixity::Closed => &self.patterns.0[..],
            Fixity::Postfix | Fixity::Infix => &self.patterns.0[1..],
            Fixity::Prefix => {
                let l = self.patterns.0.len();
                &self.patterns.0[..l - 1]
            }
        };

        let mut lp = None;
        let pat_len = pats.len();
        for (i, pat) in pats.into_iter().enumerate() {
            match pat {
                OperatorPattern::Tok(tok) => {
                    let p = just(Token::IdentOp(tok.clone()))
                        .ignored()
                        .map(|_| Vec::new());
                    if lp.is_none() {
                        lp = Some(box_parser_cloned(p));
                    } else {
                        lp = Some(box_parser_cloned(lp.take().unwrap().then_ignore(p)));
                    }
                }
                OperatorPattern::Expr => {
                    let p = {
                        if i == 0 || i == pat_len - 1 {
                            box_parser_cloned(dyn_clone::clone(higher_parser))
                        } else {
                            box_parser_cloned(dyn_clone::clone(expr))
                        }
                    }
                    .map(|e| vec![e]);
                    if lp.is_none() {
                        lp = Some(box_parser_cloned(p));
                    } else {
                        lp = Some(box_parser_cloned(lp.take().unwrap().then(p).map(
                            |(a, b)| {
                                let mut a = a;
                                a.extend(b);
                                a
                            },
                        )));
                    }
                }
            }
        }

        let associativity = self.associativity;
        let lp = lp.unwrap().map(move |e| (e, associativity, kind));
        (lp, kind)
    }

    fn from_ident(
        associativity: Associativity,
        precedence: Precedence,
        ident: &str,
        params_num: usize,
    ) -> Option<Self> {
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
        let pats_len = patterns.len();
        if pats_len < 2 {
            return None;
        }
        if expr_num > params_num {
            panic!("Too many underscores in {}", ident);
        }
        Some(Self::new(associativity, precedence, patterns))
    }

    fn new(
        associativity: Associativity,
        precedence: Precedence,
        patterns: Vec<OperatorPattern>,
    ) -> Self {
        let patterns = OperatorPatterns::new(patterns);
        let fixity = patterns.fixity();
        match associativity {
            Associativity::Left | Associativity::Right => {
                assert_eq!(fixity, Fixity::Infix);
            }
            Associativity::None => {}
        }
        Self {
            associativity,
            precedence,
            patterns,
            fixity,
        }
    }
}

#[derive(Debug)]
struct Operators(HashMap<Ident, Operator>);

impl Display for Operators {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (ident, op) in self.0.iter() {
            writeln!(f, "{}: {:?}", ident, op)?;
        }
        Ok(())
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
    fn parse_operators() {
        let _ = env_logger::try_init();

        let mut parser = Parser::default();

        let prog = r#"
        #(operator precedence := "25")
        fn _++ (a : Nat) : Nat := ?unimplemented

        #(operator precedence := "15" associativity := "left")
        fn _+_ (a b : Nat) : Nat := ?unimplemented

        #(operator precedence := "20" associativity := "left")
        fn _*_ (a b : Nat) : Nat := ?unimplemented

        #(operator precedence := "25" associativity := "right")
        fn _^_ (a b : Nat) : Nat := ?unimplemented

        #(operator precedence := "0" associativity := "right")
        fn _$_ (f : A -> B) (a : A) : B := ?unimplemented

        #(operator precedence := "25")
        fn !!_ (a : Bool) : Bool := ?unimplemented

        #(operator)
        fn if_then_else_ (cond : Bool) (a b : Unit) : Unit := ?unimplemented

        #(operator)
        fn _？_：_ (cond : Bool) (a b : Unit) : Unit := ?unimplemented

        #(operator)
        fn ||_|| (a : Int) : Nat := ?unimplemented
        "#;
        parser.should_refine = false;
        let prog = parser.parse_prog(prog).unwrap();
        /*
        _++ | _^_ | !_
        _*_
        _+_
        if_then_else_

        atom := ident | literal | "(" expr ")"
        pp := atom (++)*
        not := (!)* pp
        pow := not (^ not)*
        pow' := (not ^)* not
        prod = pp (* pp)*
        plus := prod (+ prod)*
        ite := if plus then plus else plus | plus
        expr := ite

        _++ | _^_
        _*_
        _+_
        if_then_else_
        !_

        atom := ident | literal | "(" expr ")"
        pp := atom (++)*
        pow := atom (^ atom)*
        pp_or_pow := pp | pow
        prod := pp_or_pow (* pp_or_pow)*
        plus := prod (+ prod)*
        ite := (if plus then plus else)* plus
        not := (!)* plus
        not_or_ite := ite | not
        expr := not_or_ite

        ! 2 * 2 => Not (Mul ( 2, 2) )

        !_ | _++ | _^_
        _*_
        _+_
        if_then_else_
        |_|

        atom := ident | literal | "(" expr ")"
        app := atom (atom)*
        not := (!)* atom | atom
        pp_or_pow := not (++ | ^ not)* | not
        prod := pp_or_pow (* pp_or_pow)* | pp_or_pow
        plus := prod (+ prod)* | prod
        ite := (if plus then plus else)* plus | "|" plus "|" | plus
        expr := ite

        ! 2 * (|-1|) ^ if T then X else Y

        (! 2) * (|-1| ^ (if T then X else Y))

        ! Y ^ Z


        atom := ident | literal | "(" expr ")"
        app := atom (atom)*
        not := ! expr | atom
        pp_or_pow := not (++ | ^ expr)* | not
        prod := pp_or_pow (* expr)* | pp_or_pow
        plus := prod (+ expr)* | prod
        ite := if expr then expr else expr | "|" expr "|" | plus
        expr := ite

        ! if if T then A else B then X else Y

        ! ! x
         */
        println!("{:?}", prog);

        // postfix
        assert_eq!(
            parser.parse_expr("n++").unwrap(),
            Expr::app_many(Expr::var("_++"), vec![Expr::var("n")],)
        );

        // postfix multi
        assert_eq!(
            parser.parse_expr("n++++").unwrap(),
            Expr::app_many(
                Expr::var("_++"),
                vec![Expr::app_many(Expr::var("_++"), vec![Expr::var("n")],),]
            )
        );

        // infix
        assert_eq!(
            parser.parse_expr("n+m").unwrap(),
            Expr::app_many(Expr::var("_+_"), vec![Expr::var("n"), Expr::var("m")],)
        );

        // fully-qualified operator as function
        assert_eq!(
            parser.parse_expr("_+_ n m").unwrap(),
            Expr::app_many(Expr::var("_+_"), vec![Expr::var("n"), Expr::var("m")],)
        );

        // infix multi
        assert_eq!(
            parser.parse_expr("n+m+k").unwrap(),
            Expr::app_many(
                Expr::var("_+_"),
                vec![
                    Expr::app_many(Expr::var("_+_"), vec![Expr::var("n"), Expr::var("m")],),
                    Expr::var("k")
                ]
            )
        );

        // infix lowest precedence
        assert_eq!(
            parser.parse_expr("n + m $ j * k").unwrap(),
            Expr::app_many(
                Expr::var("_$_"),
                vec![
                    Expr::app_many(Expr::var("_+_"), vec![Expr::var("n"), Expr::var("m")],),
                    Expr::app_many(Expr::var("_*_"), vec![Expr::var("j"), Expr::var("k")],),
                ]
            )
        );

        // prefix
        assert_eq!(
            parser.parse_expr("!!x").unwrap(),
            Expr::app_many(Expr::var("!!_"), vec![Expr::var("x")],)
        );

        // prefix multi
        assert_eq!(
            parser.parse_expr("!!!!x").unwrap(),
            Expr::app_many(
                Expr::var("!!_"),
                vec![Expr::app_many(Expr::var("!!_"), vec![Expr::var("x")])]
            )
        );

        // no-fix
        assert_eq!(
            parser.parse_expr("if x then y else z").unwrap(),
            Expr::app_many(
                Expr::var("if_then_else_"),
                vec![Expr::var("x"), Expr::var("y"), Expr::var("z")]
            )
        );

        // no-fix multi
        assert_eq!(
            parser
                .parse_expr("if if a then if b then c else d else e then f else g")
                .unwrap(),
            Expr::app_many(
                Expr::var("if_then_else_"),
                vec![
                    Expr::app_many(
                        Expr::var("if_then_else_"),
                        vec![
                            Expr::var("a"),
                            Expr::app_many(
                                Expr::var("if_then_else_"),
                                vec![Expr::var("b"), Expr::var("c"), Expr::var("d")]
                            ),
                            Expr::var("e"),
                        ]
                    ),
                    Expr::var("f"),
                    Expr::var("g"),
                ]
            )
        );

        // no-fix
        assert_eq!(
            parser.parse_expr("x ？y ：z").unwrap(),
            Expr::app_many(
                Expr::var("_？_：_"),
                vec![Expr::var("x"), Expr::var("y"), Expr::var("z")]
            )
        );

        // no-fix multi
        assert_eq!(
            parser.parse_expr("a ？b ？c ：d ：e ？f ：g").unwrap(),
            Expr::app_many(
                Expr::var("_？_：_"),
                vec![
                    Expr::app_many(
                        Expr::var("_？_：_"),
                        vec![
                            Expr::var("a"),
                            Expr::app_many(
                                Expr::var("_？_：_"),
                                vec![Expr::var("b"), Expr::var("c"), Expr::var("d")]
                            ),
                            Expr::var("e"),
                        ]
                    ),
                    Expr::var("f"),
                    Expr::var("g"),
                ]
            )
        );

        // closed
        assert_eq!(
            parser.parse_expr("||n + m||").unwrap(),
            Expr::app_many(
                Expr::var("||_||"),
                vec![Expr::app_many(
                    Expr::var("_+_"),
                    vec![Expr::var("n"), Expr::var("m")],
                )]
            )
        );

        // associativity
        assert_eq!(
            parser.parse_expr("n ^ m ^ k").unwrap(),
            Expr::app_many(
                Expr::var("_^_"),
                vec![
                    Expr::var("n"),
                    Expr::app_many(Expr::var("_^_"), vec![Expr::var("m"), Expr::var("k")],),
                ]
            )
        );

        // precedence
        assert_eq!(
            parser.parse_expr("n + m * k").unwrap(),
            Expr::app_many(
                Expr::var("_+_"),
                vec![
                    Expr::var("n"),
                    Expr::app_many(Expr::var("_*_"), vec![Expr::var("m"), Expr::var("k")]),
                ]
            )
        );

        // application precedence
        assert_eq!(
            parser.parse_expr("||f x x||").unwrap(),
            Expr::app_many(
                Expr::var("||_||"),
                vec![Expr::app_many(
                    Expr::var("f"),
                    vec![Expr::var("x"), Expr::var("x")]
                ),]
            )
        );

        // application on top
        assert_eq!(
            parser.parse_expr("f x x").unwrap(),
            Expr::app_many(Expr::var("f"), vec![Expr::var("x"), Expr::var("x")])
        );
    }

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
