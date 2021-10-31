use crate::env::Prog;
use crate::expr::Expr;
use crate::grammar::{ExprParser, ItemParser, ProgParser};
use crate::item::Item;
use crate::token::Token;
use logos::Logos;

type ParseError<'a> = lalrpop_util::ParseError<usize, Token<'a>, &'static str>;

pub struct Parser {
    expr_parser: ExprParser,
    item_parser: ItemParser,
    prog_parser: ProgParser,
}

impl Parser {
    pub(crate) fn parse_item<'a>(&self, input: &'a str) -> Result<Item, ParseError<'a>> {
        let tokens = Token::lexer(input);
        self.item_parser
            .parse(tokens)
            .map_err(|x| x.map_location(|_| 0))
    }

    pub(crate) fn parse_expr<'a>(&self, input: &'a str) -> Result<Expr, ParseError<'a>> {
        let tokens = Token::lexer(input);
        self.expr_parser
            .parse(tokens)
            .map_err(|x| x.map_location(|_| 0))
    }

    pub(crate) fn parse_prog<'a>(&self, input: &'a str) -> Result<Prog, ParseError<'a>> {
        let tokens = Token::lexer(input);
        self.prog_parser
            .parse(tokens)
            .map_err(|x| x.map_location(|_| 0))
    }
}

impl Parser {
    pub fn new(expr_parser: ExprParser, item_parser: ItemParser, prog_parser: ProgParser) -> Self {
        Parser {
            expr_parser,
            item_parser,
            prog_parser,
        }
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new(ExprParser::new(), ItemParser::new(), ProgParser::new())
    }
}

#[test]
fn parse_pi() {
    let parser = Parser::default();

    assert_eq!(
        parser.parse_expr("forall T : A, T").unwrap(),
        Expr::pi_many(
            [("T".parse().unwrap(), "A".parse().unwrap())],
            "T".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_expr("forall (T : A), T").unwrap(),
        Expr::pi_many(
            [("T".parse().unwrap(), "A".parse().unwrap())],
            "T".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_expr("forall (T U V : A), T").unwrap(),
        Expr::pi_many(
            [
                ("T".parse().unwrap(), "A".parse().unwrap()),
                ("U".parse().unwrap(), "A".parse().unwrap()),
                ("V".parse().unwrap(), "A".parse().unwrap())
            ],
            "T".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_expr("forall (T U : A) (V : B), T").unwrap(),
        Expr::pi_many(
            [
                ("T".parse().unwrap(), "A".parse().unwrap()),
                ("U".parse().unwrap(), "A".parse().unwrap()),
                ("V".parse().unwrap(), "B".parse().unwrap())
            ],
            "T".parse().unwrap()
        )
    );

    assert!(parser.parse_expr("forall (T U : A) X : A , T").is_err());
    assert!(parser.parse_expr("forall T U : A, T").is_err());
}

#[test]
fn parse_lam() {
    let parser = Parser::default();

    assert_eq!(
        parser.parse_expr("lam x : T => x").unwrap(),
        Expr::lam_many(
            [("x".parse().unwrap(), "T".parse().unwrap())],
            "x".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_expr("lam (x : T) => x").unwrap(),
        Expr::lam_many(
            [("x".parse().unwrap(), "T".parse().unwrap())],
            "x".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_expr("lam (x y z : T) => x").unwrap(),
        Expr::lam_many(
            [
                ("x".parse().unwrap(), "T".parse().unwrap()),
                ("y".parse().unwrap(), "T".parse().unwrap()),
                ("z".parse().unwrap(), "T".parse().unwrap())
            ],
            "x".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_expr("lam (x y : T) (z : U) => x").unwrap(),
        Expr::lam_many(
            [
                ("x".parse().unwrap(), "T".parse().unwrap()),
                ("y".parse().unwrap(), "T".parse().unwrap()),
                ("z".parse().unwrap(), "U".parse().unwrap())
            ],
            "x".parse().unwrap()
        )
    );

    assert!(parser.parse_expr("lam (a b : T) c : U => a").is_err());
    assert!(parser.parse_expr("lam x y : T => x").is_err());
}
