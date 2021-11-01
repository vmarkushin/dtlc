use crate::decl::Decl;
use crate::env::Prog;
use crate::grammar::{DeclParser, ProgParser, TermParser};
use crate::term::Term;
use crate::token::Token;
use logos::Logos;

type ParseError<'a> = lalrpop_util::ParseError<usize, Token<'a>, &'static str>;

pub struct Parser {
    term_parser: TermParser,
    decl_parser: DeclParser,
    prog_parser: ProgParser,
}

impl Parser {
    pub(crate) fn parse_decl<'a>(&self, input: &'a str) -> Result<Decl, ParseError<'a>> {
        let tokens = Token::lexer(input);
        self.decl_parser
            .parse(tokens)
            .map_err(|x| x.map_location(|_| 0))
    }

    pub(crate) fn parse_term<'a>(&self, input: &'a str) -> Result<Term, ParseError<'a>> {
        let tokens = Token::lexer(input);
        self.term_parser
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
    pub fn new(term_parser: TermParser, decl_parser: DeclParser, prog_parser: ProgParser) -> Self {
        Parser {
            term_parser,
            decl_parser,
            prog_parser,
        }
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new(TermParser::new(), DeclParser::new(), ProgParser::new())
    }
}

#[test]
fn parse_pi() {
    let parser = Parser::default();

    assert_eq!(
        parser.parse_term("forall T : A, T").unwrap(),
        Term::pi_many(
            vec![("T".parse().unwrap(), "A".parse().unwrap())],
            "T".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_term("forall (T : A), T").unwrap(),
        Term::pi_many(
            vec![("T".parse().unwrap(), "A".parse().unwrap())],
            "T".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_term("forall (T U V : A), T").unwrap(),
        Term::pi_many(
            vec![
                ("T".parse().unwrap(), "A".parse().unwrap()),
                ("U".parse().unwrap(), "A".parse().unwrap()),
                ("V".parse().unwrap(), "A".parse().unwrap())
            ],
            "T".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_term("forall (T U : A) (V : B), T").unwrap(),
        Term::pi_many(
            vec![
                ("T".parse().unwrap(), "A".parse().unwrap()),
                ("U".parse().unwrap(), "A".parse().unwrap()),
                ("V".parse().unwrap(), "B".parse().unwrap())
            ],
            "T".parse().unwrap()
        )
    );

    assert!(parser.parse_term("forall (T U : A) X : A , T").is_err());
    assert!(parser.parse_term("forall T U : A, T").is_err());
}

#[test]
fn parse_lam() {
    let parser = Parser::default();

    assert_eq!(
        parser.parse_term("lam x : T => x").unwrap(),
        Term::lam_many(
            vec![("x".parse().unwrap(), "T".parse().unwrap())],
            "x".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_term("lam (x : T) => x").unwrap(),
        Term::lam_many(
            vec![("x".parse().unwrap(), "T".parse().unwrap())],
            "x".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_term("lam (x y z : T) => x").unwrap(),
        Term::lam_many(
            vec![
                ("x".parse().unwrap(), "T".parse().unwrap()),
                ("y".parse().unwrap(), "T".parse().unwrap()),
                ("z".parse().unwrap(), "T".parse().unwrap())
            ],
            "x".parse().unwrap()
        )
    );

    assert_eq!(
        parser.parse_term("lam (x y : T) (z : U) => x").unwrap(),
        Term::lam_many(
            vec![
                ("x".parse().unwrap(), "T".parse().unwrap()),
                ("y".parse().unwrap(), "T".parse().unwrap()),
                ("z".parse().unwrap(), "U".parse().unwrap())
            ],
            "x".parse().unwrap()
        )
    );

    assert!(parser.parse_term("lam (a b : T) c : U => a").is_err());
    assert!(parser.parse_term("lam x y : T => x").is_err());
}
