use crate::decl::Decl;
use crate::env::Prog;
use crate::grammar::{DeclParser, ProgParser, TermParser};
use crate::term::Term;
use crate::token::Token;
use logos::Logos;

type ParseError<'a> = lalrpop_util::ParseError<usize, Token<'a>, &'static str>;

pub struct Parser {
    term: TermParser,
    decl: DeclParser,
    prog: ProgParser,
}

impl Parser {
    pub(crate) fn parse_decl<'a>(&self, input: &'a str) -> Result<Decl, ParseError<'a>> {
        let tokens = Token::lexer(input);
        self.decl.parse(tokens).map_err(|x| x.map_location(|_| 0))
    }

    pub(crate) fn parse_term<'a>(&self, input: &'a str) -> Result<Term, ParseError<'a>> {
        let tokens = Token::lexer(input);
        self.term.parse(tokens).map_err(|x| x.map_location(|_| 0))
    }

    pub(crate) fn parse_prog<'a>(&self, input: &'a str) -> Result<Prog, ParseError<'a>> {
        let tokens = Token::lexer(input);
        self.prog.parse(tokens).map_err(|x| x.map_location(|_| 0))
    }
}

impl Parser {
    pub fn new(term: TermParser, decl: DeclParser, prog: ProgParser) -> Self {
        Self { term, decl, prog }
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new(TermParser::new(), DeclParser::new(), ProgParser::new())
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::Parser;
    use crate::term::{Lam, Pi};

    #[test]
    fn parse_pi() {
        let parser = Parser::default();

        assert_eq!(
            parser.parse_term("forall (T : A), T").unwrap(),
            Pi::new_many(
                "T".parse().unwrap(),
                vec![("T".into(), "A".parse().unwrap())].into_iter(),
            )
        );

        assert_eq!(
            parser.parse_term("forall (T : A), T").unwrap(),
            Pi::new_many(
                "T".parse().unwrap(),
                vec![("T".into(), "A".parse().unwrap())].into_iter(),
            )
        );

        assert_eq!(
            parser.parse_term("forall (T U V : A), T").unwrap(),
            Pi::new_many(
                "T".parse().unwrap(),
                vec![
                    ("T".into(), "A".parse().unwrap()),
                    ("U".into(), "A".parse().unwrap()),
                    ("V".into(), "A".parse().unwrap())
                ]
                .into_iter(),
            )
        );

        assert_eq!(
            parser.parse_term("forall (T U : A) (V : B), T").unwrap(),
            Pi::new_many(
                "T".parse().unwrap(),
                vec![
                    ("T".into(), "A".parse().unwrap()),
                    ("U".into(), "A".parse().unwrap()),
                    ("V".into(), "B".parse().unwrap())
                ]
                .into_iter(),
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
            Lam::new_many(
                "x".parse().unwrap(),
                vec![("x".into(), "T".parse().unwrap())].into_iter()
            )
        );

        assert_eq!(
            parser.parse_term("lam (x : T) => x").unwrap(),
            Lam::new_many(
                "x".parse().unwrap(),
                vec![("x".into(), "T".parse().unwrap())].into_iter(),
            )
        );

        assert_eq!(
            parser.parse_term("lam (x y z : T) => x").unwrap(),
            Lam::new_many(
                "x".parse().unwrap(),
                vec![
                    ("x".into(), "T".parse().unwrap()),
                    ("y".into(), "T".parse().unwrap()),
                    ("z".into(), "T".parse().unwrap())
                ]
                .into_iter(),
            )
        );

        assert_eq!(
            parser.parse_term("lam (x y : T) (z : U) => x").unwrap(),
            Lam::new_many(
                "x".parse().unwrap(),
                vec![
                    ("x".into(), "T".parse().unwrap()),
                    ("y".into(), "T".parse().unwrap()),
                    ("z".into(), "U".parse().unwrap())
                ]
                .into_iter(),
            )
        );

        assert!(parser.parse_term("lam (a b : T) c : U => a").is_err());
        assert!(parser.parse_term("lam x y : T => x").is_err());
    }
}
