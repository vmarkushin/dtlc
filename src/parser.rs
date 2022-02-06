use crate::grammar::{DeclParser, ExprParser, ProgParser};
use crate::syntax::surf::{Decl, Expr, Prog};
use crate::token::Token;
use codespan::Files;
use logos::Logos;

type ParseError<'a> = lalrpop_util::ParseError<usize, Token<'a>, &'static str>;

pub struct Parser<'a> {
    expr: ExprParser,
    decl: DeclParser,
    prog: ProgParser,
    files: Files<&'a str>,
}

impl<'a> Parser<'a> {
    pub fn parse_expr(&mut self, input: &'a str) -> Result<Expr, ParseError<'a>> {
        let tokens = self.lexer(input);
        self.expr.parse(tokens)
    }

    pub fn parse_decl(&mut self, input: &'a str) -> Result<Decl, ParseError<'a>> {
        let tokens = self.lexer(input);
        self.decl.parse(tokens)
    }

    pub fn parse_prog(&mut self, input: &'a str) -> Result<Prog, ParseError<'a>> {
        let tokens = self.lexer(input);
        self.prog.parse(tokens)
    }
}

impl<'a> Parser<'a> {
    pub fn new(expr: ExprParser, decl: DeclParser, prog: ProgParser) -> Self {
        let files = Files::new();
        Self {
            expr,
            decl,
            prog,
            files,
        }
    }

    fn lexer(&mut self, input: &'a str) -> impl Iterator<Item = (usize, Token<'a>, usize)> + 'a {
        let _fid = self.files.add("tmp", input);
        let tokens = Token::lexer(input).spanned().map(move |(tok, span)| {
            // let loc = files
            //     .location(fid, RawIndex::from(span.start as u32))
            //     .unwrap();
            // (
            //     tok,
            //     Loc::new(
            //         loc.line.number().to_usize(),
            //         span.start,
            //         span.end,
            //         loc.column.to_usize(),
            //     ),
            // )
            (span.start, tok, span.end)
        });
        tokens
    }
}

impl<'a> Default for Parser<'a> {
    fn default() -> Self {
        Self::new(ExprParser::new(), DeclParser::new(), ProgParser::new())
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::{ParseError, Parser};
    use crate::syntax::surf::Expr::{self};
    use crate::syntax::Ident;
    use crate::token::Token;

    #[test]
    fn parse_pi() {
        let mut parser = Parser::default();

        assert_eq!(
            parser.parse_expr("forall (T : A), T").unwrap(),
            Expr::pi_many(
                vec![(Ident::new("T", 8..9), Expr::var("A", 12..13))].into_iter(),
                Expr::var("T", 16..17),
            )
        );

        assert_eq!(
            parser.parse_expr("forall (T U V : A), T").unwrap(),
            Expr::pi_many(
                vec![
                    (Ident::new("T", 8..9), Expr::var("A", 16..17)),
                    (Ident::new("U", 10..11), Expr::var("A", 16..17)),
                    (Ident::new("V", 12..13), Expr::var("A", 16..17)),
                ]
                .into_iter(),
                Expr::var("T", 20..21),
            )
        );

        assert_eq!(
            parser.parse_expr("forall (T U : A) (V : B), T").unwrap(),
            Expr::pi_many(
                vec![
                    (Ident::new("T", 8..9), Expr::var("A", 14..15)),
                    (Ident::new("U", 10..11), Expr::var("A", 14..15)),
                    (Ident::new("V", 18..19), Expr::var("B", 22..23)),
                ]
                .into_iter(),
                Expr::var("T", 26..27),
            )
        );

        assert_eq!(
            parser.parse_expr("forall (T U : A) X : A , T").unwrap_err(),
            ParseError::UnrecognizedToken {
                token: (17, Token::Ident("X"), 18),
                expected: vec!["\"(\"".into(), "\",\"".into()]
            }
        );
        assert_eq!(
            parser.parse_expr("forall T U : A, T").unwrap_err(),
            ParseError::UnrecognizedToken {
                token: (7, Token::Ident("T"), 8),
                expected: vec!["\"(\"".into()]
            }
        );
    }

    #[test]
    fn parse_lam() {
        let mut parser = Parser::default();

        assert_eq!(
            parser.parse_expr("lam x : T => x").unwrap(),
            Expr::lam_many(
                Expr::var("x", 13..14),
                vec![(Ident::new("x", 4..5), Expr::var("T", 8..9))].into_iter()
            )
        );

        // assert_eq!(
        //     parser.parse_expr("lam (x : T) => x").unwrap(),
        //     Expr::lam_many(
        //         "x".parse().unwrap(),
        //         vec![("x".into(), "T".parse().unwrap())].into_iter(),
        //     )
        // );
        //
        // assert_eq!(
        //     parser.parse_expr("lam (x y z : T) => x").unwrap(),
        //     Expr::lam_many(
        //         "x".parse().unwrap(),
        //         vec![
        //             ("x".into(), "T".parse().unwrap()),
        //             ("y".into(), "T".parse().unwrap()),
        //             ("z".into(), "T".parse().unwrap())
        //         ]
        //         .into_iter(),
        //     )
        // );
        //
        // assert_eq!(
        //     parser.parse_expr("lam (x y : T) (z : U) => x").unwrap(),
        //     Expr::lam_many(
        //         "x".parse().unwrap(),
        //         vec![
        //             ("x".into(), "T".parse().unwrap()),
        //             ("y".into(), "T".parse().unwrap()),
        //             ("z".into(), "U".parse().unwrap())
        //         ]
        //         .into_iter(),
        //     )
        // );
        //
        // assert!(parser.parse_expr("lam (a b : T) c : U => a").is_err());
        // assert!(parser.parse_expr("lam x y : T => x").is_err());
    }
}
