use crate::grammar::{DeclParser, ExprParser, ProgParser};
use crate::syntax::surf::{Decl, Expr, Prog};
use crate::token::{lexer, Position, Token};
use codespan_reporting::files::SimpleFile;
type ParseError<'a> = lalrpop_util::ParseError<Position, Token<'a>, &'static str>;

pub struct Parser {
    expr: ExprParser,
    decl: DeclParser,
    prog: ProgParser,
    file: SimpleFile<String, String>,
    // files: Files<Rc<String>>,
}

impl Parser {
    pub fn parse_expr<'inp>(&self, input: &'inp str) -> Result<Expr, ParseError<'inp>> {
        let tokens = lexer(input);
        self.expr.parse(tokens)
    }

    pub fn parse_decl<'inp>(&self, input: &'inp str) -> Result<Decl, ParseError<'inp>> {
        let tokens = lexer(input);
        self.decl.parse(tokens)
    }

    pub fn parse_prog<'inp>(&self, input: &'inp str) -> Result<Prog, ParseError<'inp>> {
        let tokens = lexer(input);
        self.prog.parse(tokens)
    }
}

impl Parser {
    pub fn new(expr: ExprParser, decl: DeclParser, prog: ProgParser) -> Self {
        let file = SimpleFile::new("".to_owned(), "".to_owned());
        // let files = Files::new();
        Self {
            expr,
            decl,
            prog,
            file,
            // files,
        }
    }

    // fn lexer2(&mut self, input: &'a str) -> FileIter<'a> {
    //     let files = Files::new();
    //
    //     let file_iter = FileIter {
    //         files,
    //         // input,
    //     };
    // }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new(ExprParser::new(), DeclParser::new(), ProgParser::new())
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::{ParseError, Parser};
    use crate::syntax::surf::Expr::{self};
    use crate::syntax::Ident;
    use crate::token::{Position, Token};

    #[test]
    fn parse_pi() {
        let parser = Parser::default();

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
                token: ((17, 1, 18).into(), Token::Ident("X"), (18, 1, 19).into()),
                expected: vec!["\"(\"".into(), "\",\"".into()]
            }
        );
        assert_eq!(
            parser.parse_expr("forall T U : A, T").unwrap_err(),
            ParseError::UnrecognizedToken {
                token: (
                    Position::new(7, 1, 8),
                    Token::Ident("T"),
                    Position::new(8, 1, 9)
                ),
                expected: vec!["\"(\"".into()]
            }
        );
    }

    #[test]
    fn parse_lam() {
        let parser = Parser::default();

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
