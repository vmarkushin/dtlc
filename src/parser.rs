use crate::expr::Expr;
use crate::grammar::{ExprParser, ItemParser};
use crate::item::Item;

type ParseError<'a> = lalrpop_util::ParseError<usize, lalrpop_util::lexer::Token<'a>, &'static str>;

pub struct Parser {
    expr_parser: ExprParser,
    item_parser: ItemParser,
}

impl Parser {
    pub(crate) fn parse_item<'a>(&self, input: &'a str) -> Result<Item, ParseError<'a>> {
        self.item_parser.parse(input)
    }

    pub(crate) fn parse_expr<'a>(&self, input: &'a str) -> Result<Expr, ParseError<'a>> {
        self.expr_parser.parse(input)
    }
}

impl Parser {
    pub fn new(expr_parser: ExprParser, item_parser: ItemParser) -> Self {
        Parser {
            expr_parser,
            item_parser,
        }
    }
}
