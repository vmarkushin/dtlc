#![feature(box_syntax, box_patterns, type_alias_impl_trait)]

use dtlc::repl;

fn main() {
    env_logger::init();
    repl::repl("> ", repl::run_repl);
}
