use std::{cell::RefCell, rc::Rc};

use wez_lang_lib::{environment::Environment, evaluator::Evaluator, lexer::Lexer, parser::Parser};

// #[global_allocator]
// static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;
//
fn main() {
    for x in 0..=29 {
        let s = format!("
        let fib = fn(x) {{ if (x == 0) {{ 0 }} else {{ if (x == 1) {{ 1 }} else {{ fib(x - 1) + fib(x - 2) }} }} }};
        fib({x});
        ");
        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));
        let _ = e.eval_program(&p.parse_program());
    }
}
