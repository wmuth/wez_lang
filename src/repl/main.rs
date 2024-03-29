use std::{
    cell::RefCell,
    io::{self, Write},
    rc::Rc,
};
use wez_lang_lib::{
    environment::Environment,
    evaluator::{Evaluator, PrintResult},
    lexer::Lexer,
    parser::Parser,
};

fn main() -> Result<(), io::Error> {
    let env = Rc::new(RefCell::new(Environment::new(None)));

    let mut input = String::new();
    println!("Welcome to Wez-lang REPL!");

    loop {
        print!("🐻‍❄️ >>> ");

        io::stdout().flush()?;
        io::stdin().read_line(&mut input)?;
        if input.trim_end().is_empty() {
            break;
        }

        let lex = Lexer::new(&input);
        let mut par = Parser::new(lex);
        let pro = par.parse_program();

        let err = par.get_lex_errors();
        if !err.is_empty() {
            println!("There were lexer errors:");
            for e in err {
                println!("LEXER ERR: {e}");
            }
        }

        let err = par.get_errors();
        if !err.is_empty() {
            println!("There were parser errors:");
            for e in err {
                println!("PARSER ERR: {e}");
            }
        }

        let mut e = Evaluator::new(Rc::clone(&env));
        println!("{}", e.eval_program(&pro).ps());

        input.clear();
    }

    Ok(())
}
