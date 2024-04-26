use std::{
    cell::RefCell,
    io::{self, Write},
    rc::Rc,
};

use wez_lang::{
    builtins::get_builtin_fns, environment::Environment, evaluator::Evaluator, lexer::Lexer,
    parser::Parser,
};

/// Runs the repl
fn main() -> Result<(), io::Error> {
    let env = Rc::new(RefCell::new(Environment::new(None)));
    env.borrow_mut().add_map(get_builtin_fns());

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
        match e.eval_program(&pro) {
            Ok(o) => println!("{o}"),
            Err(e) => eprintln!("{e}"),
        }

        input.clear();
    }

    Ok(())
}
