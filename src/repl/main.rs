use std::io::{self, Write};
use wez_lang_lib::{lexer::Lexer, parser::Parser};

fn main() -> Result<(), io::Error> {
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

        println!("Parsed statements:");
        for s in pro.statements {
            println!("{s}");
        }

        input.clear();
    }

    Ok(())
}
