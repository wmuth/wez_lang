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

        let err = par.get_errors();

        for e in err {
            println!("{e}");
        }

        for s in pro.statements {
            println!("{s}");
        }

        input.clear();
    }

    Ok(())
}
