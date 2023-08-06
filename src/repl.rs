use std::io::{self, Write};

pub fn repl() {
    let mut input = String::new();
    println!("Welcome to Wez-lang REPL!");

    loop {
        print!("🐻‍❄️ >>> ");
        io::stdout().flush().unwrap();
        io::stdin().read_line(&mut input).unwrap();
        let mut lex = Lexer::new(&input);
        let mut tok = lex.next();
        while tok != Token::Eof {
            println!("{}", tok);
            tok = lex.next();
        }
        input.clear();
    }
}
