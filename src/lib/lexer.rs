use crate::token::Token;
use std::fmt::Display;
use std::iter::Peekable;
use std::num::ParseIntError;
use std::rc::Rc;
use std::str::Chars;

/// The errors the [`Lexer`] can produce
pub enum LexError {
    Unparsable(String),
}

impl Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unparsable(s) => write!(f, "Unparsable \"{s}\""),
        }
    }
}

/// The lexer which lexes user input to [`Token`]
pub struct Lexer<'a> {
    ch: char,
    errs: Vec<LexError>,
    input: Peekable<Chars<'a>>,
}

impl Lexer<'_> {
    /// Creates the [`Lexer`]
    ///
    /// # Parameters
    /// - `s` the string of user input to lex
    #[must_use]
    pub fn new(s: &str) -> Lexer {
        let mut lex = Lexer {
            ch: '\0',
            errs: vec![],
            input: s.chars().peekable(),
        };
        lex.read_char();

        lex
    }

    /// Gets the vec of errors from the [`Lexer`]
    #[must_use]
    pub fn get_errs(&self) -> &[LexError] {
        &self.errs
    }

    /// Returns the next [`Token`]
    pub fn next_tok(&mut self) -> Token {
        self.skip_whitespace();

        let tok = match self.ch {
            'A'..='Z' | 'a'..='z' | '_' => {
                let ident = self.read_ident();
                match ident.as_str() {
                    "beariable" | "let" => Token::Let,
                    "bear" | "true" => Token::True,
                    "else" | "nanook" => Token::Else,
                    "false" | "penguin" => Token::False,
                    "fn" | "wez" => Token::Function,
                    "ice" | "if" => Token::If,
                    "northbound" | "return" => Token::Return,
                    "stonk" => Token::Plus,
                    _ => Token::Ident(Rc::from(ident)),
                }
            }
            '0'..='9' => match self.read_int() {
                Ok(i) => Token::Int(i),
                Err(e) => {
                    self.errs.push(LexError::Unparsable(format!("{e}")));
                    self.next_tok()
                }
            },
            '=' => match self.input.peek().unwrap_or(&'\0') {
                '=' => {
                    self.read_char();
                    Token::Eq
                }
                _ => Token::Assign,
            },
            '!' => match self.input.peek().unwrap_or(&'\0') {
                '=' => {
                    self.read_char();
                    Token::NotEq
                }
                _ => Token::Bang,
            },
            '"' => {
                if self.input.peek().unwrap_or(&'\0') == &'"' {
                    self.read_char();
                    Token::String(Rc::from(""))
                } else {
                    Token::String(Rc::from(self.read_string().as_str()))
                }
            }
            ':' => Token::Colon,
            ',' => Token::Comma,
            '{' => Token::Lbrace,
            '[' => Token::Lbracket,
            '<' => Token::Less,
            '(' => Token::Lparen,
            '-' => Token::Minus,
            '>' => Token::More,
            '%' => Token::Percent,
            '+' => Token::Plus,
            '}' => Token::Rbrace,
            ']' => Token::Rbracket,
            ')' => Token::Rparen,
            ';' => Token::Semicolon,
            '/' => Token::Slash,
            '*' => Token::Star,
            '\0' => Token::Eof,
            _ => self.try_emoji(),
        };

        self.read_char();

        tok
    }

    fn read_char(&mut self) {
        self.ch = self.input.next().unwrap_or('\0');
    }

    fn read_ident(&mut self) -> String {
        let mut build = String::with_capacity(32);
        build.insert(0, self.ch);

        while self.input.peek().unwrap_or(&'\0').is_alphabetic() {
            self.read_char();
            build.push(self.ch);
        }

        build.shrink_to_fit();

        build
    }

    fn read_int(&mut self) -> Result<isize, ParseIntError> {
        let mut build = String::with_capacity(20);
        build.insert(0, self.ch);

        while self.input.peek().unwrap_or(&'\0').is_numeric() {
            self.read_char();
            build.push(self.ch);
        }

        build.shrink_to_fit();

        build.parse()
    }

    fn read_string(&mut self) -> String {
        self.read_char();

        let mut build = String::with_capacity(64);
        build.insert(0, self.ch);

        while self.input.peek().unwrap_or(&'\0') != &'\0'
            && self.input.peek().unwrap_or(&'\0') != &'"'
        {
            self.read_char();
            build.push(self.ch);
        }

        self.read_char();

        build.shrink_to_fit();

        build
    }

    fn skip_whitespace(&mut self) {
        while self.ch.is_whitespace() {
            self.read_char();
        }
    }

    fn try_emoji(&mut self) -> Token {
        match self.ch {
            '🐻' => match self.input.peek().unwrap_or(&'\0') {
                '‍' => {
                    self.read_char();
                    self.read_char();
                    self.read_char();
                    Token::Let
                }
                _ => Token::Let,
            },
            _ => Token::Illegal,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::Lexer;
    use crate::token::Token;

    #[test]
    fn tokens_working_basic() {
        let s = "let five = 5;
                  let ten = 10;

                  let add = fn(x, y) {
                    x + y;
                  };

                  let result = add(five, ten);

                  !-/*5;
                  5<10>5;

                  if (5 < 10) {
                    return true;
                  } else {
                    return false;
                  }

                  10 == 10;
                  10 != 9;

                  \"Hello Str\";
                  \"\";
                  \" \";

                  let x = [1, \"two\"];
                  x[0];

                  let x = {1: 1, 2: 2};
                  x[1];

                  10 % 2;
                  ";

        let mut lex = Lexer::new(s);

        let correct = [
            Token::Let,
            Token::Ident(Rc::from("five")),
            Token::Assign,
            Token::Int(5),
            Token::Semicolon,
            Token::Let,
            Token::Ident(Rc::from("ten")),
            Token::Assign,
            Token::Int(10),
            Token::Semicolon,
            Token::Let,
            Token::Ident(Rc::from("add")),
            Token::Assign,
            Token::Function,
            Token::Lparen,
            Token::Ident(Rc::from("x")),
            Token::Comma,
            Token::Ident(Rc::from("y")),
            Token::Rparen,
            Token::Lbrace,
            Token::Ident(Rc::from("x")),
            Token::Plus,
            Token::Ident(Rc::from("y")),
            Token::Semicolon,
            Token::Rbrace,
            Token::Semicolon,
            Token::Let,
            Token::Ident(Rc::from("result")),
            Token::Assign,
            Token::Ident(Rc::from("add")),
            Token::Lparen,
            Token::Ident(Rc::from("five")),
            Token::Comma,
            Token::Ident(Rc::from("ten")),
            Token::Rparen,
            Token::Semicolon,
            Token::Bang,
            Token::Minus,
            Token::Slash,
            Token::Star,
            Token::Int(5),
            Token::Semicolon,
            Token::Int(5),
            Token::Less,
            Token::Int(10),
            Token::More,
            Token::Int(5),
            Token::Semicolon,
            Token::If,
            Token::Lparen,
            Token::Int(5),
            Token::Less,
            Token::Int(10),
            Token::Rparen,
            Token::Lbrace,
            Token::Return,
            Token::True,
            Token::Semicolon,
            Token::Rbrace,
            Token::Else,
            Token::Lbrace,
            Token::Return,
            Token::False,
            Token::Semicolon,
            Token::Rbrace,
            Token::Int(10),
            Token::Eq,
            Token::Int(10),
            Token::Semicolon,
            Token::Int(10),
            Token::NotEq,
            Token::Int(9),
            Token::Semicolon,
            Token::String(Rc::from("Hello Str")),
            Token::Semicolon,
            Token::String(Rc::from("")),
            Token::Semicolon,
            Token::String(Rc::from(" ")),
            Token::Semicolon,
            Token::Let,
            Token::Ident(Rc::from("x")),
            Token::Assign,
            Token::Lbracket,
            Token::Int(1),
            Token::Comma,
            Token::String(Rc::from("two")),
            Token::Rbracket,
            Token::Semicolon,
            Token::Ident(Rc::from("x")),
            Token::Lbracket,
            Token::Int(0),
            Token::Rbracket,
            Token::Semicolon,
            Token::Let,
            Token::Ident(Rc::from("x")),
            Token::Assign,
            Token::Lbrace,
            Token::Int(1),
            Token::Colon,
            Token::Int(1),
            Token::Comma,
            Token::Int(2),
            Token::Colon,
            Token::Int(2),
            Token::Rbrace,
            Token::Semicolon,
            Token::Ident(Rc::from("x")),
            Token::Lbracket,
            Token::Int(1),
            Token::Rbracket,
            Token::Semicolon,
            Token::Int(10),
            Token::Percent,
            Token::Int(2),
            Token::Semicolon,
            Token::Eof,
        ];

        for (i, token) in correct.into_iter().enumerate() {
            let next = lex.next_tok();
            assert_eq!(next, token, "Error with token {i}");
        }
    }

    #[test]
    fn tokens_working_wez() {
        let s = "beariable x = ice(bear == penguin) { wez(x) { northbound x stonk 1; } } nanook { wez(x) { northbound x stonk 2; } };
                 🐻 🐻‍❄️";

        let mut lex = Lexer::new(s);

        let ident = Rc::from("x");

        let correct = [
            Token::Let,
            Token::Ident(Rc::clone(&ident)),
            Token::Assign,
            Token::If,
            Token::Lparen,
            Token::True,
            Token::Eq,
            Token::False,
            Token::Rparen,
            Token::Lbrace,
            Token::Function,
            Token::Lparen,
            Token::Ident(Rc::clone(&ident)),
            Token::Rparen,
            Token::Lbrace,
            Token::Return,
            Token::Ident(Rc::clone(&ident)),
            Token::Plus,
            Token::Int(1),
            Token::Semicolon,
            Token::Rbrace,
            Token::Rbrace,
            Token::Else,
            Token::Lbrace,
            Token::Function,
            Token::Lparen,
            Token::Ident(Rc::clone(&ident)),
            Token::Rparen,
            Token::Lbrace,
            Token::Return,
            Token::Ident(Rc::clone(&ident)),
            Token::Plus,
            Token::Int(2),
            Token::Semicolon,
            Token::Rbrace,
            Token::Rbrace,
            Token::Semicolon,
            Token::Let,
            Token::Let,
            Token::Eof,
        ];

        for (i, token) in correct.into_iter().enumerate() {
            let next = lex.next_tok();
            assert_eq!(next, token, "Error with token {i}");
        }
    }
}
