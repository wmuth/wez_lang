use crate::token::Token;
use std::fmt::Display;
use std::iter::Peekable;
use std::num::ParseIntError;
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
    pub const fn get_errs(&self) -> &Vec<LexError> {
        &self.errs
    }

    /// Returns the next [`Token`]
    pub fn next_tok(&mut self) -> Token {
        self.skip_whitespace();

        let tok = match self.ch {
            'A'..='Z' | 'a'..='z' | '_' => {
                let ident = self.read_ident();
                match ident.as_str() {
                    "else" => Token::Else,
                    "false" => Token::False,
                    "fn" => Token::Function,
                    "if" => Token::If,
                    "let" => Token::Let,
                    "return" => Token::Return,
                    "true" => Token::True,
                    _ => Token::Ident(ident),
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
                    Token::String(String::new())
                } else {
                    Token::String(self.read_str())
                }
            }
            ',' => Token::Comma,
            '{' => Token::Lbrace,
            '<' => Token::Less,
            '(' => Token::Lparen,
            '-' => Token::Minus,
            '>' => Token::More,
            '+' => Token::Plus,
            '}' => Token::Rbrace,
            ')' => Token::Rparen,
            ';' => Token::Semicolon,
            '/' => Token::Slash,
            '*' => Token::Star,
            '\0' => Token::Eof,
            _ => Token::Illegal,
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

    fn read_str(&mut self) -> String {
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
}

#[cfg(test)]
mod tests {
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
                  ";

        let mut lex = Lexer::new(s);

        let correct = vec![
            Token::Let,
            Token::Ident(String::from("five")),
            Token::Assign,
            Token::Int(5),
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("ten")),
            Token::Assign,
            Token::Int(10),
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("add")),
            Token::Assign,
            Token::Function,
            Token::Lparen,
            Token::Ident(String::from("x")),
            Token::Comma,
            Token::Ident(String::from("y")),
            Token::Rparen,
            Token::Lbrace,
            Token::Ident(String::from("x")),
            Token::Plus,
            Token::Ident(String::from("y")),
            Token::Semicolon,
            Token::Rbrace,
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("result")),
            Token::Assign,
            Token::Ident(String::from("add")),
            Token::Lparen,
            Token::Ident(String::from("five")),
            Token::Comma,
            Token::Ident(String::from("ten")),
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
            Token::String(String::from("Hello Str")),
            Token::Semicolon,
            Token::String(String::new()),
            Token::Semicolon,
            Token::String(String::from(" ")),
            Token::Semicolon,
            Token::Eof,
        ];

        for token in correct {
            let next = lex.next_tok();
            assert_eq!(next, token);
        }
    }
}
