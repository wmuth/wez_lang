use std::fmt::Display;
use std::iter::Peekable;
use std::num::ParseIntError;
use std::str::Chars;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    Assign,
    Bang,
    Comma,
    Minus,
    Else,
    Eof,
    Eq,
    False,
    Function,
    Ident(String),
    If,
    Illegal,
    Int(isize),
    Lbrace,
    Less,
    Let,
    Lparen,
    More,
    NotEq,
    Plus,
    Rbrace,
    Return,
    Rparen,
    Semicolon,
    Slash,
    Star,
    True,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Assign => write!(f, "Assign"),
            Self::Bang => write!(f, "Bang/Exlaim"),
            Self::Comma => write!(f, "Comma"),
            Self::Minus => write!(f, "Minus"),
            Self::Else => write!(f, "Else"),
            Self::Eof => write!(f, "Eof"),
            Self::Eq => write!(f, "Equal"),
            Self::False => write!(f, "False"),
            Self::Function => write!(f, "Function"),
            Self::Ident(x) => write!(f, "Ident {x}"),
            Self::If => write!(f, "If"),
            Self::Illegal => write!(f, "Illegal"),
            Self::Int(x) => write!(f, "Int {x}"),
            Self::Lbrace => write!(f, "Lbrace"),
            Self::Less => write!(f, "Less"),
            Self::Let => write!(f, "Let"),
            Self::Lparen => write!(f, "Lparen"),
            Self::More => write!(f, "More"),
            Self::NotEq => write!(f, "Not Equal"),
            Self::Plus => write!(f, "Plus"),
            Self::Rbrace => write!(f, "Rbrace"),
            Self::Return => write!(f, "Return"),
            Self::Rparen => write!(f, "Rparen"),
            Self::Semicolon => write!(f, "Semicolon"),
            Self::Slash => write!(f, "Slash"),
            Self::Star => write!(f, "Star"),
            Self::True => write!(f, "True"),
        }
    }
}

pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    ch: char,
}

impl Lexer<'_> {
    #[must_use]
    pub fn new(s: &str) -> Lexer {
        let mut lex = Lexer {
            input: s.chars().peekable(),
            ch: '\0',
        };
        lex.read_char();

        lex
    }

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
            '0'..='9' => {
                // TODO: Handle if number was not parsable to int
                let int = self.read_int().unwrap_or(-1);
                Token::Int(int)
            }
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
            ',' => Token::Comma,
            '-' => Token::Minus,
            '{' => Token::Lbrace,
            '<' => Token::Less,
            '(' => Token::Lparen,
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
        let mut build = String::with_capacity(64);
        build.insert(0, self.ch);

        while self.input.peek().unwrap_or(&'\0').is_alphabetic() {
            self.read_char();
            build.push(self.ch);
        }

        build.shrink_to_fit();

        build
    }

    fn read_int(&mut self) -> Result<isize, ParseIntError> {
        let mut build = String::with_capacity(64);
        build.insert(0, self.ch);

        while self.input.peek().unwrap_or(&'\0').is_numeric() {
            self.read_char();
            build.push(self.ch);
        }

        build.shrink_to_fit();

        build.parse()
    }

    fn skip_whitespace(&mut self) {
        while self.ch.is_whitespace() {
            self.read_char();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Lexer, Token};

    #[test]
    fn tokens_working_basic_monkey() {
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
                  10 != 9;";
        let input = String::from(s);
        let mut lex = Lexer::new(&input);

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
            Token::Eof,
        ];

        for token in correct {
            let next = lex.next_tok();
            assert_eq!(next, token);
        }
    }
}
