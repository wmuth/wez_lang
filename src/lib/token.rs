use std::fmt::Display;

/// Tokens which are created by the [`crate::lexer::Lexer`] to be read by the
/// [`crate::parser::Parser`]
#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    Assign,
    Bang,
    Comma,
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
    Minus,
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
            Self::Minus => write!(f, "Minus"),
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
