use std::{fmt::Display, rc::Rc};

/// Tokens which are created by the [`crate::lexer::Lexer`] to be read by the
/// [`crate::parser::Parser`]
#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    Assign,
    Bang,
    Colon,
    Comma,
    Else,
    Eof,
    Eq,
    False,
    Function,
    Ident(Rc<str>),
    If,
    Illegal,
    Int(isize),
    Lbrace,
    Lbracket,
    Less,
    Let,
    Lparen,
    Macro,
    Minus,
    More,
    NotEq,
    Percent,
    Plus,
    Rbrace,
    Rbracket,
    Return,
    Rparen,
    Semicolon,
    Slash,
    Star,
    String(Rc<str>),
    True,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Assign => write!(f, "Assign"),
            Self::Bang => write!(f, "Bang/Exlaim"),
            Self::Colon => write!(f, "Colon"),
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
            Self::Lbracket => write!(f, "Lbracket"),
            Self::Less => write!(f, "Less"),
            Self::Let => write!(f, "Let"),
            Self::Lparen => write!(f, "Lparen"),
            Self::Macro => write!(f, "Macro"),
            Self::Minus => write!(f, "Minus"),
            Self::More => write!(f, "More"),
            Self::NotEq => write!(f, "Not Equal"),
            Self::Percent => write!(f, "Percent"),
            Self::Plus => write!(f, "Plus"),
            Self::Rbrace => write!(f, "Rbrace"),
            Self::Rbracket => write!(f, "Rbracket"),
            Self::Return => write!(f, "Return"),
            Self::Rparen => write!(f, "Rparen"),
            Self::Semicolon => write!(f, "Semicolon"),
            Self::Slash => write!(f, "Slash"),
            Self::Star => write!(f, "Star"),
            Self::String(s) => write!(f, "String {s}"),
            Self::True => write!(f, "True"),
        }
    }
}
