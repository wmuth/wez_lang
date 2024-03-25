use std::fmt::Display;

use crate::{
    ast::{Expression, Literal, Precedence, Prefix, Program, Statement},
    lexer::{Lexer, Token},
};

pub enum ParseError {
    UnexpectedToken(String),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedToken(s) => write!(f, "{s}"),
        }
    }
}

pub struct Parser<'a> {
    cur_tok: Token,
    errors: Vec<ParseError>,
    lexer: Lexer<'a>,
    peek_tok: Token,
}

impl Parser<'_> {
    #[must_use]
    pub fn new(mut l: Lexer) -> Parser {
        let first_tok = l.next_tok();
        let second_tok = l.next_tok();

        Parser {
            lexer: l,
            cur_tok: first_tok,
            peek_tok: second_tok,
            errors: vec![],
        }
    }

    #[must_use]
    pub fn parse_program(&mut self) -> Program {
        let mut prog = Program {
            statements: Vec::new(),
        };

        while self.cur_tok != Token::Eof {
            self.which_parse(&self.cur_tok.clone())
                .map_or_else(|e| self.errors.push(e), |s| prog.statements.push(s));
            self.next();
        }

        prog
    }

    #[must_use]
    pub const fn get_errors(&self) -> &Vec<ParseError> {
        &self.errors
    }

    fn which_parse(&mut self, t: &Token) -> Result<Statement, ParseError> {
        match t {
            Token::Let => self.parse_let(),
            Token::Return => self.parse_return(),
            _ => self.parse_expr_stmt(),
        }
    }

    fn parse_let(&mut self) -> Result<Statement, ParseError> {
        self.next();

        let ident = if let Token::Ident(s) = &self.cur_tok {
            s.clone()
        } else {
            return Err(ParseError::UnexpectedToken(format!(
                "After let was not an ident, was {}",
                &self.cur_tok,
            )));
        };
        self.next();

        if self.cur_tok != Token::Assign {
            return Err(ParseError::UnexpectedToken(String::from(
                "After ident was not assign",
            )));
        }
        self.next();

        let expr = self.parse_expression(Precedence::Lowest)?;
        self.next();

        if self.peek_tok == Token::Semicolon {
            self.next();
        }

        Ok(Statement::Let { ident, expr })
    }

    fn parse_return(&mut self) -> Result<Statement, ParseError> {
        self.next();

        let expr = self.parse_expression(Precedence::Lowest)?;
        self.next();

        if self.peek_tok == Token::Semicolon {
            self.next();
        }

        Ok(Statement::Return { expr })
    }

    fn parse_expr_stmt(&mut self) -> Result<Statement, ParseError> {
        let s = Statement::Expression {
            expr: self.parse_expression(Precedence::Lowest)?,
        };
        self.next();

        if self.peek_tok == Token::Semicolon {
            self.next();
        }

        Ok(s)
    }

    fn parse_expression(&mut self, p: Precedence) -> Result<Expression, ParseError> {
        let prefix = match self.cur_tok {
            Token::Bang | Token::Minus => self.parse_prefix(),
            Token::Ident(_) => self.parse_ident(),
            Token::Int(_) => self.parse_int(),
            _ => Err(ParseError::UnexpectedToken(format!(
                "No prefix parser for: {}",
                self.cur_tok
            ))),
        }?;

        Ok(prefix)
    }

    fn parse_ident(&mut self) -> Result<Expression, ParseError> {
        match &self.cur_tok {
            Token::Ident(i) => Ok(Expression::Ident(i.clone())),
            _ => Err(ParseError::UnexpectedToken(String::new())),
        }
    }

    fn parse_int(&mut self) -> Result<Expression, ParseError> {
        match &self.cur_tok {
            Token::Int(i) => Ok(Expression::Literal(Literal::Int(*i))),
            _ => Err(ParseError::UnexpectedToken(String::new())),
        }
    }

    fn parse_prefix(&mut self) -> Result<Expression, ParseError> {
        let p = match &self.cur_tok {
            Token::Bang => Ok(Prefix::Not),
            Token::Minus => Ok(Prefix::Negative),
            _ => Err(ParseError::UnexpectedToken(String::new())),
        }?;

        self.next();

        Ok(Expression::Prefix(
            p,
            Box::new(self.parse_expression(Precedence::Prefix)?),
        ))
    }

    fn next(&mut self) {
        std::mem::swap(&mut self.cur_tok, &mut self.peek_tok);
        self.peek_tok = self.lexer.next_tok();
    }
}

#[cfg(test)]
mod tests {
    use core::panic;

    use crate::{
        ast::{Expression, Literal, Prefix, Statement},
        lexer::Lexer,
    };

    use super::Parser;

    #[test]
    fn test_let_statement_int() {
        let s = String::from(
            "let x = 5;
             let y = 10;
             let z = 1234;",
        );

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 3, "Incorrect number of statements");

        let corr = vec!["x", "y", "z"];
        for (i, v) in corr.iter().enumerate() {
            match &prog.statements[i] {
                Statement::Let { ident, .. } => {
                    assert_eq!(v, &ident, "Incorrect ident")
                }
                _ => {}
            }
        }

        let corr = vec![5, 10, 1234];
        for (i, v) in corr.iter().enumerate() {
            match &prog.statements[i] {
                Statement::Return { expr } => match expr {
                    Expression::Literal(l) => match l {
                        Literal::Int(i) => assert_eq!(v, i, "Incorrect value"),
                        _ => {}
                    },
                    _ => {}
                },
                _ => {}
            }
        }
    }

    #[test]
    fn test_return_statement_int() {
        let s = String::from("return 5; return 10;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 2, "Incorrect number of statements");

        let corr = vec![5, 10];
        for (i, v) in corr.iter().enumerate() {
            match &prog.statements[i] {
                Statement::Return { expr } => match expr {
                    Expression::Literal(l) => match l {
                        Literal::Int(i) => assert_eq!(v, i, "Incorrect value"),
                        _ => {}
                    },
                    _ => {}
                },
                _ => {}
            }
        }
    }

    #[test]
    fn test_ident_expr() {
        let s = String::from("test; foobar;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 2, "Incorrect number of statements");

        if let Statement::Expression {
            expr: Expression::Ident(c),
        } = &prog.statements[0]
        {
            assert_eq!(&String::from("test"), c, "Ident was incorrect");
        } else {
            panic!("Statment not of type expression!");
        }

        if let Statement::Expression {
            expr: Expression::Ident(c),
        } = &prog.statements[1]
        {
            assert_eq!(&String::from("foobar"), c, "Ident was incorrect");
        } else {
            panic!("Statment not of type expression!");
        }
    }

    #[test]
    fn test_int_expr() {
        let s = String::from("1337; 120;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 2, "Incorrect number of statements");

        if let Statement::Expression {
            expr: Expression::Literal(Literal::Int(i)),
        } = &prog.statements[0]
        {
            assert_eq!(*i, 1337, "Value incorrect");
        } else {
            panic!("Statment not of type expression!");
        }

        if let Statement::Expression {
            expr: Expression::Literal(Literal::Int(i)),
        } = &prog.statements[1]
        {
            assert_eq!(*i, 120, "Value incorrect");
        } else {
            panic!("Statment not of type expression!");
        }
    }

    #[test]
    fn test_parse_prefix_expr() {
        let s = String::from("-5; !!foo;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 2, "Incorrect number of statements");

        if let Statement::Expression {
            expr: Expression::Prefix(Prefix::Negative, b),
        } = &prog.statements[0]
        {
            if let Expression::Literal(Literal::Int(i)) = **b {
                assert_eq!(i, 5);
            } else {
                panic!("Expression of wrong type!");
            }
        } else {
            panic!("Statement of wrong type!");
        }

        if let Statement::Expression {
            expr: Expression::Prefix(Prefix::Not, b2),
        } = &prog.statements[1]
        {
            if let Expression::Prefix(Prefix::Not, b3) = &**b2 {
                if let Expression::Ident(s) = &**b3 {
                    assert_eq!(*s, String::from("foo"));
                }
            } else {
                panic!("Expression of wrong type!");
            }
        } else {
            panic!("Statement of wrong type!");
        }
    }
}
