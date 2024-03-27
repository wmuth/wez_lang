use std::fmt::Display;

use crate::{
    ast::{BlockStatement, Expression, Infix, Literal, Precedence, Prefix, Program, Statement},
    lexer::Lexer,
    token::Token,
};

/// The errors the [`Parser`] can produce
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

/// The parser struct which parses [`Token`] from the [`Lexer`] into [`Statement`]
pub struct Parser<'a> {
    cur_tok: Token,
    errors: Vec<ParseError>,
    lexer: Lexer<'a>,
    peek_tok: Token,
}

impl Parser<'_> {
    /// Creates the parser
    ///
    /// # Parameters
    /// - `l` the [`Lexer`] to take tokens from
    #[must_use]
    pub fn new(mut l: Lexer) -> Parser {
        let first_tok = l.next_tok();
        let second_tok = l.next_tok();

        Parser {
            cur_tok: first_tok,
            errors: Vec::new(),
            lexer: l,
            peek_tok: second_tok,
        }
    }

    /// Parses the [`Lexer`] input to a [`Program`]
    #[must_use]
    pub fn parse_program(&mut self) -> Program {
        let mut prog = Program {
            statements: Vec::new(),
        };

        while self.cur_tok != Token::Eof {
            self.parse_stmt_type()
                .map_or_else(|e| self.errors.push(e), |s| prog.statements.push(s));
            self.next();
        }

        prog
    }

    /// Returns the errors the [`Parser`] produced
    #[must_use]
    pub const fn get_errors(&self) -> &Vec<ParseError> {
        &self.errors
    }

    fn parse_stmt_type(&mut self) -> Result<Statement, ParseError> {
        match self.cur_tok {
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
                self.cur_tok,
            )));
        };
        self.next();

        if self.cur_tok != Token::Assign {
            return Err(ParseError::UnexpectedToken(format!(
                "After ident was not assign, was {}",
                self.cur_tok,
            )));
        }
        self.next();

        let expr = self.parse_expression(&Precedence::Lowest)?;
        self.next();

        if self.peek_tok == Token::Semicolon {
            self.next();
        }

        Ok(Statement::Let { ident, expr })
    }

    fn parse_return(&mut self) -> Result<Statement, ParseError> {
        self.next();

        let expr = self.parse_expression(&Precedence::Lowest)?;
        self.next();

        if self.peek_tok == Token::Semicolon {
            self.next();
        }

        Ok(Statement::Return(expr))
    }

    fn parse_expr_stmt(&mut self) -> Result<Statement, ParseError> {
        let s = Statement::Expression(self.parse_expression(&Precedence::Lowest)?);

        if self.peek_tok == Token::Semicolon {
            self.next();
        }

        Ok(s)
    }

    fn parse_expression(&mut self, p: &Precedence) -> Result<Expression, ParseError> {
        let mut l = match self.cur_tok {
            Token::Bang | Token::Minus => self.parse_prefix(),
            Token::Function => self.parse_fn(),
            Token::Ident(_) => self.parse_ident(),
            Token::If => self.parse_if(),
            Token::Int(_) | Token::False | Token::True => self.parse_literal(),
            Token::Lparen => self.parse_group(),
            _ => Err(ParseError::UnexpectedToken(format!(
                "No prefix parser for: {}",
                self.cur_tok
            ))),
        }?;

        while self.peek_tok != Token::Semicolon && *p < token_to_precedence(&self.peek_tok) {
            match self.peek_tok {
                Token::Eq
                | Token::Less
                | Token::Minus
                | Token::More
                | Token::NotEq
                | Token::Plus
                | Token::Slash
                | Token::Star => {
                    self.next();
                    l = self.parse_infix(l)?;
                }
                Token::Lparen => {
                    self.next();
                    l = self.parse_call(l)?;
                }
                _ => break,
            }
        }

        Ok(l)
    }

    fn parse_ident(&self) -> Result<Expression, ParseError> {
        match &self.cur_tok {
            Token::Ident(i) => Ok(Expression::Ident(i.clone())),
            _ => Err(ParseError::UnexpectedToken(format!(
                "Exptected to parse an ident, tried to parse {}",
                self.cur_tok
            ))),
        }
    }

    fn parse_literal(&self) -> Result<Expression, ParseError> {
        match self.cur_tok {
            Token::False => Ok(Expression::Literal(Literal::Boolean(false))),
            Token::Int(i) => Ok(Expression::Literal(Literal::Int(i))),
            Token::True => Ok(Expression::Literal(Literal::Boolean(true))),
            _ => Err(ParseError::UnexpectedToken(format!(
                "Exptected to parse a literal, tried to parse {}",
                self.cur_tok
            ))),
        }
    }

    fn parse_prefix(&mut self) -> Result<Expression, ParseError> {
        let p = match self.cur_tok {
            Token::Bang => Ok(Prefix::Not),
            Token::Minus => Ok(Prefix::Negative),
            _ => Err(ParseError::UnexpectedToken(String::new())),
        }?;

        self.next();

        Ok(Expression::Prefix(
            p,
            Box::new(self.parse_expression(&Precedence::Prefix)?),
        ))
    }

    fn parse_infix(&mut self, l: Expression) -> Result<Expression, ParseError> {
        let infix = match self.cur_tok {
            Token::Eq => Ok(Infix::Eq),
            Token::Less => Ok(Infix::Less),
            Token::Minus => Ok(Infix::Minus),
            Token::More => Ok(Infix::More),
            Token::NotEq => Ok(Infix::NotEq),
            Token::Plus => Ok(Infix::Plus),
            Token::Slash => Ok(Infix::Slash),
            Token::Star => Ok(Infix::Star),
            _ => Err(ParseError::UnexpectedToken(format!(
                "No infix parser for {}",
                self.cur_tok
            ))),
        }?;

        let precedence = token_to_precedence(&self.cur_tok);
        self.next();

        Ok(Expression::Infix(
            infix,
            Box::new(l),
            Box::new(self.parse_expression(&precedence)?),
        ))
    }

    fn parse_group(&mut self) -> Result<Expression, ParseError> {
        self.next();

        let exp = self.parse_expression(&Precedence::Lowest)?;

        match self.peek_tok {
            Token::Rparen => {
                self.next();
                Ok(exp)
            }
            _ => Err(ParseError::UnexpectedToken(String::from(
                "Missing ) in group statement",
            ))),
        }
    }

    fn parse_if(&mut self) -> Result<Expression, ParseError> {
        if self.peek_tok != Token::Lparen {
            return Err(ParseError::UnexpectedToken(String::from(
                "If not followed by (",
            )));
        }
        self.next();
        self.next();

        let cond = self.parse_expression(&Precedence::Lowest)?;

        if self.peek_tok != Token::Rparen {
            return Err(ParseError::UnexpectedToken(String::from(
                "If condition not followed by )",
            )));
        }
        self.next();

        if self.peek_tok != Token::Lbrace {
            return Err(ParseError::UnexpectedToken(String::from(
                "Block should start with {",
            )));
        }
        self.next();

        let then = self.parse_block()?;

        let alt = if self.peek_tok == Token::Else {
            self.next();
            if self.peek_tok == Token::Lbrace {
                self.next();
                Ok(self.parse_block()?)
            } else {
                Err(ParseError::UnexpectedToken(String::from(
                    "Block statement should start with {",
                )))
            }
        } else {
            Ok(BlockStatement { stmts: vec![] })
        }?;

        Ok(Expression::If {
            cond: Box::new(cond),
            alt,
            then,
        })
    }

    fn parse_block(&mut self) -> Result<BlockStatement, ParseError> {
        self.next();

        let mut stmts = vec![];

        while self.cur_tok != Token::Rbrace && self.cur_tok != Token::Eof {
            stmts.push(self.parse_stmt_type()?);
            self.next();
        }

        Ok(BlockStatement { stmts })
    }

    fn parse_fn(&mut self) -> Result<Expression, ParseError> {
        if self.peek_tok != Token::Lparen {
            return Err(ParseError::UnexpectedToken(String::from(
                "Exptected ( after fn",
            )));
        }
        self.next();

        let params = self.parse_params()?;

        if self.peek_tok != Token::Lbrace {
            return Err(ParseError::UnexpectedToken(String::from(
                "Exptected start of body { after fn params )",
            )));
        }
        self.next();

        let body = self.parse_block()?;

        Ok(Expression::Function { body, params })
    }

    fn parse_params(&mut self) -> Result<Vec<String>, ParseError> {
        self.next();
        let mut params = vec![];

        while self.cur_tok != Token::Rparen {
            match &self.cur_tok {
                Token::Ident(i) => params.push(i.clone()),
                Token::Comma => (),
                _ => {
                    return Err(ParseError::UnexpectedToken(String::from(
                        "Expected only idents and , in params",
                    )));
                }
            }

            self.next();
        }

        Ok(params)
    }

    fn parse_call(&mut self, l: Expression) -> Result<Expression, ParseError> {
        Ok(Expression::Call {
            args: self.parse_args()?,
            ident: Box::new(l),
        })
    }

    fn parse_args(&mut self) -> Result<Vec<Expression>, ParseError> {
        let mut args = vec![];

        if self.peek_tok == Token::Rparen {
            self.next();
            return Ok(args);
        }
        self.next();

        args.push(self.parse_expression(&Precedence::Lowest)?);

        while self.peek_tok == Token::Comma {
            self.next();
            self.next();
            args.push(self.parse_expression(&Precedence::Lowest)?);
        }

        match self.peek_tok {
            Token::Rparen => {
                self.next();
                Ok(args)
            }
            _ => Err(ParseError::UnexpectedToken(String::from(
                "Expected ) at end of args",
            ))),
        }
    }

    fn next(&mut self) {
        std::mem::swap(&mut self.cur_tok, &mut self.peek_tok);
        self.peek_tok = self.lexer.next_tok();
    }
}

const fn token_to_precedence(t: &Token) -> Precedence {
    match t {
        Token::Eq | Token::NotEq => Precedence::Equals,
        Token::Less | Token::More => Precedence::LessMore,
        Token::Lparen => Precedence::Call,
        Token::Plus | Token::Minus => Precedence::Sum,
        Token::Slash | Token::Star => Precedence::Product,
        _ => Precedence::Lowest,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{BlockStatement, Expression, Infix, Literal, Prefix, Statement},
        lexer::Lexer,
    };

    use super::Parser;

    #[test]
    fn test_let_statement() {
        let s = String::from(
            "let x = 5;
             let y = 10;
             let z = 1234;
             let x = y + z;
             let y = !z;",
        );

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 5, "Incorrect number of statements");

        let corr = vec![
            Statement::Let {
                ident: String::from("x"),
                expr: Expression::Literal(Literal::Int(5)),
            },
            Statement::Let {
                ident: String::from("y"),
                expr: Expression::Literal(Literal::Int(10)),
            },
            Statement::Let {
                ident: String::from("z"),
                expr: Expression::Literal(Literal::Int(1234)),
            },
            Statement::Let {
                ident: String::from("x"),
                expr: Expression::Infix(
                    Infix::Plus,
                    Box::new(Expression::Ident(String::from("y"))),
                    Box::new(Expression::Ident(String::from("z"))),
                ),
            },
            Statement::Let {
                ident: String::from("y"),
                expr: Expression::Prefix(
                    Prefix::Not,
                    Box::new(Expression::Ident(String::from("z"))),
                ),
            },
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(*v, prog.statements[i], "Error in statement {}", i + 1);
        }
    }

    #[test]
    fn test_return_statement() {
        let s = String::from("return 5; return a - b;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 2, "Incorrect number of statements");

        let corr = vec![
            Statement::Return(Expression::Literal(Literal::Int(5))),
            Statement::Return(Expression::Infix(
                Infix::Minus,
                Box::new(Expression::Ident(String::from("a"))),
                Box::new(Expression::Ident(String::from("b"))),
            )),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(*v, prog.statements[i], "Error in statement {}", i + 1);
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

        let corr = vec![
            Statement::Expression(Expression::Ident(String::from("test"))),
            Statement::Expression(Expression::Ident(String::from("foobar"))),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(*v, prog.statements[i], "Error in statement {}", i + 1);
        }
    }

    #[test]
    fn test_literal_expr() {
        let s = String::from("1337; 120; true; false;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 4, "Incorrect number of statements");

        let corr = vec![
            Statement::Expression(Expression::Literal(Literal::Int(1337))),
            Statement::Expression(Expression::Literal(Literal::Int(120))),
            Statement::Expression(Expression::Literal(Literal::Boolean(true))),
            Statement::Expression(Expression::Literal(Literal::Boolean(false))),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(*v, prog.statements[i], "Error in statement {}", i + 1);
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

        let corr = vec![
            Statement::Expression(Expression::Prefix(
                Prefix::Negative,
                Box::new(Expression::Literal(Literal::Int(5))),
            )),
            Statement::Expression(Expression::Prefix(
                Prefix::Not,
                Box::new(Expression::Prefix(
                    Prefix::Not,
                    Box::new(Expression::Ident(String::from("foo"))),
                )),
            )),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(*v, prog.statements[i], "Error in statement {}", i + 1);
        }
    }

    #[test]
    fn test_parse_infix_expr() {
        let s = String::from("5+5;5-5;5*5;5/5;5>5;5<5;5==5;5!=5;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 8, "Incorrect number of statements");

        let corr = vec![
            Statement::Expression(Expression::Infix(
                Infix::Plus,
                Box::new(Expression::Literal(Literal::Int(5))),
                Box::new(Expression::Literal(Literal::Int(5))),
            )),
            Statement::Expression(Expression::Infix(
                Infix::Minus,
                Box::new(Expression::Literal(Literal::Int(5))),
                Box::new(Expression::Literal(Literal::Int(5))),
            )),
            Statement::Expression(Expression::Infix(
                Infix::Star,
                Box::new(Expression::Literal(Literal::Int(5))),
                Box::new(Expression::Literal(Literal::Int(5))),
            )),
            Statement::Expression(Expression::Infix(
                Infix::Slash,
                Box::new(Expression::Literal(Literal::Int(5))),
                Box::new(Expression::Literal(Literal::Int(5))),
            )),
            Statement::Expression(Expression::Infix(
                Infix::More,
                Box::new(Expression::Literal(Literal::Int(5))),
                Box::new(Expression::Literal(Literal::Int(5))),
            )),
            Statement::Expression(Expression::Infix(
                Infix::Less,
                Box::new(Expression::Literal(Literal::Int(5))),
                Box::new(Expression::Literal(Literal::Int(5))),
            )),
            Statement::Expression(Expression::Infix(
                Infix::Eq,
                Box::new(Expression::Literal(Literal::Int(5))),
                Box::new(Expression::Literal(Literal::Int(5))),
            )),
            Statement::Expression(Expression::Infix(
                Infix::NotEq,
                Box::new(Expression::Literal(Literal::Int(5))),
                Box::new(Expression::Literal(Literal::Int(5))),
            )),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(*v, prog.statements[i], "Error in statement {}", i + 1);
        }
    }

    #[test]
    fn test_group_expr() {
        let s = String::from("1 + 2 / 3; (1 + 2) / 3;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 2, "Incorrect number of statements");

        let corr = vec![
            Statement::Expression(Expression::Infix(
                Infix::Plus,
                Box::new(Expression::Literal(Literal::Int(1))),
                Box::new(Expression::Infix(
                    Infix::Slash,
                    Box::new(Expression::Literal(Literal::Int(2))),
                    Box::new(Expression::Literal(Literal::Int(3))),
                )),
            )),
            Statement::Expression(Expression::Infix(
                Infix::Slash,
                Box::new(Expression::Infix(
                    Infix::Plus,
                    Box::new(Expression::Literal(Literal::Int(1))),
                    Box::new(Expression::Literal(Literal::Int(2))),
                )),
                Box::new(Expression::Literal(Literal::Int(3))),
            )),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(*v, prog.statements[i], "Error in statement {}", i + 1);
        }
    }

    #[test]
    fn test_if_expr() {
        let s = String::from("if (x < y) { x } if (x) { x } else { y }");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 2, "Incorrect number of statements");

        let corr = vec![
            Statement::Expression(Expression::If {
                cond: Box::new(Expression::Infix(
                    Infix::Less,
                    Box::new(Expression::Ident(String::from("x"))),
                    Box::new(Expression::Ident(String::from("y"))),
                )),
                then: BlockStatement {
                    stmts: vec![Statement::Expression(Expression::Ident(String::from("x")))],
                },
                alt: BlockStatement { stmts: vec![] },
            }),
            Statement::Expression(Expression::If {
                cond: Box::new(Expression::Ident(String::from("x"))),
                then: BlockStatement {
                    stmts: vec![Statement::Expression(Expression::Ident(String::from("x")))],
                },
                alt: BlockStatement {
                    stmts: vec![Statement::Expression(Expression::Ident(String::from("y")))],
                },
            }),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(*v, prog.statements[i], "Error in statement {}", i + 1);
        }
    }

    #[test]
    fn test_fn_lit() {
        let s = String::from("fn(){1};fn(x){x};fn(x, y){ x + y };");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 3, "Incorrect number of statements");

        let corr = vec![
            Statement::Expression(Expression::Function {
                body: BlockStatement {
                    stmts: vec![Statement::Expression(Expression::Literal(Literal::Int(1)))],
                },
                params: vec![],
            }),
            Statement::Expression(Expression::Function {
                body: BlockStatement {
                    stmts: vec![Statement::Expression(Expression::Ident(String::from("x")))],
                },
                params: vec![String::from("x")],
            }),
            Statement::Expression(Expression::Function {
                body: BlockStatement {
                    stmts: vec![Statement::Expression(Expression::Infix(
                        Infix::Plus,
                        Box::new(Expression::Ident(String::from("x"))),
                        Box::new(Expression::Ident(String::from("y"))),
                    ))],
                },
                params: vec![String::from("x"), String::from("y")],
            }),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(*v, prog.statements[i], "Error in statement {}", i + 1);
        }
    }

    #[test]
    fn test_call_expr() {
        let s = String::from("next(); remove(x); add(1, 2*3, 4+5);");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 3, "Incorrect number of statements");

        let corr = vec![
            Statement::Expression(Expression::Call {
                args: vec![],
                ident: Box::new(Expression::Ident(String::from("next"))),
            }),
            Statement::Expression(Expression::Call {
                args: vec![Expression::Ident(String::from("x"))],
                ident: Box::new(Expression::Ident(String::from("remove"))),
            }),
            Statement::Expression(Expression::Call {
                args: vec![
                    Expression::Literal(Literal::Int(1)),
                    Expression::Infix(
                        Infix::Star,
                        Box::new(Expression::Literal(Literal::Int(2))),
                        Box::new(Expression::Literal(Literal::Int(3))),
                    ),
                    Expression::Infix(
                        Infix::Plus,
                        Box::new(Expression::Literal(Literal::Int(4))),
                        Box::new(Expression::Literal(Literal::Int(5))),
                    ),
                ],
                ident: Box::new(Expression::Ident(String::from("add"))),
            }),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(*v, prog.statements[i], "Error in statement {}", i + 1);
        }
    }
}
