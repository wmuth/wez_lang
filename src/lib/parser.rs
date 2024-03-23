use crate::{
    ast::{Expression, Program, Statement},
    lexer::{Lexer, Token},
};

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    cur_tok: Token,
    peek_tok: Token,
}

impl Parser<'_> {
    pub fn new(mut l: Lexer) -> Parser {
        let first_tok = l.next();
        let second_tok = l.next();

        Parser {
            lexer: l,
            cur_tok: first_tok,
            peek_tok: second_tok,
        }
    }

    pub fn parse_program(mut self) -> Program {
        let mut prog = Program {
            statements: Vec::new(),
        };

        while self.cur_tok != Token::Eof {
            match self.cur_tok {
                Token::Let => self.parse_let(&mut prog),
                Token::Semicolon => println!("Read semicolon"),
                Token::Return => self.parse_return(&mut prog),
                _ => println!("Was not let statement, was: {}", self.cur_tok),
            }

            self.next();
        }

        prog
    }

    // TODO: Dont pass program, append above
    fn parse_let(&mut self, p: &mut Program) {
        // Logic
        // Make sure that we have an ident
        // Get the ident
        // Make sure we have an assign
        // Parse expression on right hand side
        // If next is semicolon, move
        // Return let statement

        self.next();

        // match name
        let mut ident = String::new();
        match &self.cur_tok {
            Token::Ident(s) => {
                ident = s.clone();
            }
            _ => println!("After let was not ident, was: {}", &self.cur_tok),
        }

        self.next();

        // make sure equal sign
        if self.cur_tok != Token::Assign {
            println!("{}", self.cur_tok);
        }

        self.next();

        // make sure val
        let mut val = String::new();
        match &self.cur_tok {
            Token::Int(i) => {
                val = i.to_string();
            }
            _ => println!("After assign was not int, was: {}", &self.cur_tok),
        }

        self.next();

        // push
        p.statements.push(Statement::Let {
            ident,
            expr: Expression::Literal(val),
        });
    }

    fn parse_return(&mut self, p: &mut Program) {
        // Logic
        // cur = return token -> move
        // parse expr to return
        // if next is semicolon, move
        // return return expr
        todo!();
    }

    fn parse_expression(&mut self) {
        todo!();
    }

    fn parse_ident(&mut self) {
        todo!();
    }

    fn next(&mut self) {
        std::mem::swap(&mut self.cur_tok, &mut self.peek_tok);
        self.peek_tok = self.lexer.next();
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{Expression, Statement},
        lexer::Lexer,
    };

    use super::Parser;

    #[test]
    fn test_let_statement() {
        let s = String::from(
            "let x = 5;
             let y = 10;
             let z = 1234;",
        );

        let l = Lexer::new(&s);
        let p = Parser::new(l);
        let prog = p.parse_program();

        // Correct length
        assert_eq!(prog.statements.len(), 3);

        // Correnct idents
        let corr = vec!["x", "y", "z"];
        for (i, v) in corr.iter().enumerate() {
            match &prog.statements[i] {
                Statement::Let { ident, .. } => {
                    assert_eq!(v, &ident)
                }
            }
        }

        // Correct values
        let corr = vec!["5", "10", "1234"];
        for (i, v) in corr.iter().enumerate() {
            match &prog.statements[i] {
                Statement::Let { expr, .. } => match expr {
                    Expression::Literal(val) => {
                        assert_eq!(v, val)
                    }
                },
            }
        }
    }
}
