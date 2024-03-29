use std::{cell::RefCell, fmt::Display, rc::Rc};

use crate::{
    ast::{BlockStatement, Expression, Infix, Literal, Prefix, Program, Statement},
    environment::Environment,
    object::Object,
};

// TODO: prettier errors
#[derive(Debug, PartialEq, Eq)]
pub enum EvalErr {
    IncorrectNrOfArgs,
    NotBool,
    NotInt,
    UnboundIdent,
    UnexpectedExpression(String),
}

impl Display for EvalErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedExpression(s) => write!(f, "{s}"),
            Self::UnboundIdent => write!(f, "ident not bound"),
            Self::NotInt => write!(f, "value was not int"),
            Self::NotBool => write!(f, "value was not bool"),
            Self::IncorrectNrOfArgs => write!(f, "Incorrect number of arguments passed"),
        }
    }
}

pub trait PrintResult {
    fn ps(&self) -> String;
}

impl PrintResult for Result<Object, EvalErr> {
    fn ps(&self) -> String {
        match self {
            Ok(o) => format!("{o}"),
            Err(e) => format!("{e}"),
        }
    }
}

pub struct Evaluator {
    env: Rc<RefCell<Environment>>,
}

impl Evaluator {
    pub fn new(env: Rc<RefCell<Environment>>) -> Self {
        Self { env }
    }

    /// Evaluates a [`Program`] to an [`Object`] or [`EvalErr`]
    ///
    /// # Errors
    /// If evaluation was not possible for one of many reasons, returns [`EvalErr`]
    pub fn eval_program(&mut self, p: &Program) -> Result<Object, EvalErr> {
        let mut result = Object::Null;

        for s in &p.statements {
            match self.eval_statement(s)? {
                Object::Return(o) => return Ok(*o),
                other => result = other,
            }
        }

        Ok(result)
    }

    /// Evaluates a [`Statement`] to and [`Object`] or [`EvalErr`]
    ///
    /// # Errors
    /// If evaluation was not possible for one of many reasons, returns [`EvalErr`]
    pub fn eval_statement(&mut self, s: &Statement) -> Result<Object, EvalErr> {
        match s {
            Statement::Expression(e) => self.eval_expression(e),
            Statement::Let { ident, expr } => self.eval_let(ident, expr),
            Statement::Return(e) => self.eval_return(e),
        }
    }

    fn eval_blockstatement(&mut self, bs: &BlockStatement) -> Result<Object, EvalErr> {
        let mut result = Object::Null;

        for s in &bs.statements {
            result = self.eval_statement(s)?;

            if let Object::Return(_) = result {
                return Ok(result);
            }
        }

        Ok(result)
    }

    fn eval_expression(&mut self, e: &Expression) -> Result<Object, EvalErr> {
        match e {
            Expression::Call { args, ident } => self.eval_call(args, ident),
            Expression::Function { body, params } => Ok(self.eval_function(body, params)),
            Expression::Ident(s) => self.eval_ident(s),
            Expression::If { cond, then, alt } => self.eval_if(cond, then, alt),
            Expression::Infix(i, l, r) => self.eval_infix(i, l, r),
            Expression::Literal(l) => Ok(eval_literal(l)),
            Expression::Prefix(p, e) => self.eval_prefix(p, e),
        }
    }

    fn eval_let(&mut self, ident: &str, expr: &Expression) -> Result<Object, EvalErr> {
        let e = self.eval_expression(expr)?;

        self.env.borrow_mut().set(String::from(ident), e);

        Ok(Object::Null)
    }

    fn eval_return(&mut self, e: &Expression) -> Result<Object, EvalErr> {
        Ok(Object::Return(Box::new(self.eval_expression(e)?)))
    }

    fn eval_call(&mut self, args: &Vec<Expression>, ident: &Expression) -> Result<Object, EvalErr> {
        let func = self.eval_expression(ident)?;

        match func {
            Object::Function(params, block, env) => {
                if params.len() != args.len() {
                    return Err(EvalErr::IncorrectNrOfArgs);
                }

                let mut e_args = Vec::with_capacity(args.capacity());

                for a in args {
                    match self.eval_expression(a) {
                        Ok(e) => e_args.push(e),
                        Err(err) => return Err(err),
                    }
                }

                let old_env = Rc::clone(&self.env);
                let fn_env = Rc::new(RefCell::new(Environment::new(Some(Rc::clone(&env)))));

                for (i, p) in params.iter().enumerate() {
                    fn_env.borrow_mut().set(p.clone(), e_args[i].clone());
                }

                self.env = Rc::new(RefCell::new(Environment::new(Some(fn_env))));

                let obj = self.eval_blockstatement(&block);

                self.env = old_env;

                obj
            }
            _ => Err(EvalErr::UnexpectedExpression(String::from(
                "Can only call function",
            ))),
        }
    }

    fn eval_function(&mut self, body: &BlockStatement, params: &[String]) -> Object {
        Object::Function(params.into(), body.clone(), Rc::clone(&self.env))
    }

    fn eval_ident(&mut self, s: &str) -> Result<Object, EvalErr> {
        self.env
            .borrow_mut()
            .get(String::from(s))
            .map_or_else(|| Err(EvalErr::UnboundIdent), Ok)
    }

    fn eval_if(
        &mut self,
        cond: &Expression,
        then: &BlockStatement,
        alt: &BlockStatement,
    ) -> Result<Object, EvalErr> {
        let c = self.eval_expression(cond)?;

        if let Object::Boolean(b) = c {
            if b {
                Ok(self.eval_blockstatement(then)?)
            } else {
                Ok(self.eval_blockstatement(alt)?)
            }
        } else {
            Err(EvalErr::NotBool)
        }
    }

    fn eval_infix(&mut self, i: &Infix, l: &Expression, r: &Expression) -> Result<Object, EvalErr> {
        let le = self.eval_expression(l)?;
        let re = self.eval_expression(r)?;

        match i {
            Infix::Eq => Ok(Object::Boolean(le == re)),
            Infix::NotEq => Ok(Object::Boolean(le != re)),
            _ => infix_lit_cmp(i, &le, &re),
        }
    }

    fn eval_prefix(&mut self, p: &Prefix, e: &Expression) -> Result<Object, EvalErr> {
        let r = self.eval_expression(e)?;

        match p {
            Prefix::Negative => {
                if let Object::Int(i) = r {
                    Ok(Object::Int(-i))
                } else {
                    Err(EvalErr::UnexpectedExpression(String::from(
                        "Can only negate ints",
                    )))
                }
            }
            Prefix::Not => {
                if let Object::Boolean(b) = r {
                    Ok(Object::Boolean(!b))
                } else {
                    Err(EvalErr::UnexpectedExpression(String::from(
                        "Can only NOT booleans",
                    )))
                }
            }
        }
    }
}

fn eval_literal(l: &Literal) -> Object {
    match l {
        Literal::Boolean(b) => Object::Boolean(*b),
        Literal::Int(i) => Object::Int(*i),
        Literal::String(s) => Object::String(s.clone()),
    }
}

fn infix_lit_cmp(i: &Infix, le: &Object, re: &Object) -> Result<Object, EvalErr> {
    match i {
        Infix::Plus => infix_plus(le, re),
        _ => match le {
            Object::Int(lei) => {
                if let Object::Int(rei) = re {
                    match i {
                        Infix::Less => Ok(Object::Boolean(lei < rei)),
                        Infix::Minus => Ok(Object::Int(lei - rei)),
                        Infix::More => Ok(Object::Boolean(lei > rei)),
                        Infix::Slash => Ok(Object::Int(lei / rei)),
                        Infix::Star => Ok(Object::Int(lei * rei)),
                        _ => Err(EvalErr::UnexpectedExpression(format!(
                            "Infix {i} should already have been parsed"
                        ))),
                    }
                } else {
                    Err(EvalErr::NotInt)
                }
            }
            _ => Err(EvalErr::NotInt),
        },
    }
}

fn infix_plus(le: &Object, re: &Object) -> Result<Object, EvalErr> {
    match le {
        Object::String(les) => {
            if let Object::String(res) = re {
                Ok(Object::String(String::from(les) + res))
            } else {
                Err(EvalErr::UnexpectedExpression(String::from(
                    "Can only add string to string",
                )))
            }
        }
        Object::Int(lei) => {
            if let Object::Int(rei) = re {
                Ok(Object::Int(lei + rei))
            } else {
                Err(EvalErr::NotInt)
            }
        }
        _ => Err(EvalErr::UnexpectedExpression(String::from(
            "Can not add to anything but string and int",
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lexer::Lexer, object::Object, parser::Parser};

    #[test]
    fn test_eval_literal() {
        let s = String::from("5; 10; true; false;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 4, "Incorrect number of statements");

        let corr = vec![
            Object::Int(5),
            Object::Int(10),
            Object::Boolean(true),
            Object::Boolean(false),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i]).unwrap(),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_prefix() {
        let s = String::from("!true; !false; !!!false; -5; -400;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 5, "Incorrect number of statements");

        let corr = vec![
            Object::Boolean(false),
            Object::Boolean(true),
            Object::Boolean(true),
            Object::Int(-5),
            Object::Int(-400),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i]).unwrap(),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_infix() {
        let s = String::from(
            "5+5;5-5;5*5;5/5;5>5;5<5;5==5;5!=5;(1<2)==true;(1<2)==false;\"Hello \" + \"World!\";",
        );

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 11, "Incorrect number of statements");

        let corr = vec![
            Object::Int(10),
            Object::Int(0),
            Object::Int(25),
            Object::Int(1),
            Object::Boolean(false),
            Object::Boolean(false),
            Object::Boolean(true),
            Object::Boolean(false),
            Object::Boolean(true),
            Object::Boolean(false),
            Object::String(String::from("Hello World!")),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i]).unwrap(),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_if() {
        let s =
            String::from("if(true){10}; if(false){10}; if(false){5}else{10}; if(true){5}else{10};");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 4, "Incorrect number of statements");

        let corr = vec![
            Object::Int(10),
            Object::Null,
            Object::Int(10),
            Object::Int(5),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i]).unwrap(),
                "Error in statement {}",
                i + 1
            );
        }
    }

    // TODO: Create test that tests programs rather than statements
    // e.g. test "0; return 1; 0;" as => Object::Int(1)
    // helper fn to do let l let mut p let prog would be useful
    #[test]
    fn test_eval_return() {
        let s = String::from(
            "if (true) {9; return 10;}; if (false) {return 10; 9} else {return 9; 10;}; if (true) {9; 10;}; if (true) { if (true) { return 10; } return 1; };",
        );

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 4, "Incorrect number of statements");

        let corr = vec![
            Object::Return(Box::new(Object::Int(10))),
            Object::Return(Box::new(Object::Int(9))),
            Object::Int(10),
            Object::Return(Box::new(Object::Int(10))),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i]).unwrap(),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_err() {
        let s = String::from("true > 5; 5 + true; true + true; -true; if (5) {10;}; if (true) { if (true) { return true + false; } return 5; }; x;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 7, "Incorrect number of statements");

        let corr = vec![
            EvalErr::NotInt,
            EvalErr::NotInt,
            EvalErr::UnexpectedExpression(String::from(
                "Can not add to anything but string and int",
            )),
            EvalErr::UnexpectedExpression(String::from("Can only negate ints")),
            EvalErr::NotBool,
            EvalErr::UnexpectedExpression(String::from(
                "Can not add to anything but string and int",
            )),
            EvalErr::UnboundIdent,
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i]).unwrap_err(),
                "Error in statement {}",
                i + 1
            );
        }
    }

    // TODO: Whole program test here too!
    #[test]
    fn test_eval_let() {
        let s = String::from("let x = 10; x; let y = x + 10; y;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 4, "Incorrect number of statements");

        let corr = vec![Object::Null, Object::Int(10), Object::Null, Object::Int(20)];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i]).unwrap(),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_fn() {
        let s = String::from("fn(){2;}; fn(x){x;}; fn(x, y){x+y;};");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 3, "Incorrect number of statements");

        let corr = vec![
            Object::Function(
                vec![],
                BlockStatement {
                    statements: vec![Statement::Expression(Expression::Literal(Literal::Int(2)))],
                },
                Rc::clone(&e.env),
            ),
            Object::Function(
                vec![String::from("x")],
                BlockStatement {
                    statements: vec![Statement::Expression(Expression::Ident(String::from("x")))],
                },
                Rc::clone(&e.env),
            ),
            Object::Function(
                vec![String::from("x"), String::from("y")],
                BlockStatement {
                    statements: vec![Statement::Expression(Expression::Infix(
                        Infix::Plus,
                        Box::new(Expression::Ident(String::from("x"))),
                        Box::new(Expression::Ident(String::from("y"))),
                    ))],
                },
                Rc::clone(&e.env),
            ),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i]).unwrap(),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_call() {
        let s = String::from("let addone = fn(x) {x + 1;}; addone(9); let adder = fn (x) { fn(y) {x + y} }; let newAdder = adder(9); newAdder(10);");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 5, "Incorrect number of statements");

        let corr = vec![
            Object::Null,
            Object::Int(10),
            Object::Null,
            Object::Null,
            Object::Int(19),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i]).unwrap(),
                "Error in statement {}",
                i + 1
            );
        }
    }
}
