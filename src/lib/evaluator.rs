use std::{cell::RefCell, collections::HashMap, fmt::Display, rc::Rc};

use crate::{
    ast::{BlockStatement, Expression, Infix, Literal, Prefix, Program, Statement},
    builtins::BuiltinError,
    environment::Environment,
    object::Object,
};

/// The different errors which the [`Evaluator`] can produce
#[derive(Debug, PartialEq, Eq)]
pub enum EvalErr {
    BuiltinError(String),
    IncorrectNrOfArgs(usize),
    NotBool(Object),
    NotInMap(Object),
    NotInt(Object),
    OutOfRange(isize),
    UnboundIdent(String),
    UnexpectedExpression(String),
}

impl Display for EvalErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BuiltinError(s) => write!(f, "BuiltinError {s}"),
            Self::NotBool(o) => write!(f, "Value {o} was not bool"),
            Self::NotInMap(o) => write!(f, "Key {o} not in map"),
            Self::NotInt(o) => write!(f, "Value {o} was not int"),
            Self::OutOfRange(i) => write!(f, "Index {i} out of range"),
            Self::UnboundIdent(s) => write!(f, "Ident {s} not bound"),
            Self::UnexpectedExpression(s) => write!(f, "{s}"),
            Self::IncorrectNrOfArgs(nr) => {
                write!(f, "Incorrect number of arguments passed. Expected {nr}")
            }
        }
    }
}

impl From<BuiltinError> for EvalErr {
    fn from(value: BuiltinError) -> Self {
        Self::BuiltinError(format!("{value}"))
    }
}

/// The evaluator which evaluates our AST
pub struct Evaluator {
    env: Rc<RefCell<Environment>>,
}

impl Evaluator {
    #[must_use]
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
            Expression::Index(a, i) => self.eval_index(a, i),
            Expression::If { cond, then, alt } => self.eval_if(cond, then, alt),
            Expression::Infix(i, l, r) => self.eval_infix(i, l, r),
            Expression::Literal(l) => self.eval_literal(l),
            Expression::Prefix(p, e) => self.eval_prefix(p, e),
        }
    }

    fn eval_let(&mut self, ident: &Rc<str>, expr: &Expression) -> Result<Object, EvalErr> {
        let e = self.eval_expression(expr)?;

        self.env.borrow_mut().set(Rc::clone(ident), Rc::from(e));

        Ok(Object::Null)
    }

    fn eval_return(&mut self, e: &Expression) -> Result<Object, EvalErr> {
        Ok(Object::Return(Box::new(self.eval_expression(e)?)))
    }

    fn eval_call(&mut self, args: &[Expression], ident: &Expression) -> Result<Object, EvalErr> {
        let func = self.eval_expression(ident)?;

        match func {
            Object::Function(params, block, env) => {
                if params.len() != args.len() {
                    return Err(EvalErr::IncorrectNrOfArgs(params.len()));
                }

                let e_args = args
                    .iter()
                    .map(|a| self.eval_expression(a))
                    .collect::<Result<Vec<Object>, EvalErr>>()?;

                let e_args: Vec<Rc<Object>> = e_args.into_iter().map(Rc::new).collect();

                let old_env = Rc::clone(&self.env);
                let fn_env = Rc::new(RefCell::new(Environment::new(Some(Rc::clone(&env)))));

                for (i, p) in params.iter().enumerate() {
                    if let Some(v) = e_args.get(i) {
                        fn_env.borrow_mut().set(Rc::clone(p), Rc::clone(v));
                    }
                }

                self.env = Rc::new(RefCell::new(Environment::new(Some(fn_env))));

                let obj = self.eval_blockstatement(&block);

                self.env = old_env;

                obj
            }
            Object::Builtin(f, nr_a) => {
                if let Some(nr) = nr_a {
                    if nr as usize != args.len() {
                        return Err(EvalErr::IncorrectNrOfArgs(nr as usize));
                    }
                }

                let e_args = args
                    .iter()
                    .map(|a| self.eval_expression(a))
                    .collect::<Result<Vec<Object>, EvalErr>>()?;

                Ok(f(&e_args)?)
            }
            _ => Err(EvalErr::UnexpectedExpression(String::from(
                "Can only call function",
            ))),
        }
    }

    fn eval_function(&mut self, body: &BlockStatement, params: &[Rc<str>]) -> Object {
        Object::Function(params.into(), body.clone(), Rc::clone(&self.env))
    }

    fn eval_ident(&mut self, s: &Rc<str>) -> Result<Object, EvalErr> {
        self.env.borrow_mut().get(s).map_or_else(
            || Err(EvalErr::UnboundIdent(String::from(&*s.to_string()))),
            |v| Ok(Rc::unwrap_or_clone(v)),
        )
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
            Err(EvalErr::NotBool(c))
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

    fn eval_arr(&mut self, a: &[Expression]) -> Result<Object, EvalErr> {
        let mut e = Vec::with_capacity(a.len());

        for i in a {
            match self.eval_expression(i) {
                Ok(o) => e.push(o),
                Err(err) => return Err(err),
            }
        }

        Ok(Object::List(e))
    }

    fn eval_index(&mut self, a: &Expression, i: &Expression) -> Result<Object, EvalErr> {
        let ae = self.eval_expression(a)?;

        match ae {
            Object::List(a) => {
                let ie = self.eval_expression(i)?;

                if let Object::Int(idx) = ie {
                    let uidxr = TryInto::<usize>::try_into(idx);
                    let uidx = uidxr.map_or_else(|_| Err(EvalErr::OutOfRange(idx)), Ok)?;

                    a.get(uidx)
                        .map_or(Err(EvalErr::OutOfRange(idx)), |o| Ok(o.clone()))
                } else {
                    Err(EvalErr::UnexpectedExpression(String::from(
                        "Can only index with int",
                    )))
                }
            }
            Object::Map(hm) => {
                let ie = self.eval_expression(i)?;

                hm.get(&ie)
                    .map_or(Err(EvalErr::NotInMap(ie)), |o| Ok(o.clone()))
            }
            _ => Err(EvalErr::UnexpectedExpression(String::from(
                "Can only index array or map",
            ))),
        }
    }

    fn eval_literal(&mut self, l: &Literal) -> Result<Object, EvalErr> {
        match l {
            Literal::List(a) => self.eval_arr(a),
            Literal::Boolean(b) => Ok(Object::Boolean(*b)),
            Literal::Int(i) => Ok(Object::Int(*i)),
            Literal::Map(v) => self.eval_map(v),
            Literal::String(s) => Ok(Object::String(s.clone())),
        }
    }

    fn eval_map(&mut self, v: &[(Expression, Expression)]) -> Result<Object, EvalErr> {
        let mut map = HashMap::new();

        for (ke, ve) in v {
            let k = self.eval_expression(ke)?;
            let v = self.eval_expression(ve)?;
            map.insert(k, v);
        }

        Ok(Object::Map(map))
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
                        Infix::Percent => Ok(Object::Int(lei % rei)),
                        Infix::Slash => Ok(Object::Int(lei / rei)),
                        Infix::Star => Ok(Object::Int(lei * rei)),
                        _ => Err(EvalErr::UnexpectedExpression(format!(
                            "Infix {i} should already have been parsed"
                        ))),
                    }
                } else {
                    Err(EvalErr::NotInt(re.clone()))
                }
            }
            _ => Err(EvalErr::NotInt(le.clone())),
        },
    }
}

fn infix_plus(le: &Object, re: &Object) -> Result<Object, EvalErr> {
    match le {
        Object::String(les) => {
            if let Object::String(res) = re {
                Ok(Object::String(Rc::from(les.to_string() + res)))
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
                Err(EvalErr::NotInt(re.clone()))
            }
        }
        _ => Err(EvalErr::UnexpectedExpression(String::from(
            "Can not add to anything but string and int",
        ))),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::{builtins::get_builtin_fns, lexer::Lexer, object::Object, parser::Parser};

    #[test]
    fn test_eval_literal() {
        let s = String::from("5; 10; true; false;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 4, "Incorrect number of statements");

        let corr = [
            Object::Int(5),
            Object::Int(10),
            Object::Boolean(true),
            Object::Boolean(false),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
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

        let corr = [
            Object::Boolean(false),
            Object::Boolean(true),
            Object::Boolean(true),
            Object::Int(-5),
            Object::Int(-400),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_infix() {
        let s = String::from(
            "5+5;5-5;5*5;5/5;5>5;5<5;5==5;5!=5;(1<2)==true;(1<2)==false;\"Hello \" + \"World!\"; 9%2;",
        );

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 12, "Incorrect number of statements");

        let corr = [
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
            Object::String(Rc::from("Hello World!")),
            Object::Int(1),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
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

        let corr = [
            Object::Int(10),
            Object::Null,
            Object::Int(10),
            Object::Int(5),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
                "Error in statement {}",
                i + 1
            );
        }
    }

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

        let corr = [
            Object::Return(Box::new(Object::Int(10))),
            Object::Return(Box::new(Object::Int(9))),
            Object::Int(10),
            Object::Return(Box::new(Object::Int(10))),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
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

        let corr = [
            EvalErr::NotInt(Object::Boolean(true)),
            EvalErr::NotInt(Object::Boolean(true)),
            EvalErr::UnexpectedExpression(String::from(
                "Can not add to anything but string and int",
            )),
            EvalErr::UnexpectedExpression(String::from("Can only negate ints")),
            EvalErr::NotBool(Object::Int(5)),
            EvalErr::UnexpectedExpression(String::from(
                "Can not add to anything but string and int",
            )),
            EvalErr::UnboundIdent(String::from("x")),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect_err("This should never be OK"),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_let() {
        let s = String::from("let x = 10; x; let y = x + 10; y;");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let mut e = Evaluator::new(Rc::new(RefCell::new(Environment::new(None))));

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 4, "Incorrect number of statements");

        let corr = [Object::Null, Object::Int(10), Object::Null, Object::Int(20)];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
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

        let corr = [
            Object::Function(
                vec![],
                BlockStatement {
                    statements: vec![Statement::Expression(Expression::Literal(Literal::Int(2)))],
                },
                Rc::clone(&e.env),
            ),
            Object::Function(
                vec![Rc::from("x")],
                BlockStatement {
                    statements: vec![Statement::Expression(Expression::Ident(Rc::from("x")))],
                },
                Rc::clone(&e.env),
            ),
            Object::Function(
                vec![Rc::from("x"), Rc::from("y")],
                BlockStatement {
                    statements: vec![Statement::Expression(Expression::Infix(
                        Infix::Plus,
                        Box::new(Expression::Ident(Rc::from("x"))),
                        Box::new(Expression::Ident(Rc::from("y"))),
                    ))],
                },
                Rc::clone(&e.env),
            ),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
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

        let corr = [
            Object::Null,
            Object::Int(10),
            Object::Null,
            Object::Null,
            Object::Int(19),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_bultins_corr() {
        let s = String::from(
            "
                len(\"\");
                len(\"Hi\");
                len(\"Hi there\");
                len([1,2]);
                first([1,2]);
                first(\"Hi\");
                last([1,2]);
                last(\"Hi\");
                rest(\"Hi\");
                rest([1, 2]);
                push(\"H\", \"i\");
                push([1, 2], 3);
            ",
        );

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let env = Rc::new(RefCell::new(Environment::new(None)));
        env.borrow_mut().add_map(get_builtin_fns());
        let mut e = Evaluator::new(env);

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 12, "Incorrect number of statements");

        let corr = [
            Object::Int(0),
            Object::Int(2),
            Object::Int(8),
            Object::Int(2),
            Object::Int(1),
            Object::String(Rc::from("H")),
            Object::Int(2),
            Object::String(Rc::from("i")),
            Object::String(Rc::from("i")),
            Object::List(vec![Object::Int(2)]),
            Object::String(Rc::from("Hi")),
            Object::List(vec![Object::Int(1), Object::Int(2), Object::Int(3)]),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_bultins_err() {
        let s = String::from("len(\"a\", \"b\"); len(1); print();");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let env = Rc::new(RefCell::new(Environment::new(None)));
        env.borrow_mut().add_map(get_builtin_fns());
        let mut e = Evaluator::new(env);

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 3, "Incorrect number of statements");

        let corr = [
            EvalErr::IncorrectNrOfArgs(1),
            EvalErr::BuiltinError(format!(
                "{}",
                BuiltinError::WrongType(String::from("List, Map or String"))
            )),
            EvalErr::BuiltinError(format!("{}", BuiltinError::NotEnoughArgs)),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect_err("This should never be OK"),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_arr_corr() {
        let s = String::from("let a = [1, 2]; a[0]");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let env = Rc::new(RefCell::new(Environment::new(None)));
        let mut e = Evaluator::new(env);

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 2, "Incorrect number of statements");

        let corr = [Object::Null, Object::Int(1)];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_arr_err() {
        let s = String::from("a[-1]; a[0]");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let env = Rc::new(RefCell::new(Environment::new(None)));
        env.borrow_mut()
            .set(Rc::from("a"), Rc::from(Object::List(vec![])));
        let mut e = Evaluator::new(env);

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 2, "Incorrect number of statements");

        let corr = [EvalErr::OutOfRange(-1), EvalErr::OutOfRange(0)];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect_err("This should never be OK"),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_advanced_fns() {
        let s = String::from(
            "
                let map = fn(arr, f) {
                    let iter = fn(arr, acc) {
                        if (len(arr) == 0) {
                            acc
                        } else {
                            iter(rest(arr), push(acc, f(first(arr))));
                        }
                    };

                    iter(arr, []);
                };

                let double = fn(x) { x * 2 };

                map([1, 2, 3], double);

                let reduce = fn(arr, init, f) {
                    let iter = fn(arr, result) {
                        if (len(arr) == 0) {
                            result
                        } else {
                            iter(rest(arr), f(result, first(arr)));
                        }
                    };

                    iter(arr, init);
                };

                let sum = fn(arr) {
                    reduce(arr, 0, fn(init, v) { init + v });
                };

                sum([1, 2, 3]);
            ",
        );

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let env = Rc::new(RefCell::new(Environment::new(None)));
        env.borrow_mut().add_map(get_builtin_fns());
        let mut e = Evaluator::new(env);

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 6, "Incorrect number of statements");

        let corr = [
            Object::Null,
            Object::Null,
            Object::List(vec![Object::Int(2), Object::Int(4), Object::Int(6)]),
            Object::Null,
            Object::Null,
            Object::Int(6),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_fizzbuzz() {
        let s = String::from(
            "
                let reduce = fn(arr, init, f) {
                    let iter = fn(arr, result) {
                        if (len(arr) == 0) {
                            result
                        } else {
                            iter(rest(arr), f(result, first(arr)));
                        }
                    };

                    iter(arr, init);
                };

                let fizzbuzz = fn(init, n) {
                    let v = \"\";

                    if (n % 3 == 0) {
                        let v = v + \"Wizz\";
                    }

                    if (n % 5 == 0) {
                        let v = v + \"Buzz\";
                    }

                    init + v
                };

                reduce([3, 5, 15], \"\", fizzbuzz);
            ",
        );

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let env = Rc::new(RefCell::new(Environment::new(None)));
        env.borrow_mut().add_map(get_builtin_fns());
        let mut e = Evaluator::new(env);

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 3, "Incorrect number of statements");

        let corr = [
            Object::Null,
            Object::Null,
            Object::String(Rc::from("WizzBuzzWizzBuzz")),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_map_corr() {
        let s =
            String::from("{1:1, 2:2}; {1:1, \"two\":\"two\"}[1]; {1:1, \"two\":\"two\"}[\"two\"];");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let env = Rc::new(RefCell::new(Environment::new(None)));
        let mut e = Evaluator::new(env);

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 3, "Incorrect number of statements");

        let mut map = HashMap::new();
        map.insert(Object::Int(1), Object::Int(1));
        map.insert(Object::Int(2), Object::Int(2));

        let corr = [
            Object::Map(map),
            Object::Int(1),
            Object::String(Rc::from("two")),
        ];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect("This must be an OK value"),
                "Error in statement {}",
                i + 1
            );
        }
    }

    #[test]
    fn test_eval_map_err() {
        let s = String::from("{1:1}[2];");

        let l = Lexer::new(&s);
        let mut p = Parser::new(l);
        let prog = p.parse_program();
        let env = Rc::new(RefCell::new(Environment::new(None)));
        let mut e = Evaluator::new(env);

        assert_eq!(p.get_errors().len(), 0, "More than 0 errors");
        assert_eq!(prog.statements.len(), 1, "Incorrect number of statements");

        let corr = [EvalErr::NotInMap(Object::Int(2))];

        for (i, v) in corr.iter().enumerate() {
            assert_eq!(
                *v,
                e.eval_statement(&prog.statements[i])
                    .expect_err("This should never be OK"),
                "Error in statement {}",
                i + 1
            );
        }
    }
}
