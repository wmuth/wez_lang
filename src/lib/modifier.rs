use crate::{
    ast::{BlockStatement, Expression, Literal, Program, Statement},
    evaluator::{EvalErr, Evaluator},
};

pub type ModifierFn = fn(&mut Evaluator, Expression) -> Result<Expression, EvalErr>;

pub fn modify_expr(
    e: Expression,
    ev: &mut Evaluator,
    f: ModifierFn,
) -> Result<Expression, EvalErr> {
    let new_e = f(ev, e)?;
    match new_e {
        Expression::Ident(_) => Ok(new_e),
        Expression::Literal(ref l) => match l {
            Literal::List(v) => Ok(Expression::Literal(Literal::List(
                v.iter()
                    .cloned()
                    .map(|e| modify_expr(e, ev, f))
                    .collect::<Result<Vec<Expression>, EvalErr>>()?,
            ))),
            Literal::Map(v) => Ok(Expression::Literal(Literal::Map(
                v.iter()
                    .cloned()
                    .map(|(k, v)| Ok((modify_expr(k, ev, f)?, modify_expr(v, ev, f)?)))
                    .collect::<Result<Vec<(Expression, Expression)>, EvalErr>>()?,
            ))),
            Literal::Boolean(_) | Literal::Int(_) | Literal::String(_) => Ok(new_e),
        },
        Expression::Infix(i, e1, e2) => {
            let me1 = modify_expr(*e1, ev, f)?;
            let me2 = modify_expr(*e2, ev, f)?;
            Ok(f(ev, Expression::Infix(i, Box::new(me1), Box::new(me2)))?)
        }
        Expression::Index(e1, e2) => {
            let me1 = modify_expr(*e1, ev, f)?;
            let me2 = modify_expr(*e2, ev, f)?;
            Ok(f(ev, Expression::Index(Box::new(me1), Box::new(me2)))?)
        }
        Expression::Prefix(p, e) => {
            let me = modify_expr(*e, ev, f)?;
            Ok(f(ev, Expression::Prefix(p, Box::new(me)))?)
        }
        Expression::If { cond, then, alt } => Ok(Expression::If {
            cond: Box::new(modify_expr(*cond, ev, f)?),
            then: modify_bs(then, ev, f)?,
            alt: modify_bs(alt, ev, f)?,
        }),
        Expression::Call { args, ident } => Ok(Expression::Call {
            args: args
                .into_iter()
                .map(|e| modify_expr(e, ev, f))
                .collect::<Result<Vec<Expression>, EvalErr>>()?,
            ident: Box::new(modify_expr(*ident, ev, f)?),
        }),
        Expression::Function { body, params } => Ok(Expression::Function {
            body: modify_bs(body, ev, f)?,
            params,
        }),
    }
}
pub fn modify_bs(
    bs: BlockStatement,
    ev: &mut Evaluator,
    f: ModifierFn,
) -> Result<BlockStatement, EvalErr> {
    Ok(BlockStatement {
        statements: bs
            .statements
            .into_iter()
            .map(|s| modify_stmt(s, ev, f))
            .collect::<Result<Vec<Statement>, EvalErr>>()?,
    })
}

pub fn modify_stmt(s: Statement, ev: &mut Evaluator, f: ModifierFn) -> Result<Statement, EvalErr> {
    match s {
        Statement::Expression(e) => Ok(Statement::Expression(modify_expr(e, ev, f)?)),
        Statement::Let { ident, expr } => Ok(Statement::Let {
            ident,
            expr: modify_expr(expr, ev, f)?,
        }),
        Statement::Return(e) => Ok(Statement::Return(modify_expr(e, ev, f)?)),
    }
}

pub fn modify_prg(p: Program, ev: &mut Evaluator, f: ModifierFn) -> Result<Program, EvalErr> {
    Ok(Program {
        statements: p
            .statements
            .into_iter()
            .map(|s| modify_stmt(s, ev, f))
            .collect::<Result<Vec<Statement>, EvalErr>>()?,
    })
}

#[cfg(test)]
mod test {
    use std::{cell::RefCell, rc::Rc};

    use crate::{
        ast::{Expression, Infix, Literal},
        environment::Environment,
    };

    use super::*;

    #[test]
    fn test_modify_one_two() {
        fn make_one_two(_ev: &mut Evaluator, e: Expression) -> Result<Expression, EvalErr> {
            match e {
                Expression::Literal(ref l) => match l {
                    Literal::Int(i) => {
                        if *i == 1 {
                            Ok(Expression::Literal(Literal::Int(2)))
                        } else {
                            Ok(Expression::Literal(l.clone()))
                        }
                    }
                    _ => Ok(e),
                },
                _ => Ok(e),
            }
        }

        let before = Expression::Infix(
            Infix::Plus,
            Box::new(Expression::Infix(
                Infix::Minus,
                Box::new(Expression::Literal(Literal::Int(1))),
                Box::new(Expression::Literal(Literal::Int(1))),
            )),
            Box::new(Expression::Literal(Literal::Int(1))),
        );

        let after = Ok(Expression::Infix(
            Infix::Plus,
            Box::new(Expression::Infix(
                Infix::Minus,
                Box::new(Expression::Literal(Literal::Int(2))),
                Box::new(Expression::Literal(Literal::Int(2))),
            )),
            Box::new(Expression::Literal(Literal::Int(2))),
        ));

        assert_eq!(
            modify_expr(
                before,
                &mut Evaluator::new(Rc::from(RefCell::from(Environment::new(None)))),
                make_one_two
            ),
            after
        );
    }

    #[test]
    fn test_modify_arr() {
        fn add_one(_ev: &mut Evaluator, e: Expression) -> Result<Expression, EvalErr> {
            match e {
                Expression::Literal(Literal::Int(i)) => {
                    Ok(Expression::Literal(Literal::Int(i + 1)))
                }
                _ => Ok(e),
            }
        }

        let v = vec![
            Expression::Literal(Literal::Int(1)),
            Expression::Literal(Literal::Int(2)),
            Expression::Ident(Rc::from("test")),
            Expression::Literal(Literal::Int(3)),
        ];

        let before = Expression::Literal(Literal::List(v));

        let v2 = vec![
            Expression::Literal(Literal::Int(2)),
            Expression::Literal(Literal::Int(3)),
            Expression::Ident(Rc::from("test")),
            Expression::Literal(Literal::Int(4)),
        ];

        let after = Ok(Expression::Literal(Literal::List(v2)));

        assert_eq!(
            modify_expr(
                before,
                &mut Evaluator::new(Rc::from(RefCell::from(Environment::new(None)))),
                add_one
            ),
            after
        );
    }

    #[test]
    fn test_modify_map() {
        fn negate(_ev: &mut Evaluator, e: Expression) -> Result<Expression, EvalErr> {
            match e {
                Expression::Literal(Literal::Int(i)) => {
                    Ok(Expression::Literal(Literal::Int(i * -1)))
                }
                _ => Ok(e),
            }
        }

        let v = vec![
            (
                Expression::Literal(Literal::Int(1)),
                Expression::Literal(Literal::Int(1)),
            ),
            (
                Expression::Literal(Literal::Int(2)),
                Expression::Literal(Literal::Int(2)),
            ),
            (
                Expression::Literal(Literal::Int(3)),
                Expression::Literal(Literal::Int(3)),
            ),
        ];

        let before = Expression::Literal(Literal::Map(v));

        let v2 = vec![
            (
                Expression::Literal(Literal::Int(-1)),
                Expression::Literal(Literal::Int(-1)),
            ),
            (
                Expression::Literal(Literal::Int(-2)),
                Expression::Literal(Literal::Int(-2)),
            ),
            (
                Expression::Literal(Literal::Int(-3)),
                Expression::Literal(Literal::Int(-3)),
            ),
        ];

        let after = Ok(Expression::Literal(Literal::Map(v2)));

        assert_eq!(
            modify_expr(
                before,
                &mut Evaluator::new(Rc::from(RefCell::from(Environment::new(None)))),
                negate
            ),
            after
        );
    }
}
