use num::Integer;
use std::fmt::{Binary, Debug, Display, Formatter, Pointer, Write};
use std::ops::Deref;

#[derive(Debug)]
enum Expr {
    Symbol(Symbol),
    Integer(i64),
    MathOp(MathOp),
}

#[derive(Debug)]
struct Symbol {
    name: String,
}

impl Display for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name.as_str())
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        Symbol {
            name: String::from(s),
        }
    }
}

#[derive(Debug)]
struct Add {
    rhs: Box<Expr>,
    lhs: Box<Expr>,
}

impl Display for Add {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        binary_op_fmt(self, f)
    }
}

impl BinaryOp for &Add {
    fn rhs(&self) -> &Expr {
        return self.rhs.deref();
    }

    fn lhs(&self) -> &Expr {
        return self.lhs.deref();
    }

    fn op(&self) -> &str {
        "-"
    }
}

trait BinaryOp {
    fn rhs(&self) -> &Expr;
    fn lhs(&self) -> &Expr;
    fn op(&self) -> &str;
}

fn binary_op_fmt<T: BinaryOp>(op: T, f: &mut Formatter<'_>) -> std::fmt::Result {
    f.write_char('(')
        .and(<Expr as Display>::fmt(op.lhs(), f))
        .and(f.write_str(op.op()))
        .and(<Expr as Display>::fmt(op.rhs(), f))
        .and(f.write_char(')'))
}

#[derive(Debug)]
struct Sub {
    rhs: Box<Expr>,
    lhs: Box<Expr>,
}

impl BinaryOp for &Sub {
    fn rhs(&self) -> &Expr {
        return self.rhs.deref();
    }

    fn lhs(&self) -> &Expr {
        return self.lhs.deref();
    }

    fn op(&self) -> &str {
        "-"
    }
}

impl Display for Sub {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        binary_op_fmt(self, f)
    }
}

#[derive(Debug)]
enum MathOp {
    Add(Add),
    Sub(Sub),
}

impl Display for MathOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            MathOp::Add(add) => <Add as Display>::fmt(add, f),
            MathOp::Sub(sub) => <Sub as Display>::fmt(sub, f),
        }
    }
}

impl std::ops::Add for Expr {
    type Output = Expr;

    fn add(self, rhs: Self) -> Self::Output {
        return Expr::MathOp(MathOp::Add(Add {
            lhs: Box::new(self),
            rhs: Box::new(rhs),
        }));
    }
}

impl std::ops::Sub for Expr {
    type Output = Expr;

    fn sub(self, rhs: Self) -> Self::Output {
        return Expr::MathOp(MathOp::Sub(Sub {
            lhs: Box::new(self),
            rhs: Box::new(rhs),
        }));
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Integer(i) => <i64 as Display>::fmt(i, f),
            Expr::Symbol(s) => <Symbol as Display>::fmt(s, f),
            Expr::MathOp(op) => <MathOp as Display>::fmt(op, f),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Expr;
    use crate::Expr::{Integer, Symbol};
    use crate::MathOp;

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn add_integers() {
        let result = Integer(1) + Integer(1);
        assert!(match result {
            Expr::MathOp(_) => true,
            _ => false,
        })
    }

    #[test]
    fn add_symbols() {
        let result = Symbol("x".into()) + Symbol("x".into());
        assert!(match result {
            Expr::MathOp(MathOp::Add(_)) => true,
            _ => false,
        })
    }

    #[test]
    fn sub_symbols() {
        let result = Symbol("x".into()) - Integer(1);
        assert!(match result {
            Expr::MathOp(MathOp::Sub(_)) => true,
            _ => false,
        })
    }

    #[test]
    fn sub_display() {
        let result = Symbol("x".into()) - Integer(1);
        assert_eq!(result.to_string(), "(x-1)")
    }

    #[test]
    fn add_display() {
        let result = Integer(1) + Symbol("x".into());
        assert_eq!(result.to_string(), "(1-x)")
    }
}
