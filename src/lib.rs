use num::Integer;
use std::fmt::{Binary, Debug, Display, Formatter, Pointer, Write};
use std::ops::Deref;

#[derive(Debug)]
enum Expr {
    Symbol(Symbol),
    Integer(i64),
    MathOp(MathOp),
}

impl Expr {
    fn new_neg(operand: Expr) -> Expr {
        Expr::MathOp(MathOp::Neg(Neg {
            operand: Box::new(operand),
        }))
    }

    fn new_pow(lhs: Expr, rhs: Expr) -> Expr {
        Expr::MathOp(MathOp::Pow(Pow {
            rhs: Box::new(rhs),
            lhs: Box::new(lhs),
        }))
    }

    fn new_add(lhs: Expr, rhs: Expr) -> Expr {
        Expr::MathOp(MathOp::Add(Add {
            rhs: Box::new(rhs),
            lhs: Box::new(lhs),
        }))
    }

    fn new_mul(lhs: Expr, rhs: Expr) -> Expr {
        Expr::MathOp(MathOp::Mul(Mul {
            rhs: Box::new(rhs),
            lhs: Box::new(lhs),
        }))
    }
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
        self.rhs.deref()
    }

    fn lhs(&self) -> &Expr {
        self.lhs.deref()
    }

    fn op(&self) -> &str {
        "+"
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
struct Mul {
    rhs: Box<Expr>,
    lhs: Box<Expr>,
}

impl BinaryOp for &Mul {
    fn rhs(&self) -> &Expr {
        self.rhs.deref()
    }

    fn lhs(&self) -> &Expr {
        self.lhs.deref()
    }

    fn op(&self) -> &str {
        "*"
    }
}

impl Display for Mul {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        binary_op_fmt(self, f)
    }
}

#[derive(Debug)]
enum MathOp {
    Add(Add),
    Neg(Neg),
    Mul(Mul),
    Pow(Pow),
}

#[derive(Debug)]
struct Pow {
    rhs: Box<Expr>,
    lhs: Box<Expr>,
}

#[derive(Debug)]
struct Neg {
    operand: Box<Expr>,
}

impl Display for Neg {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("(-")
            .and(<Expr as Display>::fmt(&self.operand, f))
            .and(f.write_char(')'))
    }
}

impl std::ops::Mul for Expr {
    type Output = Expr;

    fn mul(self, rhs: Self) -> Self::Output {
        Expr::new_mul(self, rhs)
    }
}

impl BinaryOp for &Pow {
    fn rhs(&self) -> &Expr {
        self.rhs.deref()
    }

    fn lhs(&self) -> &Expr {
        self.lhs.deref()
    }

    fn op(&self) -> &str {
        "^"
    }
}

impl Display for Pow {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        binary_op_fmt(self, f)
    }
}

impl Display for MathOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            MathOp::Add(add) => <Add as Display>::fmt(add, f),
            MathOp::Neg(neg) => <Neg as Display>::fmt(neg, f),
            MathOp::Mul(mul) => <Mul as Display>::fmt(mul, f),
            MathOp::Pow(pow) => <Pow as Display>::fmt(pow, f),
        }
    }
}

impl std::ops::Add for Expr {
    type Output = Expr;

    fn add(self, rhs: Self) -> Self::Output {
        Expr::new_add(self, rhs)
    }
}

impl std::ops::Sub for Expr {
    type Output = Expr;

    fn sub(self, rhs: Self) -> Self::Output {
        Expr::new_add(self, Expr::new_neg(rhs))
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

impl std::ops::Div for Expr {
    type Output = Expr;

    fn div(self, rhs: Self) -> Self::Output {
        Expr::new_mul(self, Expr::new_pow(rhs, Expr::Integer(-1)))
    }
}

impl num::traits::pow::Pow<Expr> for Expr {
    type Output = Expr;

    fn pow(self, rhs: Self) -> Self::Output {
        Expr::new_pow(self, rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::Expr;
    use crate::Expr::{Integer, Symbol};
    use crate::MathOp;
    use num::traits::pow::Pow;

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
    fn sub_display() {
        let result = Symbol("x".into()) - Integer(1);
        assert_eq!(result.to_string(), "(x+(-1))")
    }

    #[test]
    fn add_display() {
        let result = Integer(1) + Symbol("x".into());
        assert_eq!(result.to_string(), "(1+x)")
    }

    #[test]
    fn mul_display() {
        let result = Integer(1) * Symbol("x".into());
        assert_eq!(result.to_string(), "(1*x)")
    }

    #[test]
    fn div_display() {
        let result = Integer(5) / Symbol("x".into());
        assert_eq!(result.to_string(), "(5*(x^-1))")
    }

    #[test]
    fn pow_display() {
        let result = Symbol("x".into()).pow(Integer(2));
        assert_eq!(result.to_string(), "(x^2)")
    }
}
