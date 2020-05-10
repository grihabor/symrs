mod simplify;

use num::Integer;
use std::fmt::{Binary, Debug, Display, Formatter, Pointer, Write};
use std::ops::Deref;

#[derive(Debug, Clone)]
enum Expr {
    Symbol(Symbol),
    Integer(i64),
    Add(Add),
    Neg(Neg),
    Mul(Mul),
    Pow(Pow),
}

impl Expr {
    fn new_neg(operand: Expr) -> Expr {
        Expr::Neg(Neg {
            arg: Box::new(operand),
        })
    }

    fn new_pow(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Pow(Pow {
            rhs: Box::new(rhs),
            lhs: Box::new(lhs),
        })
    }

    fn new_add(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Add(Add {
            args: vec![Box::new(lhs), Box::new(rhs)],
        })
    }

    fn new_mul(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Mul(Mul {
            args: vec![Box::new(lhs), Box::new(rhs)],
        })
    }

    fn new_mul_clone(lhs: &Expr, rhs: &Expr) -> Expr {
        Expr::new_mul(lhs.clone(), rhs.clone())
    }
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
struct Add {
    args: Vec<Box<Expr>>,
}

impl Display for Add {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        binary_op_fmt(&self, f)
    }
}

impl VarargOp for &Add {
    fn args(&self) -> Vec<&Expr> {
        (&self.args).into_iter().map(|a| a.deref()).collect()
    }

    fn op(&self) -> &str {
        "+"
    }
}

trait VarargOp {
    fn args(&self) -> Vec<&Expr>;
    fn op(&self) -> &str;
}

fn binary_op_fmt(op: &dyn VarargOp, f: &mut Formatter) -> std::fmt::Result {
    let mut r = f.write_char('(');
    let mut it = op.args().into_iter();

    // we need to handle first argument separately
    // to render op symbol correctly
    r = r.and(
        it.next()
            .ok_or(std::fmt::Error)
            .and_then(|arg| <Expr as Display>::fmt(arg, f)),
    );

    for arg in it {
        r = r
            .and(f.write_str(op.op()))
            .and(<Expr as Display>::fmt(arg, f))
    }
    r.and(f.write_char(')'))
}

#[derive(Debug, Clone)]
struct Mul {
    args: Vec<Box<Expr>>,
}

impl VarargOp for &Mul {
    fn args(&self) -> Vec<&Expr> {
        (&self.args).into_iter().map(|a| a.deref()).collect()
    }

    fn op(&self) -> &str {
        "*"
    }
}

impl Display for Mul {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        binary_op_fmt(&self, f)
    }
}

#[derive(Debug, Clone)]
struct Pow {
    rhs: Box<Expr>,
    lhs: Box<Expr>,
}

#[derive(Debug, Clone)]
struct Neg {
    arg: Box<Expr>,
}

impl Display for Neg {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("(-")
            .and(<Expr as Display>::fmt(&self.arg, f))
            .and(f.write_char(')'))
    }
}

impl std::ops::Mul for Expr {
    type Output = Expr;

    fn mul(self, rhs: Self) -> Self::Output {
        Expr::new_mul(self, rhs)
    }
}

impl VarargOp for &Pow {
    fn args(&self) -> Vec<&Expr> {
        let mut v = Vec::new();
        v.push(self.lhs.deref());
        v.push(self.rhs.deref());
        v
    }

    fn op(&self) -> &str {
        "^"
    }
}

impl Display for Pow {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        binary_op_fmt(&self, f)
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
            Expr::Add(add) => <Add as Display>::fmt(add, f),
            Expr::Neg(neg) => <Neg as Display>::fmt(neg, f),
            Expr::Mul(mul) => <Mul as Display>::fmt(mul, f),
            Expr::Pow(pow) => <Pow as Display>::fmt(pow, f),
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
    use num::traits::pow::Pow;

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn add_integers() {
        let result = Integer(1) + Integer(1);
        assert!(match result {
            Expr::Add(_) => true,
            _ => false,
        })
    }

    #[test]
    fn add_symbols() {
        let result = Symbol("x".into()) + Symbol("x".into());
        assert!(match result {
            Expr::Add(_) => true,
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
