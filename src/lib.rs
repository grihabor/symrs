mod expand;
mod modify;
mod simplify;

use crate::modify::Modify;
use num::Integer;
use std::convert::TryFrom;
use std::fmt::{Binary, Debug, Display, Error, Formatter, Pointer, Write};
use std::ops::Deref;

#[derive(Debug, Clone)]
enum Expr {
    Symbol(Symbol),
    Integer(i64),
    Add(Add),
    Neg(Neg),
    Mul(Mul),
    Exp(Exp),
    Ln(Ln),
}

#[derive(Debug, Clone)]
struct Exp {
    arg: ExprPtr,
}

#[derive(Debug, Clone)]
struct Ln {
    arg: ExprPtr,
}

impl Display for Ln {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fmt_func(f, "ln", &self.arg)
    }
}

impl Display for Exp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Expr::Mul(mul) = self.arg.deref() {
            let mut args = vec![];
            let mut first_ln = None;
            for arg in &mul.args {
                if let (None, Expr::Ln(ln)) = (&first_ln, arg.deref()) {
                    first_ln = Some(ln)
                } else {
                    args.push(arg.clone())
                }
            }
            if let Some(ln) = first_ln {
                let rhs = if args.len() == 1 {
                    args.remove(0)
                } else {
                    Expr::new(Expr::Mul(Mul { args }))
                };
                let pow = Pow {
                    lhs: ln.arg.clone(),
                    rhs: rhs,
                };
                return fmt_binary_op(&pow, f);
            }
        }
        fmt_func(f, "exp", &self.arg)
    }
}

struct Pow {
    lhs: ExprPtr,
    rhs: ExprPtr,
}

impl VarargOp for Pow {
    fn args(&self) -> Vec<&Expr> {
        vec![self.lhs.deref(), self.rhs.deref()]
    }

    fn op(&self) -> &str {
        "^"
    }
}

fn fmt_func(f: &mut Formatter<'_>, name: &str, arg: &ExprPtr) -> std::fmt::Result {
    f.write_str(name)
        .and(f.write_char('('))
        .and(<ExprPtr as Display>::fmt(arg, f))
        .and(f.write_char(')'))
}

type ExprPtr = Box<Expr>;
type ExprMod = Modify<ExprPtr>;

impl Expr {
    fn new(t: Expr) -> ExprPtr {
        return Box::new(t);
    }

    fn new_neg(operand: Expr) -> Expr {
        Expr::Neg(Neg {
            arg: Expr::new(operand),
        })
    }

    fn new_pow(lhs: Expr, rhs: Expr) -> Expr {
        Expr::Exp(Exp {
            arg: Expr::new(Expr::new_mul(
                rhs,
                Expr::Ln(Ln {
                    arg: Expr::new(lhs),
                }),
            )),
        })
    }

    fn new_add(lhs: Expr, rhs: Expr) -> Expr {
        let append = |args: &mut Vec<ExprPtr>, expr| match expr {
            Expr::Add(mut add) => args.append(&mut add.args),
            expr => args.push(Expr::new(expr)),
        };
        let mut args = Vec::new();
        append(&mut args, lhs);
        append(&mut args, rhs);
        Expr::Add(Add { args })
    }

    fn new_mul(lhs: Expr, rhs: Expr) -> Expr {
        let append = |args: &mut Vec<ExprPtr>, expr| match expr {
            Expr::Mul(mut mul) => args.append(&mut mul.args),
            expr => args.push(Expr::new(expr)),
        };
        let mut args = Vec::new();
        append(&mut args, lhs);
        append(&mut args, rhs);
        Expr::Mul(Mul { args })
    }

    fn new_exp(arg: Expr) -> Expr {
        Expr::Exp(Exp {
            arg: Expr::new(arg),
        })
    }

    fn new_ln(arg: Expr) -> Expr {
        Expr::Ln(Ln {
            arg: Expr::new(arg),
        })
    }
}

impl TryFrom<Expr> for Ln {
    type Error = String;

    fn try_from(value: Expr) -> Result<Self, Self::Error> {
        if let Expr::Ln(ln) = value {
            Ok(ln)
        } else {
            Err(format!("expected Expr::Ln, got {:?}", value))
        }
    }
}

impl TryFrom<Expr> for Exp {
    type Error = String;

    fn try_from(value: Expr) -> Result<Self, Self::Error> {
        if let Expr::Exp(exp) = value {
            Ok(exp)
        } else {
            Err(format!("expected Expr::Exp, got {:?}", value))
        }
    }
}

impl TryFrom<Expr> for Mul {
    type Error = String;

    fn try_from(value: Expr) -> Result<Self, Self::Error> {
        if let Expr::Mul(mul) = value {
            Ok(mul)
        } else {
            Err(format!("expected Expr::Mul, got {:?}", value))
        }
    }
}

impl TryFrom<Expr> for Add {
    type Error = String;

    fn try_from(value: Expr) -> Result<Self, Self::Error> {
        if let Expr::Add(add) = value {
            Ok(add)
        } else {
            Err(format!("expected Expr::Add, got {:?}", value))
        }
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
    args: Vec<ExprPtr>,
}

impl Display for Add {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        fmt_binary_op(&self, f)
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

fn fmt_binary_op(op: &dyn VarargOp, f: &mut Formatter) -> std::fmt::Result {
    let mut r = f.write_char('(');
    let mut it = op.args().into_iter();

    // we need to handle first argument separately
    // to render op symbol correctly
    r = r.and(
        it.next()
            .ok_or(std::fmt::Error)
            .and_then(|arg| <Expr as Display>::fmt(arg, f)),
    );

    if let Err(_) = r {
        return f.write_char(')');
    }

    for arg in it {
        r = r
            .and(f.write_str(op.op()))
            .and(<Expr as Display>::fmt(arg, f))
    }
    r.and(f.write_char(')'))
}

#[derive(Debug, Clone)]
struct Mul {
    args: Vec<ExprPtr>,
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
        fmt_binary_op(&self, f)
    }
}

#[derive(Debug, Clone)]
struct Neg {
    arg: ExprPtr,
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

impl std::ops::Mul<i64> for Expr {
    type Output = Expr;

    fn mul(self, rhs: i64) -> Self::Output {
        Expr::new_mul(self, Expr::Integer(rhs))
    }
}

impl std::ops::Add for Expr {
    type Output = Expr;

    fn add(self, rhs: Self) -> Self::Output {
        Expr::new_add(self, rhs)
    }
}

impl std::ops::Add<i64> for Expr {
    type Output = Expr;

    fn add(self, rhs: i64) -> Self::Output {
        Expr::new_add(self, Expr::Integer(rhs))
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
            Expr::Exp(exp) => <Exp as Display>::fmt(exp, f),
            Expr::Ln(ln) => <Ln as Display>::fmt(ln, f),
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
