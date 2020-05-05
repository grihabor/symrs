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

#[derive(Debug)]
struct Sub {
    rhs: Box<Expr>,
    lhs: Box<Expr>,
}

#[derive(Debug)]
enum MathOp {
    Add(Add),
    Sub(Sub),
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
        }))
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
}
