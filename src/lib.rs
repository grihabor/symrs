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
enum MathOp {
    Add(Add),
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

#[cfg(test)]
mod tests {
    use crate::Expr;
    use crate::Expr::{Integer, Symbol};

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
            Expr::MathOp(_) => true,
            _ => false,
        })
    }
}
