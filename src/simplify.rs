use crate::Add;
use crate::MathOp;
use crate::Mul;
use crate::{Expr, Symbol};
use std::collections::VecDeque;
use std::ops::Deref;
use std::process::exit;

enum Simplify {
    Done,
    Again,
}

fn simplify(expr: Expr) -> Expr {
    match expr {
        Expr::MathOp(MathOp::Add(add)) => {
            match (*add.lhs, *add.rhs) {
                (Expr::Integer(0), add_arg) | (add_arg, Expr::Integer(0)) => add_arg,
                (Expr::Integer(l), Expr::Integer(r)) => Expr::Integer(l + r),

                (lhs @ Expr::Symbol(_), rhs @ Expr::Integer(_)) => {
                    // swap operands
                    simplify(Expr::new_add(rhs, lhs))
                }

                // create the same add expression again to avoid borrow problems with expr
                (lhs, rhs) => Expr::new_add(lhs, rhs),
            }
        }

        Expr::MathOp(MathOp::Mul(mul)) => {
            match (*mul.lhs, *mul.rhs) {
                (Expr::Integer(0), _) | (_, Expr::Integer(0)) => Expr::Integer(0),
                (Expr::Integer(1), mul_arg) | (mul_arg, Expr::Integer(1)) => mul_arg,
                (Expr::Integer(l), Expr::Integer(r)) => Expr::Integer(l * r),

                (Expr::MathOp(MathOp::Add(add)), mul_arg)
                | (mul_arg, Expr::MathOp(MathOp::Add(add))) => Expr::new_add(
                    simplify(Expr::new_mul_clone(add.lhs.deref(), &mul_arg)),
                    simplify(Expr::new_mul_clone(add.rhs.deref(), &mul_arg)),
                ),

                // this match arm must be in the end because we must try
                // to simplify the expression first and only if we fail
                // we need to swap operands and try again.
                (lhs @ Expr::Symbol(_), rhs @ Expr::Integer(_))
                | (lhs @ Expr::Symbol(_), rhs @ Expr::MathOp(MathOp::Add(_))) => {
                    // swap operands
                    simplify(Expr::new_mul(rhs, lhs))
                }

                // create the same mul expression again to avoid borrow problems with expr
                (lhs, rhs) => Expr::new_mul(lhs, rhs),
            }
        }

        _ => expr,
    }
}

mod test {
    use crate::simplify::simplify;
    use crate::{Expr, Symbol};

    #[test]
    fn test_simplify() {
        let expr = Expr::new_mul(
            Expr::new_add(Expr::Integer(2), Expr::Symbol("y".into())),
            Expr::new_add(Expr::Symbol("x".into()), Expr::Integer(3)),
        );
        assert_eq!(expr.to_string(), "((2+y)*(x+3))");

        let expr = simplify(expr);
        assert_eq!(expr.to_string(), "(((2*x)+6)+((x*y)+(3*y)))");
    }
}
