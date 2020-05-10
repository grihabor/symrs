use crate::Add;
use crate::Mul;
use crate::{Expr, Symbol};
use std::collections::VecDeque;
use std::ops::Deref;
use std::process::exit;

// https://github.com/sympy/sympy/blob/sympy-1.5.1/sympy/core/function.py#L2451
// fn expand(expr: Expr) -> Expr {
//     match expr {
//         Expr::Add(add)) => {
//             match (*add.lhs, *add.rhs) {
//                 (Expr::Integer(0), add_arg) | (add_arg, Expr::Integer(0)) => add_arg,
//                 (Expr::Integer(l), Expr::Integer(r)) => Expr::Integer(l + r),
//
//                 (lhs @ Expr::Symbol(_), rhs @ Expr::Integer(_)) => {
//                     // swap operands
//                     expand(Expr::new_add(rhs, lhs))
//                 }
//
//                 (Expr::Add(left_add)), rhs) => {
//                     // change add order: ((a + b) + c) => (a + (b + c))
//                     expand(Expr::new_add(
//                         *left_add.lhs,
//                         Expr::new_add(*left_add.rhs, rhs),
//                     ))
//                 }
//
//                 // create the same add expression again to avoid borrow problems with expr
//                 (lhs, rhs) => Expr::new_add(lhs, rhs),
//             }
//         }
//
//         Expr::Mul(mul)) => {
//             match (*mul.lhs, *mul.rhs) {
//                 (Expr::Integer(0), _) | (_, Expr::Integer(0)) => Expr::Integer(0),
//                 (Expr::Integer(1), mul_arg) | (mul_arg, Expr::Integer(1)) => mul_arg,
//                 (Expr::Integer(l), Expr::Integer(r)) => Expr::Integer(l * r),
//
//                 (Expr::Add(add)), mul_arg)
//                 | (mul_arg, Expr::Add(add))) => expand(Expr::new_add(
//                     expand(Expr::new_mul_clone(add.lhs.deref(), &mul_arg)),
//                     expand(Expr::new_mul_clone(add.rhs.deref(), &mul_arg)),
//                 )),
//
//                 // this match arm must be in the end because we must try
//                 // to expand the expression first and only if we fail
//                 // we need to swap operands and try again.
//                 (lhs @ Expr::Symbol(_), rhs @ Expr::Integer(_))
//                 | (lhs @ Expr::Symbol(_), rhs @ Expr::Add(_))) => {
//                     // swap operands
//                     expand(Expr::new_mul(rhs, lhs))
//                 }
//
//                 // default case:
//                 // create the same mul expression again to avoid borrow problems with expr
//                 (lhs, rhs) => Expr::new_mul(lhs, rhs),
//             }
//         }
//
//         _ => expr,
//     }
// }

// https://github.com/sympy/sympy/blob/sympy-1.5.1/sympy/core/mul.py#L859
// Handle things like 1/(x*(x + 1)), which are automatically converted
// to 1/x*1/(x + 1)
fn expand_mul(expr: Expr) -> Expr {
    if let Expr::Pow(pow) = expr {
        match (*pow.lhs, *pow.rhs) {
            (Expr::Mul(inner_mul), Expr::Neg(neg)) => {
                let args = inner_mul
                    .args
                    .into_iter()
                    .map(|inner_arg| Box::new(Expr::new_pow(*inner_arg, Expr::Neg(neg.clone()))))
                    .collect();
                Expr::Mul(Mul { args })
            }
            (lhs, rhs) => Expr::new_pow(lhs, rhs),
        }
    } else {
        expr
    }
}

mod test {
    use crate::simplify::expand_mul;
    use crate::Expr::{Integer, Neg};
    use crate::{Expr, Symbol};

    // #[test]
    // fn test_expand() {
    //     let expr = Expr::new_mul(
    //         Expr::new_add(Expr::Integer(2), Expr::Symbol("y".into())),
    //         Expr::new_add(Expr::Symbol("x".into()), Expr::Integer(3)),
    //     );
    //     assert_eq!(expr.to_string(), "((2+y)*(x+3))");
    //
    //     let expr = expand(expr);
    //     assert_eq!(expr.to_string(), "((2*x)+(6+((x*y)+(3*y))))");
    // }

    #[test]
    fn test_expand_mul() {
        let expr = Expr::new_pow(
            Expr::new_mul(
                Expr::Symbol("x".into()),
                Expr::new_add(Expr::Symbol("x".into()), Expr::Integer(1)),
            ),
            Expr::new_neg(Expr::Symbol("y".into())),
        );
        assert_eq!(expr.to_string(), "((x*(x+1))^(-y))");

        let expr = expand_mul(expr);
        assert_eq!(expr.to_string(), "((x^(-y))*((x+1)^(-y)))");
    }
}
