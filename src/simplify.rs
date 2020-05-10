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
fn expand_exp_mul(expr: Expr) -> Expr {
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

fn cross_product<X, Z>(xvec: &Vec<Box<X>>, yvec: &Vec<Box<X>>) -> Vec<Box<Z>>
where
    X: Clone + std::ops::Mul<X, Output = Z>,
    Z: Clone,
{
    let mut result: Vec<Box<Z>> = Vec::with_capacity(xvec.len() * yvec.len());
    for x in xvec {
        for y in yvec {
            result.push(Box::new(x.deref().clone() * y.deref().clone()))
        }
    }
    result
}

// https://github.com/sympy/sympy/blob/sympy-1.5.1/sympy/core/mul.py#L859
// Handle things like 1/(x*(x + 1)), which are automatically converted
// to 1/x*1/(x + 1)
fn expand_mul_add(expr: Expr) -> Expr {
    if let Expr::Mul(mul) = expr {
        // first, we need to separate sums from other args
        let (mul_sum_args, other_mul_args) = (|| {
            let mut sum_args = Vec::with_capacity(mul.args.len());
            let mut other_args = Vec::with_capacity(mul.args.len());
            for arg in mul.args {
                match *arg {
                    Expr::Add(add) => sum_args.push(add),
                    arg => other_args.push(Box::new(arg)),
                }
            }
            (sum_args, other_args)
        })();

        if mul_sum_args.is_empty() {
            return Expr::Mul(Mul {
                args: other_mul_args,
            });
        }

        // second, calculate all sum products:
        // xyz(a + b) * (c + d) = xyz(ac + ad + bc + bd)
        let product_capacity = mul_sum_args
            .iter()
            .fold(0usize, |sum, add| sum + add.args.len());

        let sum_of_products_args = (|capacity| {
            let mut it = mul_sum_args.iter();
            let first_add = it
                .next()
                .expect("there must be at least one item, we've checked already");

            let mut product = Vec::new();
            for arg in &first_add.args {
                product.push(arg.clone())
            }

            for sum_arg in it {
                let new_sum_args = cross_product(&product, &sum_arg.args);

                // replace content of product with new_product
                product.clear();
                for arg in new_sum_args {
                    product.push(arg.clone())
                }
            }
            product
        })(product_capacity);

        // third, multiply each term and other args:
        // xyz(ac + ad + bc + bd) = xyzac + xyzad + xyzbc + xyzbd
        let expanded_args = sum_of_products_args
            .into_iter()
            .map(|sum_of_products_arg| {
                if let Expr::Mul(mut mul) = sum_of_products_arg.deref().to_owned() {
                    for arg in other_mul_args.iter() {
                        mul.args.push(arg.to_owned())
                    }
                    Box::new(Expr::Mul(mul))
                } else {
                    panic!("any other kind of Expr is not expected")
                }
            })
            .collect();

        Expr::Add(Add {
            args: expanded_args,
        })
    } else {
        expr
    }
}

mod test {
    use crate::simplify::{cross_product, expand_exp_mul, expand_mul_add};
    use crate::Expr::{Integer, Neg};
    use crate::{Expr, Mul, Symbol};
    use std::fmt::Display;

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
    fn test_cross_product() {
        let lhs: Vec<Box<i32>> = vec![1, 2, 3].into_iter().map(|i| Box::new(i)).collect();
        let rhs: Vec<Box<i32>> = vec![5, 7].into_iter().map(|i| Box::new(i)).collect();
        let expected = vec![5, 7, 10, 14, 15, 21]
            .into_iter()
            .map(|i| Box::new(i))
            .collect::<Vec<Box<i32>>>();
        assert_eq!(expected, cross_product(&lhs, &rhs),);
        let expected = vec![5, 10, 15, 7, 14, 21]
            .into_iter()
            .map(|i| Box::new(i))
            .collect::<Vec<Box<i32>>>();
        assert_eq!(expected, cross_product(&rhs, &lhs),)
    }

    #[test]
    fn test_expand_exp_mul() {
        let expr = Expr::new_pow(
            Expr::new_mul(
                Expr::Symbol("x".into()),
                Expr::new_add(Expr::Symbol("x".into()), Expr::Integer(1)),
            ),
            Expr::new_neg(Expr::Symbol("y".into())),
        );
        assert_eq!(expr.to_string(), "((x*(x+1))^(-y))");

        let expr = expand_exp_mul(expr);
        assert_eq!(expr.to_string(), "((x^(-y))*((x+1)^(-y)))");
    }

    #[test]
    fn test_expand_mul_add() {
        let expr = Expr::Mul(Mul {
            args: vec![
                Box::new(Expr::new_add(Expr::Symbol("x".into()), Integer(1))),
                Box::new(Expr::Symbol("y".into())),
                Box::new(Expr::new_add(Expr::Symbol("z".into()), Integer(2))),
            ],
        });
        assert_eq!(expr.to_string(), "((x+1)*y*(z+2))");

        let expr = expand_mul_add(expr);
        assert_eq!(expr.to_string(), "((x*z*y)+(x*2*y)+(1*z*y)+(1*2*y))");
    }
}
