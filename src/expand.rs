use crate::modify::Modify;
use crate::modify::Modify::{Changed, Same};
use crate::{Add, Exp, ExprPtr};
use crate::{Expr, Symbol};
use crate::{Ln, Mul};
use std::collections::VecDeque;
use std::env::var;
use std::ops::Deref;
use std::process::exit;

fn expand_vec(args: Vec<ExprPtr>) -> Vec<ExprMod> {
    args.into_iter().map(|arg| expand(arg)).collect()
}

fn unwrap_vec(args: Vec<ExprMod>) -> Modify<Vec<ExprPtr>> {
    args.into_iter()
        .fold(Same(Vec::new()), |mut args, arg| match arg {
            Same(expr) => match args {
                Changed(mut args) => {
                    args.push(expr);
                    Changed(args)
                }
                Same(mut args) => {
                    args.push(expr);
                    Same(args)
                }
            },
            Changed(expr) => {
                let mut args = args.unwrap();
                args.push(expr);
                Changed(args)
            }
        })
}

// https://github.com/sympy/sympy/blob/sympy-1.5.1/sympy/core/function.py#L2451
fn expand(expr_ptr: ExprPtr) -> ExprMod {
    let expr = *expr_ptr;
    match expr {
        Expr::Add(add) => unwrap_vec(expand_vec(add.args))
            .and_then(|args| Same(Expr::new(Expr::Add(Add { args }))))
            .and_then(expand_expr_add_integers)
            .if_changed(expand),
        Expr::Mul(mul) => unwrap_vec(expand_vec(mul.args))
            .and_then(|args| Same(Expr::new(Expr::Mul(Mul { args }))))
            .and_then(expand_expr_mul_integers)
            .and_then(expand_expr_mul_add)
            .if_changed(expand),
        Expr::Ln(ln) => expand(ln.arg)
            .and_then(|arg| Same(Expr::new(Expr::Ln(Ln { arg }))))
            .and_then(expand_expr_ln_mul)
            .if_changed(expand),
        Expr::Exp(exp) => expand(exp.arg)
            .and_then(|arg| Same(Expr::new(Expr::Exp(Exp { arg }))))
            .and_then(expand_expr_exp_sum)
            .and_then(expand_expr_exp_ln)
            .if_changed(expand),
        expr => Same(Expr::new(expr)),
    }
}

macro_rules! define_expand {
    ( $fn_name:ident, Expr::$variant:ident, $fn_variant:ident ) => {
        fn $fn_name(expr: ExprPtr) -> ExprMod {
            if let Expr::$variant(wrapped) = *expr {
                $fn_variant(wrapped)
            } else {
                Same(expr)
            }
        }
    };
}

define_expand!(expand_expr_exp_sum, Expr::Exp, expand_exp_sum);
define_expand!(expand_expr_exp_ln, Expr::Exp, expand_exp_ln);
define_expand!(expand_expr_mul_integers, Expr::Mul, expand_mul_integers);
define_expand!(expand_expr_mul_add, Expr::Mul, expand_mul_add);
define_expand!(expand_expr_ln_mul, Expr::Ln, expand_ln_mul);
define_expand!(expand_expr_add_integers, Expr::Add, expand_add_integers);

// exp(x + y) => exp(x) * exp(y)
fn expand_exp_sum(exp: Exp) -> ExprMod {
    match *exp.arg {
        Expr::Add(inner_add) => {
            let args = inner_add
                .args
                .into_iter()
                .map(|inner_arg| Expr::new(Expr::new_exp(*inner_arg)))
                .collect();
            Changed(Expr::new(Expr::Mul(Mul { args })))
        }
        arg => Same(Expr::new(Expr::new_exp(arg))),
    }
}

// exp(ln(x)) => x
fn expand_exp_ln(exp: Exp) -> ExprMod {
    match *exp.arg {
        Expr::Ln(ln) => Changed(ln.arg),
        arg => Same(Expr::new(Expr::new_exp(arg))),
    }
}

// ln(a * b) => ln(a) + ln(b)
fn expand_ln_mul(ln: Ln) -> ExprMod {
    match *ln.arg {
        Expr::Mul(inner_mul) => {
            let args = inner_mul
                .args
                .into_iter()
                .map(|inner_arg| Expr::new(Expr::new_ln(*inner_arg)))
                .collect();
            Changed(Expr::new(Expr::Add(Add { args })))
        }
        (arg) => Same(Expr::new(Expr::new_ln(arg))),
    }
}

fn cross_product<X, Y, Z>(xvec: &Vec<Y>, yvec: &Vec<Y>) -> Vec<Box<Z>>
where
    X: Clone + std::ops::Mul<X, Output = Z>,
    Y: Deref<Target = X>,
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
// (a + b) * (c + d) => ac + ad + bc + bd
fn expand_mul_add(mul: Mul) -> ExprMod {
    // first, we need to separate sums from other args
    let (mul_sum_args, other_mul_args) = mul.args.into_iter().fold(
        (Vec::new(), Vec::new()),
        |(mut sum_args, mut other_args), arg| {
            match *arg {
                Expr::Add(add) => sum_args.push(add),
                arg => other_args.push(Expr::new(arg)),
            };
            (sum_args, other_args)
        },
    );

    if mul_sum_args.is_empty() {
        return Same(Expr::new(Expr::Mul(Mul {
            args: other_mul_args,
        })));
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

        let mut product = Vec::with_capacity(capacity);
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
                Expr::new(Expr::Mul(mul))
            } else {
                panic!("any other kind of Expr is not expected")
            }
        })
        .collect();

    Changed(Expr::new(Expr::Add(Add {
        args: expanded_args,
    })))
}

// 3 + 2 + x => 5 + x
fn expand_add_integers(add: Add) -> ExprMod {
    let len_before = add.args.len();
    let (sum, mut args) = add
        .args
        .into_iter()
        .fold((0, Vec::new()), |(sum, mut args), arg| {
            if let Expr::Integer(i) = *arg.deref() {
                (sum + i, args)
            } else {
                args.push(arg);
                (sum, args)
            }
        });
    if sum != 0 {
        args.push(Expr::new(Expr::Integer(sum)))
    }
    match args.len() {
        // was Add, became Integer
        0 => Changed(Expr::new(Expr::Integer(0))),
        // was Add, became the Add argument
        1 => Changed(args.remove(0)),
        // compare len
        _ => {
            let variant = if args.len() == len_before {
                Same
            } else {
                Changed
            };
            variant(Expr::new(Expr::Add(Add { args })))
        }
    }
}

// 1 * x * 2 => x * 2
fn expand_mul_integers(mul: Mul) -> ExprMod {
    let len_before = mul.args.len();
    let (product, mut args) =
        mul.args
            .into_iter()
            .fold((1, Vec::new()), |(product, mut args), arg| {
                if let Expr::Integer(x) = *arg.deref() {
                    (product * x, args)
                } else {
                    args.push(arg);
                    (product, args)
                }
            });
    let mut args = match product {
        // was Mul, became Integer
        0 => return Changed(Expr::new(Expr::Integer(0))),
        1 => args,
        product => {
            args.push(Expr::new(Expr::Integer(product)));
            args
        }
    };
    match args.len() {
        0 => Changed(Expr::new(Expr::Integer(1))),
        1 => Changed(args.remove(0)),
        _ => {
            let variant = if len_before == args.len() {
                Same
            } else {
                Changed
            };
            variant(Expr::new(Expr::Mul(Mul { args })))
        }
    }
}

type ExprMod = Modify<ExprPtr>;

mod test {
    use crate::modify::Modify::Changed;
    use crate::simplify::{
        cross_product, expand, expand_add_integers, expand_exp_sum, expand_ln_mul, expand_mul_add,
        expand_mul_integers, ExprMod,
    };
    use crate::{Add, Exp, Expr, ExprPtr, Ln, Mul, Symbol};
    use std::convert::TryInto;
    use std::fmt::Display;

    fn x() -> Expr {
        Expr::Symbol("x".into())
    }
    fn y() -> Expr {
        Expr::Symbol("y".into())
    }
    fn z() -> Expr {
        Expr::Symbol("z".into())
    }
    fn unwrap_changed(expr: ExprMod) -> ExprPtr {
        if let Changed(expr) = expr {
            expr
        } else {
            panic!("same")
        }
    }

    #[test]
    fn test_expand_1() {
        let expr = (Expr::Integer(2) + y()) * (x() + 3);
        assert_eq!(expr.to_string(), "((2+y)*(x+3))");

        let expr = unwrap_changed(expand(Expr::new(expr)));
        assert_eq!(expr.to_string(), "((y*x)+(y*3)+(x*2)+6)");
    }

    #[test]
    fn test_expand_2() {
        let expr = Expr::new_exp(Expr::Integer(2) * 3);
        assert_eq!(expr.to_string(), "exp((2*3))");

        let expr = unwrap_changed(expand(Expr::new(expr)));
        assert_eq!(expr.to_string(), "exp(6)");
    }

    #[test]
    fn test_expand_3() {
        let expr = Expr::new_exp(x() + y());
        assert_eq!(expr.to_string(), "exp((x+y))");

        let expr = unwrap_changed(expand(Expr::new(expr)));
        assert_eq!(expr.to_string(), "(exp(x)*exp(y))");
    }

    #[test]
    fn test_expand_4() {
        let expr = Expr::new_exp(Expr::new_ln(x() * y()));
        assert_eq!(expr.to_string(), "exp(ln((x*y)))");

        let expr = unwrap_changed(expand(Expr::new(expr)));
        assert_eq!(expr.to_string(), "(x*y)");
    }

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
    fn test_expand_exp_sum() {
        let expr = Expr::new_exp(x() + y() * 2);
        assert_eq!(expr.to_string(), "exp((x+(y*2)))");

        let expr = unwrap_changed(expand_exp_sum(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "(exp(x)*exp((y*2)))");
    }

    #[test]
    fn test_expand_ln_mul() {
        let expr = Expr::new_ln(x() * y());
        assert_eq!(expr.to_string(), "ln((x*y))");

        let expr = unwrap_changed(expand_ln_mul(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "(ln(x)+ln(y))");
    }

    #[test]
    fn test_expand_mul_add() {
        let expr = (x() + 1) * y() * (z() + 2);
        assert_eq!(expr.to_string(), "((x+1)*y*(z+2))");

        let expr = unwrap_changed(expand_mul_add(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "((x*z*y)+(x*2*y)+(1*z*y)+(1*2*y))");
    }

    #[test]
    fn test_expand_add_integer_1() {
        let expr = Expr::Integer(0) + x() + 2;
        assert_eq!(expr.to_string(), "(0+x+2)");

        let expr = unwrap_changed(expand_add_integers(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "(x+2)");
    }

    #[test]
    fn test_expand_add_integer_2() {
        let expr = Expr::Integer(0) + 0 + 0;
        assert_eq!(expr.to_string(), "(0+0+0)");

        let expr = unwrap_changed(expand_add_integers(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "0");
    }

    #[test]
    fn test_expand_add_integer_3() {
        let expr = Expr::Integer(0) + 2 + 0;
        assert_eq!(expr.to_string(), "(0+2+0)");

        let expr = unwrap_changed(expand_add_integers(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "2");
    }

    #[test]
    fn test_expand_add_integer_4() {
        let expr = Expr::Integer(2) + 3 + x();
        assert_eq!(expr.to_string(), "(2+3+x)");

        let expr = unwrap_changed(expand_add_integers(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "(x+5)");
    }

    #[test]
    fn test_expand_mul_one_1() {
        let expr = Expr::Integer(1) * x() * 2;
        assert_eq!(expr.to_string(), "(1*x*2)");

        let expr = unwrap_changed(expand_mul_integers(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "(x*2)");
    }

    #[test]
    fn test_expand_mul_one_2() {
        let expr = Expr::Integer(1) * 1 * 1;
        assert_eq!(expr.to_string(), "(1*1*1)");

        let expr = unwrap_changed(expand_mul_integers(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "1");
    }

    #[test]
    fn test_expand_mul_one_3() {
        let expr = Expr::Integer(1) * 2 * 1;
        assert_eq!(expr.to_string(), "(1*2*1)");

        let expr = unwrap_changed(expand_mul_integers(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "2");
    }

    #[test]
    fn test_expand_mul_one_4() {
        let expr = Expr::Integer(1) * x() * 0;
        assert_eq!(expr.to_string(), "(1*x*0)");

        let expr = unwrap_changed(expand_mul_integers(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "0");
    }

    #[test]
    fn test_expand_mul_one_5() {
        let expr = Expr::Integer(1) * x() * 1;
        assert_eq!(expr.to_string(), "(1*x*1)");

        let expr = unwrap_changed(expand_mul_integers(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "x");
    }

    #[test]
    fn test_expand_mul_one_6() {
        let expr = Expr::Integer(3) * x() * 2;
        assert_eq!(expr.to_string(), "(3*x*2)");

        let expr = unwrap_changed(expand_mul_integers(expr.try_into().unwrap()));
        assert_eq!(expr.to_string(), "(x*6)");
    }
}
