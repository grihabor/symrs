use crate::expand::{
    expand_add_integers, expand_exp_ln, expand_exp_sum, expand_ln_mul, expand_mul_add,
    expand_mul_integers,
};
use crate::modify::Modify;
use crate::modify::Modify::{Changed, Same};
use crate::{Add, Exp, ExprMod, ExprPtr};
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

mod test {
    use crate::modify::Modify::Changed;
    use crate::simplify::expand;
    use crate::{Add, Exp, Expr, ExprMod, ExprPtr, Ln, Mul, Symbol};
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
}
