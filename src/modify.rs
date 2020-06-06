use crate::ExprPtr;

/// Mod is a modification. It indicates if the object
/// has been changed during a transformation or not.
pub enum Modify<T> {
    Same(T),
    Changed(T),
}

impl<T> Modify<T> {
    pub(crate) fn and_then<U, F>(self, f: F) -> Modify<U>
    where
        F: FnOnce(T) -> Modify<U>,
    {
        match self {
            Modify::Same(expr) => f(expr),
            Modify::Changed(expr) => Modify::Changed(f(expr).unwrap()),
        }
    }

    pub(crate) fn if_changed<F>(self, f: F) -> Modify<T>
    where
        F: FnOnce(T) -> Modify<T>,
    {
        match self {
            modify @ Modify::Same(_) => modify,
            Modify::Changed(expr) => Modify::Changed(f(expr).unwrap()),
        }
    }

    pub(crate) fn if_same<F>(self, f: F) -> Modify<T>
    where
        F: FnOnce(T) -> Modify<T>,
    {
        match self {
            Modify::Same(expr) => f(expr),
            modify @ Modify::Changed(_) => modify,
        }
    }

    pub(crate) fn unwrap(self) -> T {
        match self {
            Modify::Same(res) => res,
            Modify::Changed(res) => res,
        }
    }
}
