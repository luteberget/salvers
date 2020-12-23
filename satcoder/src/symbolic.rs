use crate::{Lit, SatModel, Bool};
pub trait SymbolicModel<L: Lit> {
    fn value<'a, 'b, S: Symbolic<'a, L>>(&'b self, l: &'a S) -> S::T;
}

impl<'m, L: Lit> SymbolicModel<L> for dyn SatModel<L = L> + 'm {
    fn value<'a, 'b, S: Symbolic<'a, L>>(&'b self, l: &'a S) -> S::T {
        l.interpret(self)
    }
}

pub trait Symbolic<'a, L: Lit> {
    type T;
    fn interpret<'b>(&'a self, m: &'b dyn SatModel<L = L>) -> Self::T;
}

impl<'a, L: Lit> Symbolic<'a, L> for Bool<L> {
    type T = bool;

    fn interpret(&self, m: &dyn SatModel<L = L>) -> Self::T {
        match self {
            Bool::Lit(l) => m.lit_value(l),
            Bool::Const(b) => *b,
        }
    }
}
