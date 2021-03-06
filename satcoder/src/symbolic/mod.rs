mod finset;
mod model_eq;
mod unary;
mod binary;
pub use finset::*;
pub use model_eq::*;
pub use unary::*;
pub use binary::*;

use crate::{Bool, Lit, SatModel};
pub trait SymbolicModel<L: Lit> {
    fn value<'a, 'b, S: Symbolic<'a, L>>(&'b self, l: &'a S) -> S::T;
}

impl<'m, L: Lit> SymbolicModel<L> for dyn SatModel<Lit = L> + 'm {
    fn value<'a, 'b, S: Symbolic<'a, L>>(&'b self, l: &'a S) -> S::T {
        l.interpret(self)
    }
}

impl<'m, L: Lit, T: SatModel<Lit = L> + 'm> SymbolicModel<L> for T {
    fn value<'a, 'b, S: Symbolic<'a, L>>(&'b self, l: &'a S) -> S::T {
        l.interpret(self)
    }
}

pub trait Symbolic<'a, L: Lit> {
    type T;
    fn interpret<'b>(&'a self, m: &'b dyn SatModel<Lit = L>) -> Self::T;
}

impl<'a, L: Lit> Symbolic<'a, L> for Bool<L> {
    type T = bool;

    fn interpret(&self, m: &dyn SatModel<Lit = L>) -> Self::T {
        match self {
            Bool::Lit(l) => m.lit_value(l),
            Bool::Const(b) => *b,
        }
    }
}
