use std::hash::Hash;

mod bool;
mod finset;
mod symbolic;
mod theory;
mod testsolver;

pub use crate::bool::Bool;
pub use crate::symbolic::{Symbolic, SymbolicModel};
pub use crate::finset::FinSet;
pub use crate::theory::{Theory, Refinement};

/// A literal in a SAT problem.
pub trait Lit: std::ops::Not<Output = Self> + Copy + Clone + Hash {}

/// An instance of a SAT problem (corresponds to a solver object).
pub trait SatInstance<L: Lit> {
    fn new_var(&mut self) -> Bool<L>;
    fn add_clause<IL: Into<Bool<L>>, I: IntoIterator<Item = IL>>(&mut self, clause: I);
}

/// A model of a SAT problem represents an assignment to the variables of the problem.
pub trait SatModel {
    type L: Lit;
    fn lit_value(&self, l: &Self::L) -> bool;
}

pub enum SatResult<'a, L: Lit> {
    Sat(Box<dyn SatModel<L = L> + 'a>),
    Unsat,
}

pub enum SatResultWithCore<'a, L: Lit> {
    Sat(Box<dyn SatModel<L = L> + 'a>),
    Unsat(Box<dyn ExactSizeIterator<Item = L> + 'a>),
}

pub trait SatSolver {
    type Lit: Lit;
    fn solve<'a>(&'a mut self) -> SatResult<'a, Self::Lit>;
}

pub trait SatSolverWithCore {
    type Lit: Lit;
    fn solve_with_assumptions<'a>(
        &'a mut self,
        assumptions: impl IntoIterator<Item = Bool<Self::Lit>>,
    ) -> SatResultWithCore<'a, Self::Lit>;
}

