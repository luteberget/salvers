mod bool;
pub use self::bool::*;

mod theory;
pub use self::theory::*;

use std::hash::Hash;

/// A variable in a SAT problem.
pub trait Var: Copy + Clone + PartialEq + Eq + PartialOrd + Ord + Hash {}

impl Var for i32 {}

/// A literal in a SAT problem.
pub trait Lit:
    std::ops::Not<Output = Self> + Copy + Clone + PartialEq + Eq + PartialOrd + Ord + Hash
{
    type Var: Var;

    fn into_var(self) -> (Self::Var, bool);
    fn from_var_sign(v: Self::Var, sign: bool) -> Self;
}

/// An instance of a SAT problem (corresponds to a solver object).
pub trait SatInstance<L: Lit> {
    fn new_var(&mut self) -> Bool<L>;
    fn add_clause<IL: Into<Bool<L>>, I: IntoIterator<Item = IL>>(&mut self, clause: I);
}

/// A model of a SAT problem represents an assignment to the variables of the problem.
pub trait SatModel {
    type Lit: Lit;
    fn lit_value(&self, l: &Self::Lit) -> bool;
}

pub enum SatResult<'a, L: Lit> {
    Sat(Box<dyn SatModel<Lit = L> + 'a>),
    Unsat,
}

pub enum SatResultWithCore<'a, L: Lit> {
    Sat(Box<dyn SatModel<Lit = L> + 'a>),
    Unsat(Box<[L]>),
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
