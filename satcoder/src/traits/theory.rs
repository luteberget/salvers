use crate::*;

pub trait Refinement<L: Lit> {
    fn add_deduced(&mut self, l: L, rref: u32);
    fn add_clause(&mut self, l: impl IntoIterator<Item = L>);
}

pub trait Theory<L: Lit, R: Refinement<L>> {
    fn check(&mut self, lits: &[L], refinement: &mut R);
    fn explain(&mut self, l: L, x: u32, refinement: &mut R);
    fn new_decision_level(&mut self);
    fn backtrack(&mut self, level: i32);
}
