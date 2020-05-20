pub trait Lit : std::ops::Not<Output = Self> + Copy + Clone {}
pub type Model<L> = Vec<L>;
pub type Conflict<L> = Vec<L>;

pub trait SatSolver<L : Lit> {
  fn new_var(&mut self) -> L;
  fn add_clause(&mut self, clause :impl IntoIterator<Item = impl Into<L>>);
  fn solve(&mut self, assumptions :impl IntoIterator<Item = L>) -> Result<Model<L>, Conflict<L>>;
}

pub trait SatSolverTheory<L: Lit, R: Refinement<L>> {
  fn solve_with_theory(&mut self, assumptions :impl IntoIterator<Item = L>, 
                       theory :&mut impl Theory<L, R>) -> Result<Model<L>, Conflict<L>>;
}

pub trait Refinement<L :Lit> {
  fn add_deduced(&mut self, l: L, rref :u32);
  fn add_clause(&mut self, l: impl IntoIterator<Item = L>);
}

pub trait Theory<L : Lit, R: Refinement<L>> {
  fn check(&mut self, lits :&[L], refinement :&mut R);
  fn explain(&mut self, l :L, x :u32, refinement :&mut R);
  fn new_decision_level(&mut self);
  fn backtrack(&mut self, level :i32);
}

#[cfg(test)]
mod tests {

    fn solve<L: core::fmt::Debug>(assumptions :impl IntoIterator<Item = L>) {
      for a in assumptions { println!("{:?}", a); }
    }

    #[test]
    fn it_works() {
      type Lit = usize;
      solve(Some(1));
    }
}
