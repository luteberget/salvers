use mysatsolver::*;

pub struct MaxSatSolver<Th> {
  satsolver :DplltSolver<Th>,
  soft_clauses :Vec<Vec<Lit>>,
  selectors :HashMap<Lit, usize>,
  sums :HashMap<Lit, Totalizer>,
}

impl<Th> MaxSatSolver<Th> {

  pub fn new(theory :Th) -> Self {
    MaxSatSolver {
      satsolver: DplltSolver::new(theory),
      soft_clauses: Vec::new(),
      selectors: HashMap::new(),
      sums: HashMap::new(),
    }
  }

  pub fn new_var(&mut self) -> Lit {
    self.satsolver.new_var()
  }

  pub fn add_hard_clause(&mut self, cl :&[Lit]) {
    self.satsolver.add_clause(cl);
  }

  pub fn add_soft_clause(&mut self, cl :Vec<Lit>) {
    if cl.len() == 0 { panic!(); }

    let mut selector_lit = cl[0];
    if cl.len() > 1 {
      selector_lit = self.satsolver.new_var();
      cl.push(selector_lit.inverse());
      self.satsolver.push(cl);
    }

    self.selectors.insert(selector_lit, self.soft_clauses.len());
    self.soft_clauses.push(cl);
  }

  pub fn compute(&mut self) -> bool {
    let mut cost = 0;
    loop {
      self.satsolver.set_assumptions(self.selections.iter().chain(self.sums.iter()));
      if self.satsolver.solve() { return true; }
      // Not yet satisfiable, relax more.
      let core = self.satsolver.final_assumptions.clone();
      if core.len() == 0 { return false; }
      cost += 1;
      if core.len() == 1 && self.selectors.remove(&core[0]) {
          // unit core
          self.satsolver.add_clause(&[core[0].inverse()]);
      } else {
        for l in core.iter() {
            self.selectors.remove(l);
            if let Some((tot,bound)) = self.sums.remove(l) {
                tot.increase_bound(&mut self.satsolver, pbnd+1);
                self.sums.insert(tot.rhs()[pbnd+1].inverse(), (tot, pbnd+1));
            }
        }

        if core.len() > 1 {
          let t = Totalizer::count(&mut self.satsolver, core.iter().map(|l| l.inverse()), 1);
          self.sums.insert(tot.rhs()[1].inverse(), (t, 1));
        }
      }
    }
  }
}


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
