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
      let core_sels = core.iter().filter(|l| self.selectors.contains(l)).collect::<Vec<_>>();
      let core_sums = core.iter().filter(|l| self.selectors.contains(l)).collect::<Vec<_>>();
      let mut garbage = HashSet::new();


      if core.sels.len() == 1 && core_sums.len() == 0 {
        // unit core
        self.satsolver.add_clause(vec![core_sels[0].inverse()]);
        garbage.insert(core_sels[0]);
      } else {
        // non-unit core

        /* Process soft clause selectors participating in a new core. */
        let mut relaxations = Vec::new();
        for l in core_sels.iter() {
          garbage.insert(*l);
          relaxations.push(l.inverse());
        }

        /* Process cardinality sums participating in a new core. */
        for l in core_sums.iter() {
          garbage.insert(*l);

          /* update sum: increase the bound of a given totalizer sum. */
          let (totalizer,prev_bound) = self.sums.get(l).unwrap();
          let new_bound = prev_bound + 1;
          totalizer.increase_bound(&mut self.satsolver, new_bound);

          let l_new = totalizer.lits[new_bound].inverse();
          self.garbage.remove(&l_new);
          relaxations.push(l.inverse());
        }

        if relaxations.len() > 1 {
          // new cardinality constraint
          let t = Totalizer::new(&mut self.satsolver, relaxations, 1);
          t.add_clauses(&mut self.satsolver);
          t.set_bound(b);
        }
      }

      // update set of assumptions (selections + sums)
      self.selectors.retain(|(lit, soft_clause_id)| !garbage.contains(lit));
      self.sums.retain(|(lit, totalizer)| !garbage.contains(lit));
    }
  }
}


// Incremental totalizer encoding (implements atmost-n constraint)
// Ported from itot.hh by Antonio Morgadox and Alexey S. Ignatiev. 

type Totalizer = TotTree;
pub struct TotTree {
  lits :Vec<Var>,
  nof_input: u32,
  left : Option<Box<TotTree>>,
  right : Option<Box<TotTree>>,
}

impl TotTree {

 fn singleton(l :Lit) -> Self {
    TotTree {
      lits: vec![l], 
      nof_input: 1, 
      left: None,
      right: None,
    }
 }

 pub fn new(solver :&mut SatSolver, lhs :Vec<Lit>, rhs :u32) -> TotTree {
   let mut nqueue = l.iter().map(|l| Self::singleton(l)).collect::<VecDeque<_>>();
   while nqueue.len() > 1 {
     let l = nqueue.pop_font();
     let r = nqueue.pop_font();
     let kmin = (l.nof_input + r.nof_input).min(rhs+1);
     let new_vars = (0..kmin).map(|_| s.new_var()).collect::<Vec<_>>();
     Self::new_ua(solver, &new_vars, kmin, &l.lits, &r.lits);
   }
   nqueue.pop_back().unwrap()
 }

  fn new_ua(solver :&mut SatSolver, new_vars :&[Lit], rhs :u32, left :&[Lits], right :&[Lits]) {
     // i = 0
     for j in 0..(rhs.min(right.len())) {
       solver.add_clause(vec![right[j].inverse(), new_vars[j]]);
     }
     
     // j = 0
     for i in 0..(rhs.min(left.len())) {
       solver.add_clause(vec![left[i].inverse(), new_vars[i]]);
     }

     // i,j > 0
     for i in 1..=kmin {
       for j in 1..=((rhs - i).min(right.len())) {
         solver.add_clause(vec![left[i-1].inverse(), right[j-1].inverse(), new_vars[i+j-1]]);
       }
     }
  }

  pub fn increase_bound(&mut self, solver :&mut SatSolver, new_bound :u32) {
    let kmin = (new_bound+1).min(self.nof_input);
    if kmin <= self.lits.len() { return; }
    self.left.increase_bound(solver, new_bound);
    self.right.increase_bound(solver, new_bound);
    Self::increase_ua(solver, &mut self.lits, &self.left.lits, &self.right.lits, kmin);
  }

  fn increase_ua(solver :&mut SatSolver, ov :&mut Vec<Lit>, av :&[Lit], bv :&[Lit], rhs :u32) {
    let last = ov.len();
    while last.len() < rhs { ov.push(solver.new_var()); }

    let maxi = rhs.min(av.len());
    let maxj = rhs.min(bv.len());

    // i = 0
    for j in last..maxj {
      solver.add_clause(vec![bv[j].inverse(), ov[j]]);
    }

    // j = 0
    for i in last..maxi {
      solver.add_clause(vec![av[i].inverse(), ov[i]);
    }

    // i,j > 0
    for i in 1..=maxi {
      let maxj = (rhs-i).min(bv.len());
      let minj = (last - i + 1).max(1);
      for j in minj..=maxj {
        solver.add_clause(vec![av[i-1].inverse(), bv[j-1].inverse(), ov[i+j-1]]);
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
