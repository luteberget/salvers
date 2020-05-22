use sattrait::*;
use totalizer::*;
use std::collections::HashMap;
use std::hash::Hash;

/// Soft clauses implemented by
/// relaxable cardinality constraints.
pub struct RC2SoftClauses<L: Lit + Hash + PartialEq + Eq> {
    cost: u32,
    selectors: HashMap<L, ()>,
    sums: HashMap<L, (Totalizer<L>, u32)>,
}

impl<L: Lit + Hash + PartialEq + Eq> RC2SoftClauses<L> {
    /// Empty set of soft clauses.
    pub fn new() -> Self {
        RC2SoftClauses {
            cost: 0,
            selectors: HashMap::new(),
            sums: HashMap::new(),
        }
    }

    /// Add a (unit weight) clause to the soft clause set. Also adds the clause to the given SAT
    /// solver with an added guard literal.
    pub fn add_soft_clause<S: SatInstance<L>>(&mut self, solver: &mut S, mut cl: Vec<L>) {
        let selector = if cl.len() == 0 {
            panic!()
        } else if cl.len() == 1 {
            cl[0]
        } else {
            let s = solver.new_var();
            cl.push(!s);
            solver.add_clause(cl);
            s
        };

        self.selectors.insert(selector, ());
    }

    /// Increase the cost until the instance is satisfiable.  The `sat` parameter is used to add
    /// new cardinality constraints to the SAT instance.  The `solve` parameter is called using the
    /// `sat` and a set of assumptions and should return a model or a `Vec<L>` containing an
    /// unsat subset of the given assumptions.  If the `solve` parameter returns an empty unsat
    /// subset, then the whole instance is unsatifisable, and `increase_cost` returns `None`.  If
    /// the `solve` parameter returns a model, then the instance is satisfiable and,
    /// `increase_cost` returns a tuple containing the cost and the model.
    pub fn increase_cost<S: SatInstance<L>, F>(
        &mut self,
        sat: &mut S,
        mut solve: F,
    ) -> Option<u32>
    where
        F: FnMut(&mut S, &mut dyn Iterator<Item = L>) -> Result<(), Vec<L>>,
    {
        loop {
            let assumptions = self.selectors.keys().chain(self.sums.keys()).cloned();
            match solve(sat, &mut assumptions.into_iter()) {
                Ok(_) => {
                    return Some(self.cost);
                }
                Err(core) if core.len() == 0 => {
                    return None;
                },
                Err(core) => {
                    self.cost += 1;
                    debug_assert!(core.iter().all(|l| self.selectors.contains_key(l) || self.sums.contains_key(l)));
                    if core.len() == 1 { 
                        sat.add_clause([!core[0]].iter().cloned());
                    }
                    for l in core.iter() {
                        self.selectors.remove(l);
                        if let Some((mut tot, bound)) = self.sums.remove(l) {
                            tot.increase_bound(sat, bound + 1);
                            self.add_soft_card(tot, bound + 1);
                        }
                    }
                    let relax = core.iter().map(|l| !*l);
                    let count = Totalizer::count(sat, relax, 1);
                    self.add_soft_card(count, 1); // note that this does nothing if relax.len() == 1.
                }
            };
        }
    }

    /// Add a soft cardinality constraint.
    fn add_soft_card(&mut self, tot: Totalizer<L>, bound: u32) {
        if (bound as usize) < tot.rhs().len() {
            self.sums.insert(!tot.rhs()[bound as usize], (tot, bound));
        } // if not, the clauses are a lost cause, their full cost is already added.
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use minisat::*;

    #[test]
    pub fn example0() {
        // pure maxsat formula example from J. Marques-Silva's slides.
        let mut s = Solver::new();
        let x = (0..=8).map(|_| s.new_var()).collect::<Vec<_>>();

        let mut soft = RC2SoftClauses::new();
        soft.add_soft_clause(&mut s, vec![x[6], x[2]]);
        soft.add_soft_clause(&mut s, vec![!x[6], x[2]]);
        soft.add_soft_clause(&mut s, vec![!x[2], x[1]]);
        soft.add_soft_clause(&mut s, vec![!x[1]]);
        soft.add_soft_clause(&mut s, vec![!x[6],x[8]]);
        soft.add_soft_clause(&mut s, vec![x[6],!x[8]]);
        soft.add_soft_clause(&mut s, vec![x[2],x[4]]);
        soft.add_soft_clause(&mut s, vec![!x[4],x[5]]);
        soft.add_soft_clause(&mut s, vec![x[7],x[5]]);
        soft.add_soft_clause(&mut s, vec![!x[7],x[5]]);
        soft.add_soft_clause(&mut s, vec![!x[5],x[3]]);
        soft.add_soft_clause(&mut s, vec![!x[3]]);

        let result = soft.increase_cost(&mut s, |s, assumptions| {
            s.solve_under_assumptions(assumptions)
                .map(|_| ())
                .map_err(|b| b.collect())
        });

        assert!(result.is_some());
        assert!(result.unwrap() == 2);

    }
}

