use crate::constraints::Totalizer;
use crate::traits::*;
use std::collections::HashMap;
use std::hash::Hash;

pub struct RelaxableCardinalityConstraints<L: Lit + Hash + PartialEq + Eq> {
    sums: HashMap<Bool<L>, (Totalizer<L>, u32)>,
}

impl<L: Lit> RelaxableCardinalityConstraints<L> {
    pub fn new() -> Self {
        RelaxableCardinalityConstraints {
            sums: HashMap::new(),
        }
    }

    pub fn assumptions<'a>(&'a self) -> impl IntoIterator<Item = Bool<L>> + 'a {
        self.sums.keys().copied()
    }

    pub fn increase_sum_bound(&mut self, s: &mut impl SatInstance<L>, x: Bool<L>) {
        if let Some((mut tot, bound)) = self.sums.remove(&x) {
            tot.increase_bound(s, bound + 1);
            self.add_soft_card(tot, bound + 1);
        } else {
            panic!();
        }
    }

    pub fn relax_set(&mut self, s: &mut impl SatInstance<L>, xs: impl IntoIterator<Item = L>) {
        let relax = xs.into_iter().map(Bool::Lit).map(|l| !l);
        let count = Totalizer::count(s, relax, 1);
        self.add_soft_card(count, 1); /* note that this does nothing if relax.len() == 1. */
    }

    /// Add a soft cardinality constraint.
    fn add_soft_card(&mut self, tot: Totalizer<L>, bound: u32) {
        if (bound as usize) < tot.rhs().len() {
            self.sums.insert(!tot.rhs()[bound as usize], (tot, bound));
        } // if not, the clauses are a lost cause, their full cost is already added.
    }
}

/// Soft clauses implemented by
/// relaxable cardinality constraints.
pub struct RC2SoftClauses<L: Lit + Hash + PartialEq + Eq> {
    cost: u32,
    maxcost: u32,
    selectors: HashMap<Bool<L>, ()>,
    cardinality: RelaxableCardinalityConstraints<L>,
}

impl<L: Lit + core::fmt::Debug> RC2SoftClauses<L> {
    /// Empty set of soft clauses.
    pub fn new() -> Self {
        RC2SoftClauses {
            cost: 0,
            maxcost: 0,
            selectors: HashMap::new(),
            cardinality: RelaxableCardinalityConstraints::new(),
        }
    }

    /// Add a (unit weight) clause to the soft clause set. Also adds the clause to the given SAT
    /// solver with an added guard literal.
    pub fn add_soft_clause<S: SatInstance<L>>(&mut self, solver: &mut S, mut cl: Vec<Bool<L>>) {
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

        self.maxcost += 1;
        self.selectors.insert(selector, ());
    }

    /// Increase the cost until the instance is satisfiable.  The `sat` parameter is used to add
    /// new cardinality constraints to the SAT instance.  The `solve` parameter is called using the
    /// `sat` and a set of assumptions and should return a model or a `Vec<L>` containing an
    /// unsat subset of the given assumptions.  If the `solve` parameter returns an empty unsat
    /// subset, then the whole instance is unsatifisable, and `increase_cost` returns `None`.  If
    /// the `solve` parameter returns a model, then the instance is satisfiable and,
    /// `increase_cost` returns a tuple containing the cost and the model.
    pub fn increase_cost<'a, S: SatInstance<L> + SatSolverWithCore<Lit = L>>(
        &mut self,
        sat: &'a mut S,
    ) -> Option<(u32, Box<dyn SatModel<Lit = L> + 'a>)> {
        loop {
            let mut assumptions = self
                .selectors
                .keys()
                .copied()
                .chain(self.cardinality.assumptions());
            let result = {
                /*let _p = hprof::enter("sat solve"); */
                sat.solve_with_assumptions(&mut assumptions)
            };
            drop(assumptions);

            match result {
                SatResultWithCore::Sat(ref _model) => {
                    // It is a current limitation of the Rust compiler that we cannot return the
                    // model that has already been borrowed from `sat`, because then we would
                    // extend that specific borrow to cover the full lifetime in the function
                    // signature. Since we dynamically decide whether to return the value or to
                    // release it and make a new borrow (adding constraints and solving again in
                    // the match arm below), the lifetimes are not compatible.
                    //
                    // This is fixed by an experimental version of the Rust borrow checker, called
                    // Polonius, which is available in the nightly compiler version:
                    //   `cargo +nightly rustc -- -Zpolonius`
                    //
                    // For a MiniSAT-like SAT solver this should not be much of a problem, as
                    // solving again would make all the same assignments on the first try (phase
                    // saving) and therefore find the same model without search.

                    drop(result);
                    let mut assumptions = self
                        .selectors
                        .keys()
                        .copied()
                        .chain(self.cardinality.assumptions());
                    if let SatResultWithCore::Sat(model) =
                        sat.solve_with_assumptions(&mut assumptions)
                    {
                        return Some((self.cost, model));
                    } else {
                        panic!();
                    }
                }
                SatResultWithCore::Unsat(ref core) => {
                    // This clone becomes unnecessary with the Polonius borrow checker, see comment
                    // above.
                    let core = core.clone().to_vec();
                    drop(result);

                    if core.len() == 0 {
                        return None;
                    }

                    self.cost += 1;
                    println!("COST {:?}/{}", self.cost, self.maxcost);
                    debug_assert!(core
                        .iter()
                        .copied()
                        .map(Bool::Lit)
                        .all(|l| self.selectors.contains_key(&l)
                            || self.cardinality.sums.contains_key(&l)));

                    if core.len() == 1 {
                        sat.add_clause([!core[0]].iter().cloned());
                    }

                    for l in core.iter().copied().map(Bool::Lit) {
                        if self.selectors.remove(&l).is_none() {
                            self.cardinality.increase_sum_bound(sat, l);
                        }
                    }

                    self.cardinality.relax_set(sat, core);
                }
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solvers::minisat::*;
    use crate::symbolic::*;

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
        soft.add_soft_clause(&mut s, vec![!x[6], x[8]]);
        soft.add_soft_clause(&mut s, vec![x[6], !x[8]]);
        soft.add_soft_clause(&mut s, vec![x[2], x[4]]);
        soft.add_soft_clause(&mut s, vec![!x[4], x[5]]);
        soft.add_soft_clause(&mut s, vec![x[7], x[5]]);
        soft.add_soft_clause(&mut s, vec![!x[7], x[5]]);
        soft.add_soft_clause(&mut s, vec![!x[5], x[3]]);
        soft.add_soft_clause(&mut s, vec![!x[3]]);

        let result = soft.increase_cost(&mut s);

        if let Some((cost, model)) = result {
            assert!(cost == 2);
            let values = x
                .iter()
                .enumerate()
                .map(|(i, x)| {
                    if model.value(x) {
                        format!(" x{}", i)
                    } else {
                        format!("!x{}", i)
                    }
                })
                .collect::<Vec<_>>();
            println!("Values: {:?}", values);
        } else {
            panic!("unsat");
        }
    }
}
