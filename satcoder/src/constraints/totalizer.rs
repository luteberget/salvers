use crate::*;
use std::collections::VecDeque;

/// Incremental totalizer encoding of cardinality constraint.
pub struct Totalizer<L: Lit> {
    lits: Vec<Bool<L>>,
    nof_input: u32,
    left: Option<Box<Self>>,
    right: Option<Box<Self>>,
}

impl<L: Lit> Totalizer<L> {
    fn singleton(l: Bool<L>) -> Self {
        Totalizer {
            lits: vec![l],
            nof_input: 1,
            left: None,
            right: None,
        }
    }

    /// Produce a totalizer cardinality constraint by counting the given literals up to the
    /// bound given by the `rhs` parameter.
    pub fn count<S: SatInstance<L>>(
        solver: &mut S,
        items: impl IntoIterator<Item = Bool<L>>,
        rhs: u32,
    ) -> Self {
        Self::merge(solver, items.into_iter().map(Self::singleton), rhs)
    }

    /// Merge a set of totalizers into a new one with the upper bound given by the `rhs` parameter.
    pub fn merge<S: SatInstance<L>>(
        solver: &mut S,
        items: impl IntoIterator<Item = Self>,
        rhs: u32,
    ) -> Self {
        let mut nqueue = items.into_iter().collect::<VecDeque<_>>();

        while nqueue.len() > 1 {
            let mut l = nqueue.pop_front().unwrap();
            let mut r = nqueue.pop_front().unwrap();
            l.increase_bound(solver, rhs);
            r.increase_bound(solver, rhs);
            let kmin = (l.nof_input + r.nof_input).min(rhs + 1);

            let mut new_lits = Vec::new();
            add_totalizer_constraints(solver, &mut new_lits, kmin, &l.lits, &r.lits);

            nqueue.push_back(Totalizer {
                lits: new_lits,
                nof_input: l.nof_input + r.nof_input,
                left: Some(Box::new(l)),
                right: Some(Box::new(r)),
            });
        }

        assert!(nqueue.len() == 1);
        nqueue.pop_back().unwrap()
    }

    /// Get the literals represeting the count in unary encoding.
    /// Forcing the literal `!rhs[i]` to be true makes `rhs <= i`.
    pub fn rhs(&self) -> &[Bool<L>] {
        &self.lits
    }

    /// Increase the bound of the totalizer. Adds variables and constraints using the given solver.
    pub fn increase_bound<S: SatInstance<L>>(&mut self, solver: &mut S, rhs: u32) {
        let kmin = (rhs + 1).min(self.nof_input);
        if kmin as usize <= self.lits.len() {
            return;
        }
        let left = self.left.as_mut().unwrap();
        let right = self.right.as_mut().unwrap();
        left.increase_bound(solver, rhs);
        right.increase_bound(solver, rhs);
        add_totalizer_constraints(solver, &mut self.lits, kmin, &left.lits, &right.lits);
    }
}

fn add_totalizer_constraints<L: Lit, S: SatInstance<L>>(
    solver: &mut S,
    ov: &mut Vec<Bool<L>>,
    rhs: u32,
    av: &[Bool<L>],
    bv: &[Bool<L>],
) {
    let prev_ov_size = ov.len();
    while ov.len() < rhs as usize {
        ov.push(solver.new_var());
    }

    let maxj = (rhs as usize).min(bv.len());
    for j in prev_ov_size..maxj {
        solver.add_clause([!bv[j], ov[j]].iter().cloned());
    }

    let maxi = (rhs as usize).min(av.len());
    for i in prev_ov_size..maxi {
        solver.add_clause([!av[i], ov[i]].iter().cloned());
    }

    for i in 1..=maxi {
        let maxj = (rhs as isize - i as isize).min(bv.len() as isize) as usize;
        let minj = (prev_ov_size as isize - i as isize + 1).max(1) as usize;
        for j in minj..=maxj {
            solver.add_clause([!av[i - 1], !bv[j - 1], ov[i + j - 1]].iter().cloned());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use minisat::*;

    #[test]
    fn one_of_each() {
        let mut solver = Solver::new();
        let x1 = solver.new_var();
        let x2 = solver.new_var();
        let totalizer1 = Totalizer::count(&mut solver, [x1, x2].iter().cloned(), 2);
        let totalizer2 = Totalizer::count(&mut solver, [!x1, !x2].iter().cloned(), 2);
        solver.add_clause([!totalizer1.rhs()[1]].iter().cloned());
        solver.add_clause([!totalizer2.rhs()[1]].iter().cloned());
        let model = solver.solve().ok().unwrap();
        println!("value x1 {:?} = {:?}", x1, model.value(&x1));
        println!("value x2 {:?} = {:?}", x2, model.value(&x2));
        assert!(
            [x1, x2]
                .iter()
                .map(|x| if model.value(x) { 1 } else { 0 })
                .sum::<usize>()
                == 1
        );
    }

    #[test]
    fn partition_10() {
        let mut solver = Solver::new();
        let xs = (0..10).map(|_| solver.new_var()).collect::<Vec<_>>();
        solver.add_clause([xs[0], xs[1]].iter().cloned());
        solver.add_clause([xs[2], xs[3]].iter().cloned());
        solver.add_clause([xs[4], xs[5]].iter().cloned());
        solver.add_clause([xs[6], xs[7]].iter().cloned());
        solver.add_clause([xs[8], xs[9]].iter().cloned());

        let totalizer = Totalizer::count(&mut solver, xs.iter().map(|x| *x), 7);
        solver.add_clause([!totalizer.rhs()[7]].iter().cloned()); // there is not 9 as

        let totalizer = Totalizer::count(&mut solver, xs.iter().map(|x| !*x), 3);
        solver.add_clause([!totalizer.rhs()[3]].iter().cloned()); // there is not 3 bs

        // At least one is true
        let model = solver.solve().ok().unwrap();
        println!(
            "values {:?}",
            xs.iter()
                .map(|x| if model.value(x) { 'A' } else { 'B' })
                .collect::<Vec<char>>()
        );
    }

    #[test]
    fn combinations() {
        for num_vars in 1..10 {
            for count_bound in 0..=num_vars {
                for maximum in 0..=count_bound {
                    for asserted in 0..=num_vars {
                        println!(
                            "n{} bound{} max{} assert{}",
                            num_vars, count_bound, maximum, asserted
                        );

                        let mut solver = Solver::new();
                        let xs = (0..num_vars).map(|_| solver.new_var()).collect::<Vec<_>>();
                        for a in 0..asserted {
                            solver.add_clause(Some(xs[num_vars - 1 - a].into()));
                        }

                        let totalizer =
                            Totalizer::count(&mut solver, xs.iter().cloned(), count_bound as u32);
                        assert!(totalizer.rhs().len() == (xs.len()).min(count_bound + 1));
                        if (maximum as usize) < totalizer.rhs().len() {
                            solver.add_clause(Some(!totalizer.rhs()[maximum as usize]));
                        }

                        let should_succeed = asserted <= maximum;
                        if should_succeed {
                            let model = solver.solve().ok().unwrap();
                            let values = xs.iter().map(|v| model.value(v)).collect::<Vec<_>>();
                            println!("  values {:?}", values);
                            assert!(
                                values.iter().map(|x| if *x { 1 } else { 0 }).sum::<usize>()
                                    <= maximum
                            );
                        } else {
                            assert!(solver.solve().is_err());
                        }
                    }
                }
            }
        }
    }
}
