use sattrait::*;
use std::collections::VecDeque;

/// Incremental totalizer encoding of cardinality constraint.
pub struct Totalizer<L: Lit> {
    lits: Vec<L>,
    nof_input: u32,
    left: Option<Box<Self>>,
    right: Option<Box<Self>>,
}

impl<L: Lit> Totalizer<L> {
    fn singleton(l: L) -> Self {
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
        items: impl IntoIterator<Item = L>,
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
    ///
    /// Typically used as: 
    ///  * If the literal `!rhs[i]` is true, then `rhs <= i`.
    ///  * If the literal `rhs[i-1]` is true, then `rhs >= i`.
    pub fn rhs(&self) -> &[L] {
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
    ov: &mut Vec<L>,
    rhs: u32,
    av: &[L],
    bv: &[L],
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

    for i in 1..maxi {
        let maxj = (rhs as isize - i as isize).min(bv.len() as isize) as usize;
        let minj = (prev_ov_size as isize - i as isize + 1).max(1) as usize;
        for j in minj..=maxj {
            solver.add_clause([!av[i - 1], !bv[j - 1], ov[i + j - 1]].iter().cloned());
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
