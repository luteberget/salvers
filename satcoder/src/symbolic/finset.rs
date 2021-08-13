use crate::{constraints::*, symbolic::*, *};

#[derive(Debug, Clone)]
pub struct FinSet<L: Lit, T>(Vec<(Bool<L>, T)>);

impl<L: Lit, T> FinSet<L, T> {
    pub fn from_vec_unsafe(xs: Vec<(Bool<L>, T)>) -> Self {
        Self(xs)
    }
    pub fn new(solver: &mut impl SatInstance<L>, mut xs: Vec<T>) -> Self {
        if xs.len() == 0 {
            panic!("Symbolic value cannot be initialized from empty list.");
        } else if xs.len() == 1 {
            FinSet(vec![(true.into(), xs.remove(0))])
        } else if xs.len() == 2 {
            let l = solver.new_var();
            let a = xs.remove(0);
            let b = xs.remove(0);
            FinSet(vec![(l, a), (!l, b)])
        } else {
            let lits = xs.iter().map(|_| solver.new_var()).collect::<Vec<_>>();
            solver.assert_exactly_one(lits.iter().copied());
            FinSet(lits.into_iter().zip(xs.into_iter()).collect())
        }
    }

    pub fn domain(&self) -> impl Iterator<Item = &T> {
        self.0.iter().map(|(_, v)| v)
    }
}

impl<L: Lit, T: Eq> FinSet<L, T> {
    pub fn has_value(&self, a: &T) -> Bool<L> {
        for (v, x) in &self.0 {
            if x == a {
                return *v;
            }
        }
        false.into()
    }
}

impl<'a, L: Lit, FT: 'a> Symbolic<'a, L> for FinSet<L, FT> {
    type T = &'a FT;

    fn interpret(&'a self, m: &dyn SatModel<Lit = L>) -> Self::T {
        for (v, x) in &self.0 {
            if m.value(v) {
                return x;
            }
        }

        //unreachable!("FinSet encoding is inconsistent -- could not determine value from model.")
        // Cadical returns undecided sometimes, will return the first value here as a temporary
        // workaround.
        return &self.0[0].1;
    }
}
