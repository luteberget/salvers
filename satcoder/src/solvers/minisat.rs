//! [MiniSAT](http://minisat.se/)
use crate::*;

pub use ::minisat::Lit;
pub use ::minisat::Solver;
pub use ::minisat::Var;

pub type Bool = crate::Bool<Lit>;

impl crate::Var for Var {}
impl crate::Lit for Lit {
    type Var = Var;

    fn into_var(self) -> (Self::Var, bool) {
        Lit::var(self)
    }

    fn from_var_sign(v: Self::Var, sign: bool) -> Self {
        Lit::from_var_sign(v, sign)
    }
}

impl SatInstance<Lit> for ::minisat::Solver {
    fn new_var(&mut self) -> Bool {
        Bool::Lit(self.new_lit())
    }

    fn add_clause<IL: Into<Bool>, I: IntoIterator<Item = IL>>(&mut self, clause: I) {
        if let Ok(lits) = clause
            .into_iter()
            .filter_map(|i| match i.into() {
                Bool::Lit(l) => Some(Ok(l)),
                Bool::Const(false) => None,
                Bool::Const(true) => Some(Err(())),
            })
            .collect::<Result<Vec<Lit>, ()>>()
        {
            ::minisat::Solver::add_clause(self, lits);
        }
    }
}

impl SatSolverWithCore for ::minisat::Solver {
    type Lit = Lit;

    fn solve_with_assumptions<'a>(
        &'a mut self,
        assumptions: impl IntoIterator<Item = crate::Bool<Self::Lit>>,
    ) -> SatResultWithCore<'a, Self::Lit> {
        match ::minisat::Solver::solve_under_assumptions(
            self,
            assumptions.into_iter().filter_map(|i| match i.into() {
                Bool::Const(false) => panic!("unsat"),
                Bool::Const(true) => None,
                Bool::Lit(l) => Some(l),
            }),
        ) {
            Ok(m) => SatResultWithCore::Sat(Box::new(m)),
            Err(c) => {
                // MiniSAT gives a conflict clause, we want an
                // unsat core, so invert each literal.
                let vec = c.iter().map(|c| !c).collect::<Vec<_>>();

                SatResultWithCore::Unsat(vec.into_boxed_slice())
            }
        }
    }
}

impl SatSolver for ::minisat::Solver {
    type Lit = Lit;

    fn solve<'a>(&'a mut self) -> SatResult<'a, Self::Lit> {
        match self.solve_with_assumptions(std::iter::empty()) {
            SatResultWithCore::Sat(m) => SatResult::Sat(m),
            SatResultWithCore::Unsat(_) => SatResult::Unsat,
        }
    }
}

impl<'a> SatModel for ::minisat::Model<'a> {
    type Lit = Lit;

    fn lit_value(&self, l: &Self::Lit) -> bool {
        ::minisat::Model::lit_value(self, l)
    }
}

pub struct MiniSatRandomPolarity {
    solver: ::minisat::Solver,
}

impl MiniSatRandomPolarity {
    pub fn new() -> Self {
        Self {
            solver: minisat::Solver::new(),
        }
    }
}

impl Default for MiniSatRandomPolarity {
    fn default() -> Self {
        Self::new()
    }
}

impl SatInstance<Lit> for MiniSatRandomPolarity {
    fn new_var(&mut self) -> Bool {
        use std::hash::Hasher;
        let lit = self.solver.new_lit();
        let mut s = std::collections::hash_map::DefaultHasher::new();
        lit.hash(&mut s);
        let pol = s.finish() % 2 == 0;
        self.solver.set_polarity(lit, pol);
        Bool::Lit(lit)
    }

    fn add_clause<IL: Into<Bool>, I: IntoIterator<Item = IL>>(&mut self, clause: I) {
        SatInstance::add_clause(&mut self.solver, clause)
    }
}

impl SatSolverWithCore for MiniSatRandomPolarity {
    type Lit = Lit;

    fn solve_with_assumptions(
        &mut self,
        assumptions: impl IntoIterator<Item = crate::Bool<Self::Lit>>,
    ) -> SatResultWithCore<'_, Self::Lit> {
        SatSolverWithCore::solve_with_assumptions(&mut self.solver, assumptions)
    }
}

impl SatSolver for MiniSatRandomPolarity {
    type Lit = Lit;

    fn solve(&mut self) -> SatResult<'_, Self::Lit> {
        SatSolver::solve(&mut self.solver)
    }
}
