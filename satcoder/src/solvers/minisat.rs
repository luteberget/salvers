use crate::*;

use ::minisat::Lit as SLit;
use ::minisat::Var as SVar;

impl Var for SVar {}
impl Lit for SLit {
    type Var = SVar;

    fn into_var(self) -> (Self::Var, bool) {
        SLit::var(self)
    }

    fn from_var_sign(v: Self::Var, sign: bool) -> Self {
        SLit::from_var_sign(v, sign)
    }
}

impl SatInstance<SLit> for ::minisat::Solver {
    fn new_var(&mut self) -> Bool<SLit> {
        Bool::Lit(self.new_lit())
    }

    fn add_clause<IL: Into<Bool<SLit>>, I: IntoIterator<Item = IL>>(&mut self, clause: I) {
        ::minisat::Solver::add_clause(
            self,
            clause.into_iter().filter_map(|i| match i.into() {
                Bool::Lit(l) => Some(l),
                Bool::Const(true) => None,
                Bool::Const(false) => panic!("unsat"),
            }),
        )
    }
}

impl SatSolverWithCore for ::minisat::Solver {
    type Lit = SLit;

    fn solve_with_assumptions<'a>(
        &'a mut self,
        assumptions: impl IntoIterator<Item = Bool<Self::Lit>>,
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
                let vec = c.iter().collect::<Vec<_>>();
                SatResultWithCore::Unsat(vec.into_boxed_slice())
            }
        }
    }
}

impl SatSolver for ::minisat::Solver {
    type Lit = SLit;

    fn solve<'a>(&'a mut self) -> SatResult<'a, Self::Lit> {
        match self.solve_with_assumptions(std::iter::empty()) {
            SatResultWithCore::Sat(m) => SatResult::Sat(m),
            SatResultWithCore::Unsat(_) => SatResult::Unsat,
        }
    }
}

impl<'a> SatModel for ::minisat::Model<'a> {
    type L = SLit;

    fn lit_value(&self, l: &Self::L) -> bool {
        ::minisat::Model::lit_value(self, l)
    }
}
