use crate::{SatInstance, SatSolver, SatSolverWithCore, SatResult, SatResultWithCore, Bool, SatModel};
pub type Solver = dpllt::DplltSolver<dpllt::NullTheory>;
pub use dpllt::*;
use dpllt::Lit as SLit;
use dpllt::Var as SVar;

impl crate::Var for SVar {}

impl crate::Lit for SLit {
    type Var = SVar;

    fn into_var(self) -> (Self::Var, bool) {
        (self.var(), self.sign())
    }

    fn from_var_sign(v: Self::Var, sign: bool) -> Self {
        SLit::new(v, sign)
    }
}

impl<T: dpllt::Theory> SatInstance<SLit> for dpllt::DplltSolver<T> {
    fn new_var(&mut self) -> Bool<SLit> {
        Bool::Lit(self.new_var_default())
    }

    fn add_clause<IL: Into<Bool<SLit>>, I: IntoIterator<Item = IL>>(&mut self, clause: I) {
        let mut s_clause :Vec<SLit> = Vec::new();
        for l in clause.into_iter() {
            match l.into() {
                Bool::Const(true) => { return; },
                Bool::Const(false) => {},
                Bool::Lit(l) => { s_clause.push(l); },
            }
        }
        self.add_clause(s_clause);
    }
}

struct Model<'a, T> {
    solver: &'a dpllt::DplltSolver<T>,
}

impl<'a, T: dpllt::Theory> SatModel for Model<'a, T> {
    type Lit = SLit;

    fn lit_value(&self, l: &Self::Lit) -> bool {
        self.solver.value(*l)
    }
}

impl<T: dpllt::Theory> SatSolver for dpllt::DplltSolver<T> {
    type Lit = SLit;

    fn solve<'a>(&'a mut self) -> SatResult<'a, Self::Lit> {
        let result = self.solve();
        if result == dpllt::LBOOL_TRUE {
            SatResult::Sat(Box::new(Model { solver: self }))
        } else if result == dpllt::LBOOL_FALSE {
            SatResult::Unsat
        } else {
            panic!()
        }
    }
}

impl<T: dpllt::Theory> SatSolverWithCore for dpllt::DplltSolver<T> {
    type Lit = SLit;

    fn solve_with_assumptions<'a>(
        &'a mut self,
        assumptions: impl IntoIterator<Item = Bool<Self::Lit>>,
    ) -> SatResultWithCore<'a, Self::Lit> {
        self.set_assumptions(assumptions.into_iter().filter_map(|l| match l.into() {
            Bool::Const(true) => None,
            Bool::Const(false) => panic!(),
            Bool::Lit(l) => Some(l),
        }));

        let result = self.solve();
        if result == dpllt::LBOOL_TRUE {
            self.set_assumptions(std::iter::empty());
            SatResultWithCore::Sat(Box::new(Model { solver: self }))
        } else if result == dpllt::LBOOL_FALSE {
            self.set_assumptions(std::iter::empty());
            SatResultWithCore::Unsat(self.conflict.clone().into_boxed_slice())
        } else {
            panic!()
        }
    }
}
