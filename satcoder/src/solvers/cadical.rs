//! [CaDiCaL SAT Solver](http://fmv.jku.at/cadical/)

use crate::*;

pub type Bool = crate::traits::Bool<Lit>;
pub use self::Cadical as Solver;

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Lit(i32);

impl std::ops::Not for Lit {
    type Output = Lit;

    fn not(self) -> Self::Output {
        Lit(-self.0)
    }
}

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Var(u32);

impl crate::Var for Var {}

impl crate::Lit for Lit {
    type Var = Var;

    fn into_var(self) -> (Self::Var, bool) {
        (Var(self.0.abs() as u32), self.0 < 0)
    }

    fn from_var_sign(v: Self::Var, sign: bool) -> Self {
        Lit(if sign { -(v.0 as i32) } else { v.0 as i32 })
    }
}



pub struct Cadical {
    pub cadical: ::cadical::Solver,
    next_var: u32,
}

impl std::fmt::Debug for Cadical {
    
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Cadical instance ({}) {{ variables: {}, clauses: {} }}",
            self.cadical.signature(),
            self.cadical.num_variables(),
            self.cadical.num_clauses()
        )
    }
}

impl Cadical {
    pub fn new() -> Self {
        Cadical {
            cadical: ::cadical::Solver::new(),
            next_var: 1,
        }
    }
    pub fn with_config(config: &str) -> Result<Self, ::cadical::Error> {
        Ok(Cadical {
            cadical: ::cadical::Solver::with_config(config)?,
            next_var: 1,
        })
    }
}

impl SatInstance<Lit> for Cadical {
    fn new_var(&mut self) -> Bool {
        let l = Bool::Lit(Lit(self.next_var as i32));
        self.next_var += 1;
        l
    }

    fn add_clause<IL: Into<Bool>, I: IntoIterator<Item = IL>>(&mut self, clause: I) {
        let lits = clause
            .into_iter()
            .filter_map(|l| match l.into() {
                Bool::Const(false) => None,
                Bool::Const(true) => Some(Err(())),
                Bool::Lit(Lit(x)) => Some(Ok(x)),
            })
            .collect::<Result<Vec<_>, ()>>();
        if let Ok(lits) = lits {
            self.cadical.add_clause(lits.iter().cloned());
        }
    }
}

impl SatSolver for Cadical {
    type Lit = Lit;

    fn solve<'a>(&'a mut self) -> SatResult<'a, Self::Lit> {
        match self.cadical.solve() {
            Some(true) => SatResult::Sat(Box::new(CadicalModel { instance: self })),
            Some(false) => SatResult::Unsat,
            None => {
                panic!("Resource limits are not supported yet by satcoder (use cadical directly)")
            }
        }
    }
}

impl SatSolverWithCore for Cadical {
    type Lit = Lit;

    fn solve_with_assumptions<'a>(
        &'a mut self,
        assumptions: impl IntoIterator<Item = Bool>,
    ) -> SatResultWithCore<'a, Self::Lit> {
        let assumptions = assumptions
            .into_iter()
            .filter_map(|l| match l {
                Bool::Const(true) => None,
                Bool::Const(false) => panic!(),
                Bool::Lit(l) => Some(l),
            })
            .collect::<Vec<_>>();

        match self.cadical.solve_with(assumptions.iter().map(|&Lit(l)| l)) {
            Some(true) => SatResultWithCore::Sat(Box::new(CadicalModel { instance: self })),
            Some(false) => {
                let core = assumptions
                    .into_iter()
                    .filter(|l| self.cadical.failed(l.0))
                    .collect::<Vec<_>>();
                SatResultWithCore::Unsat(core.into_boxed_slice())
            }
            None => {
                panic!("Resource limits are not supported yet by satcoder (use cadical directly)")
            }
        }
    }
}

struct CadicalModel<'a> {
    instance: &'a Cadical,
}

impl<'a> SatModel for CadicalModel<'a> {
    type Lit = Lit;

    fn lit_value(&self, l: &Self::Lit) -> bool {
        self.instance.cadical.value(l.0).unwrap()
    }
}
