use crate::*;

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct CdcLit(i32);

impl std::ops::Not for CdcLit {
    type Output = CdcLit;

    fn not(self) -> Self::Output {
        CdcLit(-self.0)
    }
}

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct CdcVar(u32);

impl Var for CdcVar {}

impl Lit for CdcLit {
    type Var = CdcVar;

    fn into_var(self) -> (Self::Var, bool) {
        (CdcVar(self.0.abs() as u32), self.0 < 0)
    }

    fn from_var_sign(v: Self::Var, sign: bool) -> Self {
        CdcLit(if sign { -(v.0 as i32) } else { v.0 as i32 })
    }
}

pub struct Cadical {
    pub cadical: ::cadical::Solver,
    next_var: u32,
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

impl SatInstance<CdcLit> for Cadical {
    fn new_var(&mut self) -> Bool<CdcLit> {
        let l = Bool::Lit(CdcLit(self.next_var as i32));
        self.next_var += 1;
        l
    }

    fn add_clause<IL: Into<Bool<CdcLit>>, I: IntoIterator<Item = IL>>(&mut self, clause: I) {
        self.cadical.add_clause(clause.into_iter().filter_map(|l| match l.into() {
            Bool::Const(true) => None,
            Bool::Const(false) => panic!(),
            Bool::Lit(CdcLit(x)) => Some(x),
        }))
    }
}

impl SatSolver for Cadical {
    type Lit = CdcLit;

    fn solve<'a>(&'a mut self) -> SatResult<'a, Self::Lit> {
        match self.cadical.solve() {
            Some(true) => SatResult::Sat(Box::new(CadicalModel { instance: self })),
            Some(false) => SatResult::Unsat,
            None => panic!("Resource limits are not supported yet by satcoder (use cadical directly)"),
        }
    }
}

impl SatSolverWithCore for Cadical {
    type Lit = CdcLit;

    fn solve_with_assumptions<'a>(
        &'a mut self,
        assumptions: impl IntoIterator<Item = Bool<Self::Lit>>,
    ) -> SatResultWithCore<'a, Self::Lit> {
       let assumptions = assumptions.into_iter().filter_map(|l| match l {
            Bool::Const(true) => None,
            Bool::Const(false) => None,
            Bool::Lit(l) => Some(l),
        }).collect::<Vec<_>>();

        match self.cadical.solve_with(assumptions.iter().map(|&CdcLit(l)| l)) {
            Some(true) => SatResultWithCore::Sat(Box::new(CadicalModel { instance: self })),
            Some(false) => {
                let core = assumptions.into_iter().filter(|l| self.cadical.failed(l.0)).collect::<Vec<_>>();
                SatResultWithCore::Unsat(core.into_boxed_slice())
            },
            None => panic!("Resource limits are not supported yet by satcoder (use cadical directly)"),
        }
    }
}

struct CadicalModel<'a> {
    instance :&'a Cadical,
}

impl<'a> SatModel for CadicalModel<'a> {
    type L = CdcLit;

    fn lit_value(&self, l: &Self::L) -> bool {
        self.instance.cadical.value(l.0).unwrap()
    }
}
