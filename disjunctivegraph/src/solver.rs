use crate::longestpaths::*;

pub use mysatsolver::Lit;
use mysatsolver::*;
//use sattrait;
//use smallvec::SmallVec;
use std::collections::HashMap;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// Integer variable for use in scheduling constraints (see `SchedulingSolver`).
pub struct IntVar(Node);

struct SchedulingTheory {
    condition_edge: HashMap<Lit, Edge>, // Map from bool variable to edge
    edge_condition: HashMap<Edge, Lit>, // Map from edge to bool variable
    graph: LongestPaths,

    #[cfg(debug_assertions)]
    requires_backtrack: bool,

    model: Option<Values>,

    trail: Vec<Edge>,
    trail_lim: Vec<usize>,
}

impl SchedulingTheory {
    fn new() -> Self {
        SchedulingTheory {
            condition_edge: HashMap::new(),
            edge_condition :HashMap::new(),
            #[cfg(debug_assertions)]
            requires_backtrack: false,
	    model: None,
            graph: LongestPaths::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
        }
    }

    fn new_int(&mut self) -> IntVar {
	assert!(self.trail_lim.len() == 0);
        IntVar(self.graph.new_node())
    }

    fn add_diff(
        &mut self,
        lit: Option<Lit>,
        IntVar(x): IntVar,
        IntVar(y): IntVar,
        length: i32,
    ) -> bool {
        let _p = hprof::enter("add scheduling constraint");
	assert!(self.trail_lim.len() == 0);
        let edge = self.graph.new_edge(x, y, length);
        if let Some(lit) = lit {
            self.condition_edge.insert(lit, edge);
            self.edge_condition.insert(edge, lit);
            true
        } else {
            let result = self.graph.enable_edge(edge).is_ok();
            result
        }
    }
}

impl Theory for SchedulingTheory {
    fn check(&mut self, ch: Check, lits: &[Lit], buf: &mut Refinement) {
        #[cfg(debug_assertions)]
        assert!(!self.requires_backtrack);

        for lit in lits {
            if let Some(edge) = self.condition_edge.get(lit) {
	      self.model = None;
              if let Err(cycle) = self.graph.enable_edge(*edge) {

                let map = &self.edge_condition;
                let cycle = cycle.filter_map(|edge| map.get(&edge)).map(|lit| !*lit);

                buf.add_clause(cycle);

                #[cfg(debug_assertions)]
                {
                    self.requires_backtrack = true;
                }

                return;

              } else {
                self.trail.push(*edge);
              }
            } else {
                println!("irrelevant lit {:?}", lit);
            }
        }

        if let Check::Final = ch {
          // If we get here, the problem is SAT, so we preserve the model before backtracking.
          println!("Theory: FINAL SAT");
	  if !self.model.is_some() {
            println!("extracting values");
            self.model = Some(self.graph.all_values());
	  }
	}
    }

    fn explain(&mut self, _l: Lit, _x: u32, _buf: &mut Refinement) {
        unreachable!()
    }

    fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    fn backtrack(&mut self, level: i32) {
        if (level as usize) < self.trail_lim.len() {
            #[cfg(debug_assertions)]
            {
                self.requires_backtrack = false;

                let backtrack_size = ((self.trail.len() - self.trail_lim[level as usize] ) as f32) /(self.trail_lim.len() as f32);
                println!("Backtracking over {}% of the trail.", (backtrack_size * 100.0) as usize);
            }

            self.graph.disable_edges(self.trail.drain(self.trail_lim[level as usize]..));
            self.trail_lim.truncate(level as usize);
        }
    }
}

/// Incremental solver for difference constraints.
///
/// TODO includes optimization criteria as monotone functions on the scheduling variables.
pub struct SchedulingSolver {
    prop: DplltSolver<SchedulingTheory>,
    was_sat: bool,
}

impl SchedulingSolver {
    /// New, empty solver.
    pub fn new() -> Self {
        SchedulingSolver {
            prop: DplltSolver::new(SchedulingTheory::new()),
            was_sat: false,
        }
    }

    fn theory(&mut self) -> &mut SchedulingTheory {
        &mut self.prop.theory
    }

    /// Get a fresh boolean variable.
    pub fn new_bool(&mut self) -> Lit {
        self.was_sat = false;
        self.prop.new_var_default()
    }

    /// Get a fresh integer scheduling variable.
    pub fn new_int(&mut self) -> IntVar {
        self.was_sat = false;
        self.theory().new_int()
    }

    /// Add a clause over boolean variables.
    pub fn add_clause(&mut self, v: &[Lit]) {
        self.was_sat = false;
        self.prop.add_clause(v.iter().cloned());
    }

    /// Add a difference constraint over integer scheduling variables.
    /// If the `lit` argument is given, the constraint is implied by the given boolean literal.
    /// If `lit` is `None`, the constraint is always implied.
    pub fn add_diff(&mut self, lit: Option<Lit>, x: IntVar, y: IntVar, l: i32) {
        self.was_sat = false;
        if !self.theory().add_diff(lit, x, y, l) {
           self.add_clause(&vec![]); // UNSAT
        }
    }

    /// Solve the problem.
    /// Returns either a model, or an `Err` result if the problem is unsatisfiable.
    pub fn solve<'a>(&'a mut self) -> Result<Model<'a>, ()> {
        self.prop.set_assumptions(std::iter::empty());
        self.was_sat = self.prop.solve() == LBOOL_TRUE;
        if self.was_sat {
            Ok(Model { solver: self })
        } else {
            Err(())
        }
    }

    /// Solve the probem under assumptions given as an iterator over boolean literals.
    /// Returns either a model, or an `Err` result if the problem is unsatisfiable.
    pub fn solve_with_assumptions<'a>(
        &'a mut self,
        a: &[Lit],
    ) -> Result<Model<'a>, Box<dyn Iterator<Item = Lit> + 'a>> {
        self.prop.set_assumptions(a.iter().cloned());
        self.was_sat = self.prop.solve() == LBOOL_TRUE;
        if self.was_sat {
            Ok(Model { solver: self })
        } else {
            Err(Box::new(self.prop.conflict.iter().map(|l| !*l)))
        }
    }

    pub fn get_model<'a>(&'a self) -> Option<Model<'a>> {
      if self.was_sat { return Some(Model { solver: self }); }
      None
    }

}

pub struct Model<'a> {
    solver: &'a SchedulingSolver,
}

impl<'a> Model<'a> {
    /// If the previous call to `solve` was successful, and no variables or constraints have been
    /// added, this returns the value of an integer scheduling variable.
    pub fn get_int_value(&self, IntVar(x): IntVar) -> i32 {
	debug_assert!(self.solver.prop.theory.model.is_some());
        self.solver.prop.theory.model.as_ref().unwrap().get(x)
    }

    /// If the previous call to `solve` was successful, and no variables or constraints have been
    /// added, this returns the value of a boolean literal.
    pub fn get_bool_value(&self, lit: Lit) -> bool {
        self.solver.prop.value(lit)
    }
}
