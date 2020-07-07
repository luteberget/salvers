use crate::longestpaths::*;
pub use mysatsolver::Lit;
use mysatsolver::*;
use smallvec::SmallVec;
use std::collections::HashMap;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// Integer variable for use in scheduling constraints (see `SchedulingSolver`).
pub struct IntVar(Node);

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// Integer variable for use in scheduling constraints (see `SchedulingSolver`).
pub struct SumRef(usize);

impl SumRef {
  fn idx(&self) -> usize { self.0 }
}

struct NodeSumRef {
    sum :SumRef,
    coeff: i32,
}

struct Sum {
    lit :Lit,
    bound: u32,
    current_value :i32,
}

struct SchedulingTheory {
    condition_edge: HashMap<Lit, Edge>, // Map from bool variable to edge
    edge_condition: HashMap<Edge, Lit>, // Map from edge to bool variable
    graph: LongestPaths,

    #[cfg(debug_assertions)]
    requires_backtrack: bool,

    model: Option<Values>,
    invalidate_model: bool,

    sum_constraints: Vec<Sum>,
    node_constraints: Vec<SmallVec<[NodeSumRef; 4]>>,

    trail: Vec<Edge>,
    trail_lim: Vec<usize>,
}

impl SchedulingTheory {
    fn new() -> Self {
        SchedulingTheory {
            condition_edge: HashMap::new(),
            edge_condition: HashMap::new(),
            #[cfg(debug_assertions)]
            requires_backtrack: false,
            model: None,
            invalidate_model: false,

            sum_constraints: Vec::new(),
            node_constraints: Vec::new(),

            graph: LongestPaths::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
        }
    }


    fn new_int(&mut self) -> IntVar {
        assert!(self.trail_lim.len() == 0);
        let node = self.graph.new_node();
        while self.node_constraints.len() <= node.idx() {
          self.node_constraints.push(Default::default());
        }
        IntVar(node)
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
            let (node_constraints, sum_constraints) = (&mut self.node_constraints, &mut self.sum_constraints);
            let result = self.graph.enable_edge_cb(edge, |node,old,new| {
              for component in node_constraints[node.idx()].iter() {
                let sum = &mut sum_constraints[component.sum.idx()];
                let value_diff = component.coeff * (new - old);
                sum.current_value += value_diff;
              }
            }).is_ok();
            result
        }
    }
}

impl Theory for SchedulingTheory {
    fn check(&mut self, ch: Check, lits: &[Lit], buf: &mut Refinement) {
        #[cfg(debug_assertions)]
        assert!(!self.requires_backtrack);

        if self.invalidate_model {
            self.invalidate_model = false;
            self.model = None;
        }

        for lit in lits {
            if let Some(edge) = self.condition_edge.get(lit) {
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
        self.invalidate_model = true;
        if (level as usize) < self.trail_lim.len() {
            #[cfg(debug_assertions)]
            {
                self.requires_backtrack = false;

                let backtrack_size = ((self.trail.len() - self.trail_lim[level as usize]) as f32)
                    / (self.trail_lim.len() as f32);
                println!(
                    "Backtracking over {}% of the trail.",
                    (backtrack_size * 100.0) as usize
                );
            }

            self.graph
                .disable_edges(self.trail.drain(self.trail_lim[level as usize]..));
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
        if self.was_sat {
            return Some(Model { solver: self });
        }
        None
    }

    pub fn new_sum_constraint(&mut self, bound :u32) -> SumRef {
      assert!(self.prop.theory.trail_lim.len() == 0);
      let ref_ = SumRef(self.prop.theory.sum_constraints.len());
      let lit = self.new_bool();
      self.prop.theory.sum_constraints.push(Sum { lit, bound, current_value: 0 });
      ref_
    }

    pub fn add_constraint_coeff(&mut self, sum :SumRef, IntVar(node) :IntVar, coeff :i32) {
      assert!(self.prop.theory.trail_lim.len() == 0);
      let component = NodeSumRef { sum, coeff };
      let value = self.prop.theory.graph.value(node) * coeff;
      self.prop.theory.node_constraints[node.idx()].push(component);
      self.prop.theory.sum_constraints[sum.idx()].current_value += value;
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

impl<'a> sattrait::Model<Lit> for Model<'a> {
    fn value(&self, l: Lit) -> bool {
        self.get_bool_value(l)
    }
}

impl sattrait::SatInstance<Lit> for SchedulingSolver {
    fn new_var(&mut self) -> Lit {
        self.new_bool()
    }
    fn add_clause(&mut self, c: impl IntoIterator<Item = impl Into<Lit>>) {
        self.add_clause(&c.into_iter().map(|l| l.into()).collect::<Vec<_>>());
    }
}

impl sattrait::SatSolver<Lit> for SchedulingSolver {
    fn solve<'a>(
        &'a mut self,
        assumptions: impl IntoIterator<Item = impl Into<Lit>>,
    ) -> Result<Box<dyn sattrait::Model<Lit> + 'a>, Box<dyn Iterator<Item = Lit> + 'a>> {
        match self.solve_with_assumptions(
            &assumptions
                .into_iter()
                .map(|x| x.into())
                .collect::<Vec<_>>(),
        ) {
            Ok(m) => Ok(Box::new(m)),
            Err(c) => Err(c),
        }
    }

    fn result<'a>(
        &'a self,
    ) -> Result<Box<dyn sattrait::Model<Lit> + 'a>, Box<dyn Iterator<Item = Lit> + 'a>> {
        if self.was_sat {
            Ok(Box::new(Model { solver: self }))
        } else {
            Err(Box::new(self.prop.conflict.iter().map(|l| !*l)))
        }
    }
}
