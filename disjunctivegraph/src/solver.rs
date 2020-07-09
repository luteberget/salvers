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
pub struct SumRef(u32);

impl SumRef {
    fn idx(&self) -> usize {
        self.0 as usize
    }
}

struct NodeSumRef {
    sumref: SumRef,
    coeff: i32,
}

struct Sum {
    lit: Lit,
    bound: u32,
    current_value: i32,
    min_violation :u32,
    nodes :SmallVec<[Node;4]>,
}

struct SumWatcher {
    sum_constraints: Vec<Sum>,
    node_constraints: Vec<SmallVec<[NodeSumRef; 4]>>,
    violations: Vec<SumRef>,
}

impl SumWatcher {
    fn new() -> Self {
        SumWatcher {
            sum_constraints: Vec::new(),
            node_constraints: Vec::new(),
            violations: Vec::new(),
        }
    }

    fn notify(&mut self, node: Node, old: i32, new :i32) {
        println!("notify {:?} {} {}", node, old, new);
        for NodeSumRef { sumref, coeff } in self.node_constraints[node.idx()].iter() {

            let sum = &mut self.sum_constraints[sumref.idx()];
            let new_value = sum.current_value + coeff * (new - old);

            // remove previous violation
            if sum.current_value > sum.bound as i32 && !(new_value > sum.bound as i32) {
                self.violations.retain(|x| x != sumref);
            }

            sum.current_value = new_value;

            if new_value > sum.bound as i32 {
                println!("Adding violation {:?}", sumref);
                self.violations.push(*sumref);
                sum.min_violation = sum.min_violation.min(sum.current_value as u32 - sum.bound);
            }
        }
    }

    fn get_violations(&self) -> &[SumRef] {
        &self.violations
    }
}

struct SchedulingTheory {
    condition_edge: HashMap<Lit, Edge>, // Map from bool variable to edge
    edge_condition: HashMap<Edge, Lit>, // Map from edge to bool variable
    graph: LongestPaths,

    #[cfg(debug_assertions)]
    requires_backtrack: bool,

    model: Option<Values>,
    invalidate_model: bool,

    sum_watcher: SumWatcher,
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
            sum_watcher: SumWatcher::new(),
            graph: LongestPaths::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
        }
    }

    fn new_int(&mut self) -> IntVar {
        assert!(self.trail_lim.len() == 0);
        let node = self.graph.new_node();
        while self.sum_watcher.node_constraints.len() <= node.idx() {
            self.sum_watcher.node_constraints.push(Default::default());
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
            let sums = &mut self.sum_watcher;
            let result = self
                .graph
                .enable_edge_cb(edge, |nd, a, b| sums.notify(nd, a, b))
                .is_ok();
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
                let sums = &mut self.sum_watcher;
                if let Err(cycle) = self
                    .graph
                    .enable_edge_cb(*edge, |nd, a, b| sums.notify(nd, a, b))
                {
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

                // Check sum constraints

                for sumref in self.sum_watcher.get_violations() {
                    let sum = &self.sum_watcher.sum_constraints[sumref.idx()];
                    let critical_set = self.graph.critical_set(sum.nodes.iter().cloned());
                    let map = &self.edge_condition;
                    let reason = critical_set.filter_map(|edge| map.get(&edge)).map(|lit| !*lit);
                    let clause = std::iter::once(!sum.lit).chain(reason);
                    buf.add_clause(clause);

                    #[cfg(debug_assertions)]
                    {
                        self.requires_backtrack = true;
                    }

                    return;
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

            let sums = &mut self.sum_watcher;
            self.graph.disable_edges_cb(
                self.trail.drain(self.trail_lim[level as usize]..),
                |nd, a, b| sums.notify(nd, a, b),
            );
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

    pub fn delete_sum_constraint(&mut self, sumref :SumRef) {
        assert!(self.prop.theory.trail_lim.len() == 0);
        for node in self.prop.theory.sum_watcher.sum_constraints[sumref.idx()].nodes.iter() {
            self.prop.theory.sum_watcher.node_constraints[node.idx()].retain(|n| n.sumref != sumref);
        }
        let lit = self.prop.theory.sum_watcher.sum_constraints[sumref.idx()].lit;
        self.add_clause(&vec![!lit]);
    }

    pub fn new_sum_constraint(&mut self, lit :Lit, bound: u32) -> SumRef {
        assert!(self.prop.theory.trail_lim.len() == 0);
        let ref_ = SumRef(self.prop.theory.sum_watcher.sum_constraints.len() as u32);
        self.prop.theory.sum_watcher.sum_constraints.push(Sum {
            nodes : SmallVec::new(),
            lit,
            bound,
            current_value: 0, min_violation: u32::MAX,
        });
        ref_
    }

    pub fn add_constraint_coeff(&mut self, sumref: SumRef, IntVar(node): IntVar, coeff: i32) {
        assert!(self.prop.theory.trail_lim.len() == 0);
        let component = NodeSumRef { sumref, coeff };
        let value = self.prop.theory.graph.value(node) * coeff;
        self.prop.theory.sum_watcher.node_constraints[node.idx()].push(component);
        let sum = &mut self.prop.theory.sum_watcher.sum_constraints[sumref.idx()];
        sum.current_value += value;
        sum.nodes.push(node);
    }

    pub fn optimize<'a>(&'a mut self) -> Result<(i32,Model<'a>), ()>{
        // RC2-like algorithm, except that the constraints are not relaxable, 
        // and they are implemented as a theory using diff constraints scheduling/longest paths.

        let mut cost : i32 = 0;

        loop {

            let mut assumptions = vec![];
            let mut result = self.solve_with_assumptions(&assumptions);
            match result {
                Ok(model) => {
                    return Ok((cost, model));
                },
                Err(ref mut core) => {

                    let core = core.collect::<Vec<_>>();

                    todo!();

                    //for sumref in core.iter().map(|x| 


                },
            }

        }

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
