use crate::longestpaths::*;
use log::*;
pub use dpllt::Lit;
use dpllt::*;
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

#[derive(Debug)]
struct NodeSumRef {
    sumref: SumRef,
    coeff: i32,
}

#[derive(Debug)]
struct Sum {
    lit: Lit,
    bound: u32,
    current_value: i32,
    min_violation: u32,
    nodes: SmallVec<[(Node, i32); 4]>,
    optimize: bool,
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

    fn set_sum_value(
        sums: &mut Vec<Sum>,
        violations: &mut Vec<SumRef>,
        sumref: SumRef,
        new_value: i32,
    ) {
        let sum = &mut sums[sumref.idx()];

        // remove previous violation
        if !(new_value > sum.bound as i32) {
            //println!("removing violation");
            violations.retain(|x| *x != sumref);
        }

        sum.current_value = new_value;

        if new_value > sum.bound as i32 {
            //println!("Adding violation {:?}", sumref);
            violations.push(sumref);
            sum.min_violation = sum.min_violation.min(sum.current_value as u32 - sum.bound);
        }
    }

    fn evaluate(&mut self, sumref: SumRef, nodes: impl Fn(&Node) -> i32) {
        let sum = &self.sum_constraints[sumref.idx()];
        let new_value = sum
            .nodes
            .iter()
            .map(|(n, coeff)| nodes(n) * coeff)
            .sum::<i32>();
        //println!("evaluating {} @ {:?}", new_value, sum);
        Self::set_sum_value(
            &mut self.sum_constraints,
            &mut self.violations,
            sumref,
            new_value,
        );
        //println!("after evaluating, violations: {:?}", self.violations);
    }

    fn notify(&mut self, node: Node, old: i32, new: i32) {
        //println!("notify {:?} {} {}", node, old, new);
        //println!("  - constraints {:?}", self.node_constraints[node.idx()]);
        for NodeSumRef { sumref, coeff } in self.node_constraints[node.idx()].iter() {
            let sum = &mut self.sum_constraints[sumref.idx()];
            let new_value = sum.current_value + coeff * (new - old);
            Self::set_sum_value(
                &mut self.sum_constraints,
                &mut self.violations,
                *sumref,
                new_value,
            );
        }
    }

    //    fn get_violations(&self) -> &[SumRef] {
    //        &self.violations
    //    }
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
    sum_by_lit: HashMap<Lit, SumRef>,

    trail: Vec<Edge>,
    trail_lim: Vec<usize>,

    // perf counters
    num_sumwatcher_clauses: usize,
    num_cycle_clauses: usize,
}

impl SchedulingTheory {
    fn new() -> Self {
        SchedulingTheory {
            condition_edge: HashMap::new(),
            edge_condition: HashMap::new(),
            sum_by_lit: HashMap::new(),
            #[cfg(debug_assertions)]
            requires_backtrack: false,
            model: None,
            invalidate_model: false,
            sum_watcher: SumWatcher::new(),
            graph: LongestPaths::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            num_sumwatcher_clauses: 0,
            num_cycle_clauses: 0,
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
        let _p = hprof::enter("theory check");
        //println!("Check {:?} {:?}", ch, lits);
        #[cfg(debug_assertions)]
        assert!(!self.requires_backtrack);

        if self.invalidate_model {
            self.invalidate_model = false;
            self.model = None;
        }

        {
            let _p = hprof::enter("theory sumrefcheck1");
            for sumref in self.sum_watcher.violations.drain(..) {
                //println!("sumref {:?}", sumref);
                let sum = &self.sum_watcher.sum_constraints[sumref.idx()];
                let critical_set = self.graph.critical_set(sum.nodes.iter().map(|(n, _)| *n));
                let map = &self.edge_condition;
                let reason = critical_set
                    .filter_map(|edge| map.get(&edge))
                    .map(|lit| !*lit);
                let clause = std::iter::once(!sum.lit).chain(reason);

                //println!("iter critical set...");
                let clause = clause.collect::<Vec<_>>();
                self.num_sumwatcher_clauses += 1;
                //debug!("SUMWATCHER (1) Adding clause {:?}", clause);
                //println!("iter critical set done");

                buf.add_clause(clause);

                //// Doesn't necessarily require backtrack... (?)
                //#[cfg(debug_assertions)]
                //{
                //    self.requires_backtrack = true;
                //}

                //return;
            }
            //println!("sumref done.");
        }

        for lit in lits {
            if let Some(edge) = {
                let _p = hprof::enter("theory condition_edge.get(lit)");
                self.condition_edge.get(lit)
            } {
                let sums = &mut self.sum_watcher;

                if let Err(cycle) = {
                    let _p = hprof::enter("theory enable_edge");

                    self.graph
                        .enable_edge_cb(*edge, |nd, a, b| sums.notify(nd, a, b))
                } {
                    let _p = hprof::enter("theory cycle");
                    let map = &self.edge_condition;
                    let cycle = cycle
                        .filter_map(|edge| map.get(&edge))
                        .map(|lit| !*lit)
                        .collect::<Vec<_>>();
                    //debug!("SCHEDULING cycle constraint {:?}", cycle);
                    self.num_cycle_clauses += 1;

                    buf.add_clause(cycle);

                    #[cfg(debug_assertions)]
                    {
                        self.requires_backtrack = true;
                    }

                    return;
                } else {
                    self.trail.push(*edge);
                }

                {
                    let _p = hprof::enter("theory sumcheck2");
                    for sumref in self.sum_watcher.violations.drain(..) {
                        let sum = &self.sum_watcher.sum_constraints[sumref.idx()];
                        let critical_set =
                            self.graph.critical_set(sum.nodes.iter().map(|(n, _)| *n));
                        let map = &self.edge_condition;
                        let reason = critical_set
                            .filter_map(|edge| map.get(&edge))
                            .map(|lit| !*lit);
                        let clause = std::iter::once(!sum.lit).chain(reason);

                        let clause = clause.collect::<Vec<_>>();
                        //debug!("SUMWATCHER (2) Adding clause {:?}", clause);
                        self.num_sumwatcher_clauses += 1;

                        buf.add_clause(clause);

                        //// Doesn't necessarily require backtrack... (?)
                        //#[cfg(debug_assertions)]
                        //{
                        //    self.requires_backtrack = true;
                        //}

                        //return;
                    }
                }
            } else {
                //println!("irrelevant lit {:?}", lit);
            }
        }

        if let Check::Final = ch {
            // If we get here, the problem is SAT, so we preserve the model before backtracking.
            //println!("Theory: FINAL SAT");
            if !self.model.is_some() {
                let _p = hprof::enter("theory extractmodel");
                //println!("extracting values");
                self.model = Some(self.graph.all_values());
            }
        }

        //println!("check done.");
    }

    fn explain(&mut self, _l: Lit, _x: u32, _buf: &mut Refinement) {
        unreachable!()
    }

    fn new_decision_level(&mut self) {
        let _p = hprof::enter("theory trail_lim");
        self.trail_lim.push(self.trail.len());
    }

    fn backtrack(&mut self, level: i32) {
        let _p = hprof::enter("theory backtrack");
        self.invalidate_model = true;
        if (level as usize) < self.trail_lim.len() {
            #[cfg(debug_assertions)]
            {
                self.requires_backtrack = false;

                let backtrack_size = ((self.trail.len() - self.trail_lim[level as usize]) as f32)
                    / (self.trail_lim.len() as f32);
                //println!(
                //    "Backtracking over {}% of the trail.",
                //    (backtrack_size * 100.0) as usize
                //);
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
    num_cores: usize,
    num_sum_constraints: usize,
}

impl SchedulingSolver {
    /// New, empty solver.
    pub fn new() -> Self {
        SchedulingSolver {
            prop: DplltSolver::new(SchedulingTheory::new()),
            was_sat: false,
            num_cores: 0,
            num_sum_constraints: 0,
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
        //println!("start sat...");
        self.was_sat = self.prop.solve() == LBOOL_TRUE;
        //println!("sat done");
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

    pub fn delete_sum_constraint(&mut self, sumref: SumRef) {
        assert!(self.prop.theory.trail_lim.len() == 0);
        for (node, _) in self.prop.theory.sum_watcher.sum_constraints[sumref.idx()]
            .nodes
            .iter()
        {
            self.prop.theory.sum_watcher.node_constraints[node.idx()]
                .retain(|n| n.sumref != sumref);
        }
        let lit = self.prop.theory.sum_watcher.sum_constraints[sumref.idx()].lit;
        self.add_clause(&vec![!lit]);
        let remove = self.prop.theory.sum_by_lit.remove(&lit);
        debug_assert!(remove.is_some());
    }

    pub fn new_sum_constraint(&mut self, lit: Lit, bound: u32) -> SumRef {
        debug!("new sum constraint {:?} < {}", lit, bound);
        self.num_sum_constraints += 1;
        assert!(self.prop.theory.trail_lim.len() == 0);
        let sumref = SumRef(self.prop.theory.sum_watcher.sum_constraints.len() as u32);
        self.prop.theory.sum_watcher.sum_constraints.push(Sum {
            nodes: SmallVec::new(),
            lit,
            bound,
            current_value: 0,
            min_violation: u32::MAX,
            optimize: true,
        });
        self.prop.theory.sum_by_lit.insert(lit, sumref);
        sumref
    }

    pub fn set_conditional_upper_bound(&mut self, lit: Lit, var: IntVar, value: u32) {
        let sumref = self.new_sum_constraint(lit, value);
        self.prop.theory.sum_watcher.sum_constraints[sumref.0 as usize].optimize = false;
        self.add_constraint_coeff(sumref, var, 1);
    }

    pub fn add_constraint_coeff(&mut self, sumref: SumRef, IntVar(node): IntVar, coeff: i32) {
        assert!(self.prop.theory.trail_lim.len() == 0);
        let component = NodeSumRef { sumref, coeff };
        let value = self.prop.theory.graph.value(node) * coeff;
        self.prop.theory.sum_watcher.node_constraints[node.idx()].push(component);
        let sum = &mut self.prop.theory.sum_watcher.sum_constraints[sumref.idx()];
        if let Some((_n, c)) = sum.nodes.iter_mut().find(|(n, _)| *n == node) {
            *c += coeff;
        } else {
            sum.nodes.push((node, coeff));
        }
        let graph = &self.prop.theory.graph;
        self.prop
            .theory
            .sum_watcher
            .evaluate(sumref, |n| graph.value(*n));
    }

    pub fn optimize<'a>(&'a mut self) -> Result<(i32, Model<'a>), ()> {
        // RC2-like algorithm, except that the constraints are not relaxable,
        // and they are implemented as a theory using diff constraints scheduling/longest paths.

        debug!("start optimize.");
        let mut cost: i32 = 0;

        //println!(" before optimization, sum constraints are:");
        //println!(" {:?}", self.prop.theory.sum_watcher.sum_constraints);

        loop {
            let mut result = {
                let _p = hprof::enter("optimize solve");
                // Assume all the sum constraints.
                // TODO don't copy the assumption lits, somehow.
                let assumptions = self
                    .prop
                    .theory
                    .sum_watcher
                    .sum_constraints
                    .iter()
                    .filter(|s| s.optimize)
                    .map(|s| s.lit)
                    .collect::<Vec<Lit>>();
                //println!("solving with assumptions {:?}", assumptions);
                //println!("solving with assumptions...");
                let mut result = self.solve_with_assumptions(&assumptions);
                result
            };
            //println!("solver finished");
            match result {
                Ok(_) => {
                    drop(result);
                    let model = self.get_model().unwrap();
                    return Ok((cost, model));
                }
                Err(ref mut core) => {
                    let _p = hprof::enter("optimize treat core");
                    // Some of them are not satisifable
                    let core = core.collect::<Vec<_>>();
                    drop(result);

                    self.num_cores += 1;
                    debug!("got core {} {:?}", core.len(), core);
                    if core.len() == 0 {
                        return Err(());
                    }

                    let mut min_weight = u32::MAX;
                    let mut sum_bound = 0;
                    let mut components = Vec::new();
                    for lit in core.iter() {
                        let sumref = self.prop.theory.sum_by_lit[lit];
                        let sum = &mut self.prop.theory.sum_watcher.sum_constraints[sumref.idx()];
                        min_weight = min_weight.min(sum.min_violation);
                    }

                    for lit in core.iter() {
                        let new_lit = self.new_bool();
                        let sumref = self.prop.theory.sum_by_lit[lit];
                        let sum = &mut self.prop.theory.sum_watcher.sum_constraints[sumref.idx()];
                        sum.bound += min_weight;

                        for (nd, c) in sum.nodes.iter() {
                            components.push((*nd, *c));
                        }

                        // Instead of deleting this constraint and adding a new one, let's just
                        // increase the bound and find a new lit.
                        //self.delete_sum_constraint(sumref);
                        sum.lit = new_lit;
                        sum.min_violation = u32::MAX;
                        sum_bound += sum.bound;
                        self.prop.theory.sum_by_lit.remove(lit);
                        self.prop.theory.sum_by_lit.insert(new_lit, sumref);

                        let graph = &self.prop.theory.graph;
                        self.prop
                            .theory
                            .sum_watcher
                            .evaluate(sumref, |v| graph.value(*v));

                        // The main weakness I see here is that we forget about the `lit` which we
                        // have already learnt a lot about from conflicts. Those clauses become wasted.
                    }

                    cost += min_weight as i32;
                    debug!("increased cost by {} to {}", min_weight, cost);
                    debug!(
                        "#cores={}, #sums={}, #sumlearn={}, #cyclelearn={}",
                        self.num_cores,
                        self.num_sum_constraints,
                        self.prop.theory.num_sumwatcher_clauses,
                        self.prop.theory.num_cycle_clauses
                    );
                    debug_assert!(min_weight < u32::MAX);

                    if core.len() > 1 {
                        let sum_bool = self.new_bool();
                        let new_sum = self.new_sum_constraint(sum_bool, sum_bound + min_weight);
                        for (nd, c) in components {
                            self.add_constraint_coeff(new_sum, IntVar(nd), c);
                        }
                    }

                    //println!(" after treating the core, sum constraints are:");
                    //println!(" {:?}", self.prop.theory.sum_watcher.sum_constraints);
                }
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
