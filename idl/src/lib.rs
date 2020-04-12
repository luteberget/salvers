use mysatsolver::*;
use smallvec::SmallVec;
use std::collections::HashMap;
use std::collections::VecDeque;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// Integer variable for use in difference constraints (see `IdlSolver`).
pub struct DVar(u32);

struct InnerIdl {
    next_dvar: u32,
    conditions: HashMap<Lit, u32>, // lit ->  edge idx
    requires_backtrack: bool,
    graph: IdlGraph,
    trail :Vec<u32>, // trail of activated edges
    trail_lim :Vec<usize>,
}

struct IdlGraph {
    conflict: Vec<Lit>,
    nodes: Vec<IdlNode>,
    edges: Vec<IdlEdge>,

    update_dists: Vec<(u32, i32)>,
    queue: VecDeque<i32>,
}

struct IdlNode {
    dist: i32,
    pred: i32,
    out_edges: SmallVec<[u32; 4]>,
}

struct IdlEdge {
    from: i32, // negative sign means not enabled
    to: u32,
    weight: i32,
    lit: Lit,
}

impl IdlGraph {
    fn disable_edge(&mut self, del_id :u32) -> bool {
      let edge = &mut self.edges[del_id as usize];
      if edge.from < 0 { return false; }
      edge.from *= -1;
      true
    }

    fn enable_edge(&mut self, add_id: u32) -> bool {
        let edge = &mut self.edges[add_id as usize];

        // was it already enabled?
        if edge.from > 0 {
            return true;
        }
        edge.from *= -1;

        // was it already feasible?
        if self.nodes[edge.from as usize].dist + edge.weight >= self.nodes[edge.to as usize].dist {
            return true;
        }

        // update dists
        self.update_dists.clear();
        self.queue.clear();
        self.queue.push_back(add_id as i32);

        let mut updated_root = false;
        while let Some(edge_idx) = self.queue.pop_front() {
            let edge = &mut self.edges[edge_idx as usize];
            if edge.from < 0 {
                // skip non-active constraints
                continue;
            }
            let x = &self.nodes[edge.from as usize];
            let y = &self.nodes[edge.to as usize];
            if x.dist + edge.weight < y.dist {
                if updated_root && edge_idx == add_id as i32 {
                    // prepare the conflict vec for the caller to read
                    self.analyze_conflict(add_id);

                    // backtrack on updated dists
                    for (node, dist) in self.update_dists.iter().rev() {
                        self.nodes[*node as usize].dist = *dist;
                    }

                    // backtrack on constraint-active-flag
                    self.edges[add_id as usize].from *= -1;

                    return false;
                }

                updated_root = true;
                self.update_dists.push((edge.to, y.dist));
                self.nodes[edge.to as usize].dist = x.dist + edge.weight;
                self.nodes[edge.to as usize].pred = edge_idx;
                for other in self.nodes[edge.to as usize].out_edges.iter() {
                    self.queue.push_back(*other as i32);
                }
            }
        }

        true
    }

    fn analyze_conflict(&mut self, add_id: u32) {
        self.conflict.clear();
        let mut edge_id = self.nodes[self.edges[add_id as usize].from as usize].pred;
        while edge_id != add_id as i32 {
            let lit = self.edges[edge_id as usize].lit;
            if lit != LIT_UNDEF {
                self.conflict.push(lit);
            }
            edge_id = self.nodes[self.edges[edge_id as usize].from as usize].pred;
        }
    }

}

const V0: DVar = DVar(1);

impl InnerIdl {
    fn new() -> Self {
        let mut idl = InnerIdl {
            next_dvar: 0,
            conditions: HashMap::new(),
            requires_backtrack: false,
            trail :Vec::new(),
            trail_lim :Vec::new(),
            graph: IdlGraph {
                conflict: Vec::new(),
                nodes: Vec::new(),
                edges: Vec::new(),
                queue: VecDeque::new(),
                update_dists: Vec::new(),
            },
        };
        let _undef = idl.new_int();
        let _x0 = idl.new_int();
        idl
    }

    fn new_int(&mut self) -> DVar {
        let v = DVar(self.next_dvar);
        self.next_dvar += 1;
        self.graph.nodes.push(IdlNode {
            dist: 0,
            pred: -1,
            out_edges: SmallVec::new(),
        });
        v
    }

    fn add_constraint(&mut self, lit: Option<Lit>, DVar(x): DVar, DVar(y): DVar, k: i32) {
        let edge_idx = self.graph.edges.len() as u32;
        self.graph.edges.push(IdlEdge {
            from: -(x as i32),
            to: y,
            weight: k,
            lit: lit.unwrap_or(LIT_UNDEF),
        });
        self.graph.nodes[x as usize].out_edges.push(edge_idx);
        if let Some(lit) = lit {
            self.conditions.insert(lit, edge_idx);
        } else {
            self.enable(edge_idx);
        }
    }

    fn enable(&mut self, e :u32) -> bool{
      let val = self.graph.enable_edge(e);
      if val { self.trail.push(e); }
      val
    }
}

impl Theory for InnerIdl {
    fn check(&mut self, _ch: Check, lits: &[Lit], buf: &mut Refinement) {
        assert!(!self.requires_backtrack);
        println!("check {:?} {:?}", _ch, lits);
        for lit in lits {
            for edge_idx in self.conditions.get(lit) {
                if !self.graph.enable_edge(*edge_idx) {
                    buf.add_clause(self.graph.conflict.iter().cloned());
                    self.requires_backtrack = true;
                    return;
                }
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
        self.requires_backtrack = false;
        if (level as usize) < self.trail_lim.len() {
          for edge in self.trail.drain(self.trail_lim[level as usize]..) {
            self.graph.disable_edge(edge);
          }
          self.trail_lim.truncate(level as usize);
        }
    }
}

/// DPLL(T) solver with integer difference logic theory.
pub struct IdlSolver {
    prop: DplltSolver<InnerIdl>,
}

impl IdlSolver {
    pub fn new() -> Self {
        Self {
            prop: DplltSolver::new(InnerIdl::new()),
        }
    }

    fn inner(&mut self) -> &mut InnerIdl {
        &mut self.prop.theory
    }

    /// Get a fresh Boolean variable.
    pub fn new_bool(&mut self) -> mysatsolver::Lit {
        self.prop.new_var_default()
    }

    /// Get a fresh integer variable.
    pub fn new_int(&mut self) -> DVar {
        self.inner().new_int()
    }

    /// Get a variable representing zero, for use in constraints
    /// involving only one variable.
    ///
    /// Example:
    /// ```
    /// let mut s = idl::IdlSolver::new();
    /// let x = s.new_int();
    /// s.add_diff(None, s.zero(), x, -2); // 0 - x <= -2   (i.e. x >= 2)
    /// assert!(s.solve());
    /// assert!(s.get_value(x) >= 2);
    /// ```
    pub fn zero(&self) -> DVar {
        V0
    }

    /// Add a Boolean clause.
    pub fn add_clause(&mut self, v: &[Lit]) {
        self.prop.add_clause(v.iter().cloned());
    }

    /// Assert that x - y <= k, where x and y are integer variables.
    /// If the Boolean `lit` is set, the constraint applies only when `lit` is true.
    ///
    /// Example:
    /// ```
    /// let mut s = idl::IdlSolver::new();
    /// let x = s.new_int();
    /// let y = s.new_int();
    /// let z = s.new_int();
    /// s.add_diff(None, y, z, -5);
    /// s.add_diff(None, x, y, -5);
    /// assert!(s.solve());
    /// assert!(s.get_value(x) + 5 <= s.get_value(y));
    /// assert!(s.get_value(y) + 5 <= s.get_value(z));
    /// ```
    pub fn add_diff(&mut self, lit: Option<Lit>, x: DVar, y: DVar, k: i32) {
        self.inner().add_constraint(lit, x, y, k);
    }

    pub fn solve(&mut self) -> bool {
        self.prop.solve() == LBOOL_TRUE
    }

    pub fn get_value(&mut self, DVar(x): DVar) -> i32 {
        let idl = &self.prop.theory;
        idl.graph.nodes[1].dist - idl.graph.nodes[x as usize].dist
    }
}
