use dpllt::*;
use sattrait;
pub use dpllt::Lit;
use smallvec::SmallVec;
use std::collections::HashMap;
use std::collections::VecDeque;

type Domain = i64;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// Integer variable for use in difference constraints (see `IdlSolver`).
pub struct DVar(u32);

#[derive(Debug)]
struct InnerIdl {
    next_dvar: u32,
    conditions: HashMap<Lit, u32>, // lit ->  edge idx

    #[cfg(debug_assertions)]
    requires_backtrack: bool,

    graph: IdlGraph,
    trail: Vec<u32>, // trail of activated edges
    trail_lim: Vec<usize>,
}

#[derive(Debug)]
pub struct IdlGraph {
    pub conflict: Vec<Lit>,
    pub nodes: Vec<IdlNode>,
    pub edges: Vec<IdlEdge>,

    pub update_dists: Vec<(u32, Domain)>,
    pub queue: VecDeque<i32>,
}

#[derive(Debug)]
pub struct IdlNode {
    pub dist: Domain,
    pub pred: i32,
    pub out_edges: SmallVec<[u32; 4]>,
}

#[derive(Debug)]
pub struct IdlEdge {
    pub from: i32, // negative sign means not enabled
    pub to: u32,
    pub weight: Domain,
    pub lit: Lit,
}

impl IdlGraph {
    pub fn new() -> Self { IdlGraph 
            {
                conflict: Vec::new(),
                nodes: Vec::new(),
                edges: Vec::new(),
                queue: VecDeque::new(),
                update_dists: Vec::new(),
            }
    }

    pub fn disable_edge(&mut self, del_id: u32) -> bool {
        //println!("disable {}", del_id);
        let edge = &mut self.edges[del_id as usize];
        if edge.from < 0 {
            return false;
        }
        edge.from *= -1;
        true
    }

    pub fn enable_edge(&mut self, add_id: u32) -> bool {
        let edge = &mut self.edges[add_id as usize];

        // was it already enabled?
        if edge.from > 0 {
            return true;
        }
        edge.from *= -1;

	if self.nodes[edge.from as usize].dist + edge.weight <= self.nodes[edge.to as usize].dist {
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
            if x.dist + edge.weight > y.dist {
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
                //println!("new {:?}", self.nodes.iter().map(|n| n.dist));
                for other in self.nodes[edge.to as usize].out_edges.iter() {
                    self.queue.push_back(*other as i32);
                }
            }
        }

        true
    }

    pub fn analyze_conflict(&mut self, add_id: u32) {
        //println!("analyze {}: {:#?}", add_id, self);
        self.conflict.clear();
        let add_lit = self.edges[add_id as usize].lit;
        if add_lit != LIT_UNDEF {
            self.conflict.push(add_lit);
        }

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
            #[cfg(debug_assertions)]
            requires_backtrack: false,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            graph: IdlGraph::new(),
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

    fn add_constraint(&mut self, lit: Option<Lit>, DVar(x): DVar, DVar(y): DVar, k: Domain) -> bool {
        let _g = hprof::enter("idl add constraint");
        let edge_idx = self.graph.edges.len() as u32;
        self.graph.edges.push(IdlEdge {
            from: -(x as i32),
            to: y,
            weight: -k,
            lit: lit.unwrap_or(LIT_UNDEF),
        });
        self.graph.nodes[x as usize].out_edges.push(edge_idx);
        if let Some(lit) = lit {
            self.conditions.insert(lit, edge_idx);
            true
        } else {
            self.enable(edge_idx)
        }
    }

    fn enable(&mut self, e: u32) -> bool {
        let _p = hprof::enter("idl enable");
        let val = self.graph.enable_edge(e);
        if val {
            self.trail.push(e);
        }
        val
    }
}

impl Theory for InnerIdl {
    fn check(&mut self, _ch: Check, lits: &[Lit], buf: &mut Refinement) {
        #[cfg(debug_assertions)]
        assert!(!self.requires_backtrack);
        //println!("check {:?} {:?}", _ch, lits);
        //if let Check::Final = _ch { println!("final trail {:?}\nndoes: {:#?}", self.trail,self.graph.nodes); }
        //println!("before: {:#?}", self);
        for lit in lits {
            if let Some(edge_idx) = self.conditions.get(lit) {
                //println!("enabling conditional {:?}->{}", lit, edge_idx);
                if !self.graph.enable_edge(*edge_idx) {
                    //println!("Adding  {:?}", self.graph.conflict);
                    buf.add_clause(self.graph.conflict.iter().map(|l| l.inverse()));
                    #[cfg(debug_assertions)]
                    {
                        self.requires_backtrack = true;
                    }
                    return;
                }
                self.trail.push(*edge_idx);
            } else {
                //println!("irrelevant lit {:?}", lit);
            }
        }
    }

    fn explain(&mut self, _l: Lit, _x: u32, _buf: &mut Refinement) {
        unreachable!()
    }

    fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
        //println!("new theory decision level {}", self.trail_lim.len());
        //println!("trail: {:?}", self.trail);
        //println!("trail_lim: {:?}", self.trail_lim);
    }

    fn backtrack(&mut self, level: i32) {
        if (level as usize) < self.trail_lim.len() {
            #[cfg(debug_assertions)]
            {
                self.requires_backtrack = false;
            }
            //println!("backtracking to i={}",self.trail_lim[level as usize]);
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
    was_sat :bool,
}

impl IdlSolver {
    pub fn new() -> Self {
        Self {
            prop: DplltSolver::new(InnerIdl::new()),
            was_sat: false,
        }
    }

    fn inner(&mut self) -> &mut InnerIdl {
        &mut self.prop.theory
    }

    /// Get a fresh Boolean variable.
    pub fn new_bool(&mut self) -> dpllt::Lit {
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
    /// assert!(s.solve().is_ok());
    /// assert!(s.get_int_value(x) >= 2);
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
    /// assert!(s.solve().is_ok());
    /// assert!(s.get_int_value(x) + 5 <= s.get_int_value(y));
    /// assert!(s.get_int_value(y) + 5 <= s.get_int_value(z));
    /// ```
    pub fn add_diff(&mut self, lit: Option<Lit>, x: DVar, y: DVar, k: Domain) {
        let ok = self.inner().add_constraint(lit, x, y, k);
        if !ok { self.prop.add_clause(std::iter::empty()); }
    }

    pub fn solve<'a>(&'a mut self) -> Result<Model<'a>, ()> {
        self.prop.set_assumptions(std::iter::empty());
        self.was_sat = self.prop.solve() == LBOOL_TRUE;
        if self.was_sat {
           Ok(Model { solver: self })
        } else {
           Err(())
        }
    }

    pub fn solve_with_assumptions<'a>(&'a mut self, a: &[Lit]) -> Result<Model<'a>, Box<dyn Iterator<Item = Lit> + 'a>> {
        self.prop.set_assumptions(a.iter().cloned());
        self.was_sat = self.prop.solve() == LBOOL_TRUE;
        if self.was_sat {
          Ok(Model { solver: self })
	} else { 
          Err(Box::new(self.prop.conflict.iter().map(|l| !*l)))
        }
    }

    pub fn get_int_value(&mut self, DVar(x): DVar) -> Domain {
        let idl = &self.prop.theory;
	idl.graph.nodes[x as usize].dist -  idl.graph.nodes[1].dist
    }

    pub fn get_bool_value(&self, lit :Lit) -> bool {
        self.prop.value(lit)
    }
}

impl sattrait::SatSolver<Lit> for IdlSolver {
  fn solve<'a>(&'a mut self, assumptions :impl IntoIterator<Item = impl Into<Lit>>) -> Result<Box<dyn sattrait::Model<Lit> + 'a>, Box<dyn Iterator<Item = Lit> + 'a>> {
    match self.solve_with_assumptions(&assumptions.into_iter().map(|x| x.into()).collect::<Vec<_>>()) {
      Ok(m) => Ok(Box::new(m)),
      Err(c) => Err(c),
    }
  }

  fn result<'a>(&'a self) -> Result<Box<dyn sattrait::Model<Lit> + 'a>, Box<dyn Iterator<Item = Lit> + 'a>> {
    if self.was_sat {
      Ok(Box::new(Model{ solver: self}))
    } else {
      Err(Box::new(self.prop.conflict.iter().map(|l| !*l)))
    }
  }
}


pub struct Model<'a> {
  solver :&'a IdlSolver,
}

impl<'a> sattrait::Model<Lit> for Model<'a> {
  fn value(&self, l :Lit) -> bool { self.solver.get_bool_value(l) }
}

impl sattrait::SatInstance<Lit> for IdlSolver {
  fn new_var(&mut self) -> Lit { self.new_bool() }
  fn add_clause(&mut self, c :impl IntoIterator<Item = impl Into<Lit>>) {
    self.add_clause(&c.into_iter().map(|l| l.into()).collect::<Vec<_>>());
  }
}


