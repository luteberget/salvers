pub mod longestpaths;
use longestpaths::*;

use mysatsolver::*;
use sattrait;
pub use mysatsolver::Lit;
use smallvec::SmallVec;
use std::collections::{HashMap};

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// Integer variable for use in scheduling constraints (see `SchedulingSolver`).
pub struct DVar(Node);

struct SchedulingTheory {
  conditions :HashMap<Lit, Edge>, // Map from bool variable to edge
  graph :IncrementalLongestPaths,

  #[cfg(debug_assertions)]
  requires_backtrack :bool,

  trail :Vec<Edge>,
  trail_lim :Vec<usize>,
}

impl SchedulingTheory {
  fn new() -> Self {
    SchedulingTheory {
      conditions: HashMap::new(),
      #[cfg(debug_assertions)]
      requires_backtrack: false,
      graph: IncrementalLongestPaths::new(),
      trail: Vec::new(),
      trail_lim: Vec::new(),
    }
  }

  fn new_int(&mut self) -> DVar {
    DVar(self.graph.new_node())
  }

  fn add_constraint(&mut self, lit :Option<Lit>, DVar(x) :DVar, DVar(y) :DVar, length :u32) {
    let _p = hprof::enter("add scheduling constraint");
    let edge = self.graph.new_edge(x, y, length);
    if let Some(lit) = lit {
      self.conditions.insert(lit, edge);
    } else {
      self.enable(edge);
    }
  }

  fn enable(&mut self, e :Edge) -> bool {
    let _p = hprof::enter("scheduling enable");
    let activated = self.graph.activate(e, &mut |_,_,_| {});
    if activated { self.trail.push(e); }
    activated
  }
}

impl Theory for SchedulingTheory {
  fn check(&mut self, _ch :Check, lits :&[Lit], buf :&mut Refinement) {
    #[cfg(debug_assertions)] assert!(!self.requires_backtrack);
    
    for lit in lits {
      if let Some(edge_idx) = self.conditions.get(lit) {
        if !self.graph.activate(*edge_idx) {
          //buf.add_clause(self.graph.conflict.iter())

          #[cfg(debug_assertions)]
          {
            self.requires_backtrack = true;
          }

          return;

        } else {
            self.trail.push(edge_idx);
        }
      } else {
        println!("irrelevant lit {:?}", lit);
      }
    }
  }

  fn explain(&mut self, _l :Lit, _x :u32, _buf :&mut Refinement) {
    unreachable!()
  }

  fn new_decision_level(&mut self) {
    self.trail_lim.push(self.trail.len());
  }

  fn backtrack(&mut self, level :i32) {
    if (level as usize) < self.trail_lim.len() {
      #[cfg(debug_assertions)]
      { 
        self.requires_backtrack = false;
      }

      for edge in self.trail.drain(self.trail_lim[level as usize]..) {
        self.graph.deactivate(edge, &mut |_,_,_| {}); 
      }

      self.trail_lim.truncate(level as usize);
    }
  }
}

pub struct SchedulingSolver {
    prop: DplltSolver<SchedulingTheory>,
    was_sat :bool,
}

impl SchedulingSolver {
   pub fn new() -> Self {
     SchedulingSolver {
       prop: DplltSolver::new(SchedulingTheory::new()),
       was_sat :false,
     }
   }

   fn theory(&mut self) -> &mut SchedulingTheory {
     &mut self.prop.theory
   }

   pub fn new_bool(&mut self) -> Lit {
     self.prop.new_var_default()
   }

   pub fn new_int(&mut self) -> DVar {
     self.theory().new_int()
   }

   pub fn add_clause(&mut self, v :&[Lit]) {
     self.prop.add_clause(v.iter().cloned());
   }

   pub fn add_diff(&mut self, lit :Option<Lit>, x :DVar, y :DVar, l :u32) {
     self.theory().add_constraint(lit, x, y, l);
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

   pub fn get_int_value(&mut self, DVar(x) :DVar) -> u32 {
     self.prop.theory.graph.value(x)
   }

   pub fn get_bool_value(&self, lit :Lit) -> bool {
     self.prop.value(lit)
   }

}

pub struct Model<'a> {
  solver :&'a SchedulingSolver,
}


