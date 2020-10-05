use crate::clausedb::*;
use crate::bools::*;


#[derive(Debug, Clone, PartialEq, Eq, Copy)]
struct Watcher {
    cref: ClauseHeaderOffset,
    blocker: Lit,
}

type VMap<T> = Vec<T>;
type LMap<T> = Vec<T>;

pub struct UnitPropagator {
  next_var :i32,
  clause_database :ClauseDatabase,
  trail :Vec<Lit>,
  ok :bool,

  /// the index that split the constant part (decision level zero) from the 
  /// user-pushed assignment literals.
  const_lim: usize,
  qhead: usize,

  assigns :VMap<LBool>,
  watch_occs :LMap<Vec<Watcher>>,
  add_tmp :Vec<Lit>,
}

impl UnitPropagator {
  pub fn new() -> Self {
    UnitPropagator {
        next_var: 0,
        clause_database: ClauseDatabase {
	    clause_data :Vec::new(),
            wasted: 0,
        },
        trail: Vec::new(),
        ok: true,
        const_lim: 0,
        qhead: 0,
        watch_occs: Vec::new(),
        add_tmp :Vec::new(),
        assigns: Vec::new(),
    }
  }

  pub fn new_var(&mut self) -> Lit {
    let var = Var((self.next_var, self.next_var += 1).0);
    map_insert(&mut self.watch_occs, Lit::new(var, false).0 as usize, Default::default(), Default::default());
    map_insert(&mut self.watch_occs, Lit::new(var, true).0 as usize, Default::default(), Default::default());
    map_insert(&mut self.assigns, var.0 as usize, Default::default(), Default::default());
    Lit::new(var, false)
  }


    fn var_value(&self, var: Var) -> LBool {
        self.assigns[var.0 as usize]
    }

    pub fn lit_value(&self, lit: Lit) -> LBool {
        Self::assigns_lit_value(&self.assigns, lit)
    }

    fn assigns_lit_value(assigns: &Vec<LBool>, lit: Lit) -> LBool {
        LBool::xor(&assigns[lit.var().0 as usize], lit.sign())
    }

   pub fn backtrack(&mut self, pos :usize) {
       let assigns = &mut self.assigns;
       let trail = &mut self.trail;
       let idx = self.const_lim + pos;
       for lit in trail.drain(idx..).rev() {
           assigns[lit.var().0 as usize] = LBOOL_UNDEF;
       }
       self.qhead = idx;
   }

   pub fn extend(&mut self, ps :impl IntoIterator<Item = Lit>) -> bool {
       for p in ps.into_iter() {
          self.assign(p);
       }
       self.propagate() == CLAUSE_NONE
   }

   pub fn pos(&self) -> usize { self.trail.len() - self.const_lim }

   pub fn add_clause(&mut self, ps :impl IntoIterator<Item = Lit>) -> bool {
       assert!(self.const_lim == self.trail.len());
       assert!(self.pos() == 0);
 
       self.add_tmp.clear();
       self.add_tmp.extend(ps);
       self.add_tmp.sort();
       {
           let mut prev = LIT_UNDEF;
           let mut already_sat = false;
           let add_tmp = &mut self.add_tmp;
           let assigns = &self.assigns;
           add_tmp.retain(|l| {
               if Self::assigns_lit_value(assigns, *l) == LBOOL_TRUE || *l == prev.inverse() {
                   already_sat = true;
               }
               (prev, prev=*l).0 != *l && Self::assigns_lit_value(assigns, *l) != LBOOL_FALSE
           });
           if already_sat { return true; }
       }

       if self.add_tmp.len() == 0 {
          self.ok = false;
          return false;
       } else if self.add_tmp.len() == 1 {
         self.assign(self.add_tmp[0]);
         self.const_lim += 1;
         self.ok = self.propagate() == CLAUSE_NONE;
         return self.ok;
       } else {
         let cref = self.clause_database.add_clause(&self.add_tmp, false);
         self.attach_clause(cref);
       }
       true
   }

   fn assign(&mut self, l :Lit) {
      self.assigns[l.var().0 as usize] = LBool::from_bool(l.sign());
      self.trail.push(l);
   }

   fn attach_clause(&mut self, cref: ClauseHeaderOffset) {
       let header = self.clause_database.get_header(cref);
       let sz = header.get_size();
       assert!(sz > 1);

       let lits = self.clause_database.get_lits(cref, sz as usize);
       self.watch_occs[lits[0].inverse().0 as usize].push(Watcher {
           cref, blocker: lits[1],
       });
       self.watch_occs[lits[1].inverse().0 as usize].push(Watcher {
           cref, blocker: lits[0],
       });
   }


   fn propagate(&mut self) -> ClauseHeaderOffset {
      let mut conflict_clause = CLAUSE_NONE;
      let mut num_props = 0;
      while self.qhead < self.trail.len() {
          let p = self.trail[self.qhead];
          self.qhead += 1;
          // We don't need to clean the watch list here (like in minisat) because we never detach clauses.

          let (mut i, mut j) = (0, 0);
          'for_each_watch: while i < self.watch_occs[p.0 as usize].len() {
              let assigns = &self.assigns;
              let watches = &mut self.watch_occs[p.0 as usize];
              let blocker = watches[i].blocker;
              let cref = watches[i].cref;
              if Self::assigns_lit_value(assigns, blocker) == LBOOL_TRUE {
                  watches[j] = watches[i];
                  j += 1; i += 1;
                  continue;
              }

              let header = self.clause_database.get_header(cref);
              let lits = self.clause_database.get_lits_mut(cref, header.get_size() as usize);
              let false_lit = p.inverse();

              if lits[0] == false_lit {
                  lits.swap(0,1);
              }

              assert!(lits[1] == false_lit);
              i += 1;
              
              let first = lits[0];
              let w = Watcher { cref, blocker: first };

              if first != blocker && Self::assigns_lit_value(assigns, first) == LBOOL_TRUE {
                  watches[j] = w;
                  j += 1;
                  continue;
              }

              let mut k = 2;
              while k < lits.len() {
                  if Self::assigns_lit_value(assigns, lits[k]) != LBOOL_FALSE {
                      lits[1] = lits[k];
                      lits[k] = false_lit;
                      self.watch_occs[lits[1].inverse().0 as usize].push(w);
                      continue 'for_each_watch;
                  } else {
                      k += 1;
                  }
              }

              watches[j] = w;
              j += 1;
              if Self::assigns_lit_value(assigns, first) == LBOOL_FALSE {
                  conflict_clause = cref;
                  self.qhead = self.trail.len();
                  while i < self.watch_occs[p.0 as usize].len() {
                      self.watch_occs[p.0 as usize][j] = self.watch_occs[p.0 as usize][i];
                      j += 1; i += 1;
                  }
              } else {
                  self.assign(first);
                  //self.assign(first, cref); // TODO use clause references for reporting conflict?
              }
          }

          self.watch_occs[p.0 as usize].truncate(j);
      }

      conflict_clause
   }
}

fn var_map_insert<T: Default + Clone>(map: &mut Vec<T>, Var(idx): Var, value: T, default: T) {
    map_insert(map, idx as usize, value, default)
}

fn map_insert<T: Default + Clone>(map: &mut Vec<T>, idx: usize, value: T, default: T) {
    map.resize((idx as usize + 1).max(map.len()), default);
    map[idx as usize] = value;
}

