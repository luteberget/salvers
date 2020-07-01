use std::collections::{HashMap, HashSet, BinaryHeap, VecDeque};
use smallvec::*;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Node(u32);

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Edge(u32);

pub struct IncrementalLongestPaths {
  n_nodes :usize,
  n_edges :usize,
  edge_data :Vec<EdgeData>,
  node_outgoing :Vec<SmallVec<[Edge;4]>>,
  node_incoming :Vec<SmallVec<[Edge;4]>>,
  node_location :Vec<u32>,
  scratch :IncrPathsScratch,
}

struct IncrPathsScratch {
  queue : BinaryHeap<(u32,u32)>,
  affected :HashSet<u32>,
  deque :VecDeque<u32>,
}

struct EdgeData {
  start_node :Node,
  end_node :Node,
  length :u32,
  is_activated: bool,
  is_critical: bool,
}

impl IncrementalLongestPaths {

  pub fn new() -> Self { 
    IncrementalLongestPaths {
      n_nodes: 0,
      n_edges: 0,
      edge_data: Vec::new(),
      node_outgoing: Vec::new(),
      node_incoming: Vec::new(),
      node_location: Vec::new(),
      scratch: IncrPathsScratch { 
        queue: BinaryHeap::new(),
        affected: HashSet::new(),
        deque: VecDeque::new(),
      },
    }
  }

  pub fn value(&self, node: Node) -> u32 {
    self.node_location[node.0 as usize]
  }

  pub fn new_node(&mut self) -> Node {
    let node = Node(self.n_nodes as u32);
    self.n_nodes += 1;
    self.node_location.push(0);
    self.node_incoming.push(SmallVec::new());
    self.node_outgoing.push(SmallVec::new());
    node
  }

  pub fn new_edge(&mut self, a :Node, b :Node, l :u32) -> Edge {
    let edge = Edge(self.n_edges as u32);
    self.n_edges += 1;

    self.edge_data.push(EdgeData {
      start_node: a,
      end_node: b,
      length: l,
      is_activated: false,
      is_critical: false,
    });

    self.node_outgoing[a.0 as usize].push(edge);
    self.node_incoming[b.0 as usize].push(edge);

    edge
  }

  fn update_path(&mut self, node :Node, update :&mut impl FnMut(Node,u32,u32)) {
    let old_value = self.value(node);
    let new_value = self.node_incoming[node.0 as usize].iter().filter_map(|e| {
        let edge_data = &self.edge_data[e.0 as usize];
        if !edge_data.is_activated { return None; }
        Some(self.value(edge_data.start_node) + edge_data.length)
    }).max().unwrap_or(0);
 
    if old_value != new_value {
      self.node_location[node.0 as usize] = new_value;
      update(node, old_value, new_value);
    }
  }

  pub fn deactivate(&mut self, edge :Edge, update :&mut impl FnMut(Node,u32,u32)) {
    if !self.edge_data[edge.0 as usize].is_activated { return; }
    self.edge_data[edge.0 as usize].is_activated = false;
    if !self.edge_data[edge.0 as usize].is_critical { return; }
    self.edge_data[edge.0 as usize].is_critical = false;

    let edge_data = &self.edge_data[edge.0 as usize];
    let had_other_critical = self.node_incoming[edge_data.end_node.0 as usize].iter().any(|e| 
      self.edge_data[e.0 as usize].is_critical);
    if had_other_critical { return; }

    // Compute affected set
    self.scratch.affected.clear();
    debug_assert!(self.scratch.deque.len() == 0);
    self.scratch.deque.push_back(edge_data.end_node.0);
    while let Some(node) = self.scratch.deque.pop_front() {
      self.scratch.affected.insert(node);
      for outgoing_edge in self.node_outgoing[node as usize].iter() {
        let edge_data = &self.edge_data[outgoing_edge.0 as usize];
        let next_node = edge_data.end_node;
        if !edge_data.is_activated || !edge_data.is_critical { continue; }
        self.edge_data[outgoing_edge.0 as usize].is_critical = false;
        let has_critical = self.node_incoming[next_node.0 as usize].iter()
		.any(|e| self.edge_data[e.0 as usize].is_critical);
        if !has_critical {
          self.scratch.deque.push_back(next_node.0);
        }
      }
    }

    let mut degreelp = self.scratch.affected.iter().map(|n| {
        let count = self.node_incoming[*n as usize].iter()
                        .filter(|e| self.scratch.affected.contains(&self.edge_data[e.0 as usize].start_node.0))
                        .count() as u32;
        (*n, count)
    }).collect::<HashMap<u32,u32>>();

    debug_assert!(self.scratch.deque.len() == 0);
    self.scratch.deque.extend(degreelp.iter().filter_map(|(n,d)| if *d == 0 { Some(*n) } else { None }));
    
    while let Some(node) = self.scratch.deque.pop_front() {
      debug_assert!(self.scratch.affected.contains(&node));
      self.update_path(Node(node), update);
      
      for e in self.node_incoming[node as usize].iter() {
        let edge_data = &self.edge_data[e.0 as usize];
        if !edge_data.is_activated { continue; }
        debug_assert!(edge_data.end_node.0 == node);
        if self.value(edge_data.start_node) + edge_data.length == self.value(edge_data.end_node) {
          self.edge_data[e.0 as usize].is_critical = true;
        }
      }

      for e in self.node_outgoing[node as usize].iter() {
        let edge_data = &self.edge_data[e.0 as usize];
        if !edge_data.is_activated { continue; }
        *degreelp.get_mut(&edge_data.end_node.0).unwrap() -= 1;
        if degreelp[&edge_data.end_node.0]  == 0 {
          self.scratch.deque.push_back(edge_data.end_node.0);
        }
      }
    }
  }

  pub fn activate(&mut self, edge :Edge, update :&mut impl FnMut(Node,u32,u32)) -> bool {
    debug_assert!(self.scratch.queue.len() == 0);
    if self.edge_data[edge.0 as usize].is_activated { return true; }
    self.edge_data[edge.0 as usize].is_activated = true;

    // TODO we need a trail of updates anyway for backtracking when cycles are detected.
    // So we might put seen and visited as bit fields on edge_data, and then undo them
    // when the function ends (at a cycle, at sum violation(?) or at success).
    let mut seen = HashSet::new();
    let mut visited = HashSet::new();

    let edge_data = &self.edge_data[edge.0 as usize];
    if self.value(edge_data.start_node) + edge_data.length > self.value(edge_data.end_node) {
      self.scratch.queue.push((self.value(edge_data.end_node), edge_data.end_node.0));
      while let Some((_,v)) = self.scratch.queue.pop() {
        visited.insert(v);
        self.update_path(Node(v), update);

        for e in self.node_incoming[v as usize].iter() {
          let edge_data = &self.edge_data[e.0 as usize];
          debug_assert!(v == edge_data.end_node.0);
          if !edge_data.is_activated { continue; }
          let is_critical = self.value(edge_data.start_node) + edge_data.length == self.value(edge_data.end_node);
          self.edge_data[e.0 as usize].is_critical = is_critical;
        }

        for e in self.node_outgoing[v as usize].iter() {
          let edge_data = &self.edge_data[e.0 as usize];
          debug_assert!(v == edge_data.start_node.0);
          if !edge_data.is_activated { continue; }

          if self.value(Node(v)) + edge_data.length > self.value(edge_data.end_node) {
            if !seen.contains(&edge_data.end_node.0) {
              seen.insert(edge_data.end_node.0);
              self.scratch.queue.push((self.value(edge_data.end_node), edge_data.end_node.0));
            } else if visited.contains(&edge_data.end_node.0) {
              panic!("cycle");
              return false;
            }
          } else if self.value(Node(v)) + edge_data.length == self.value(edge_data.end_node) {
            self.edge_data[e.0 as usize].is_critical = true;
          }
        }

      }
    } else if self.value(edge_data.start_node) + edge_data.length == self.value(edge_data.end_node) {
      self.edge_data[edge.0 as usize].is_critical = true;
    } else {
      // No need to do anything
    }

    true
  }
}

pub(crate) fn nonincremental_longest_paths(edges :&[(u32,u32,u32)]) -> HashMap<u32,u32> {
  let mut pred : HashMap<u32, Vec<(u32,u32)>> = HashMap::new();
  let mut succ : HashMap<u32, Vec<(u32,u32)>> = HashMap::new();
  let mut visited : HashSet<u32> = HashSet::new();
  let mut all_nodes : HashSet<u32> = HashSet::new();
  for (a,b,l) in edges.iter() {
    all_nodes.insert(*a);
    all_nodes.insert(*b);
    succ.entry(*a).or_insert(Vec::new()).push((*b, *l));
    pred.entry(*b).or_insert(Vec::new()).push((*a, *l));
  }

  let mut paths : HashMap<u32,u32> = HashMap::new();
  let mut queue = all_nodes.iter().filter(|x| pred.get(x).map(|preds| preds.len() == 0).unwrap_or(true)).cloned().collect::<Vec<_>>();

   while let Some(v) = queue.pop() {
     visited.insert(v);
     let new_path = pred.get(&v).iter().flat_map(|x| x.iter()).map(|(n,l)| paths[n] + l).max().unwrap();
     paths.insert(v, new_path);
     for (next_node,_) in succ.get(&v).iter().flat_map(|x| x.iter()) {
       let is_ready = pred.get(next_node).iter().flat_map(|x| x.iter()).all(|(prev_node,_l)| visited.contains(prev_node));
       if is_ready { queue.push(*next_node); }
     }
   }

  paths

}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  pub fn hello() {
    let mut incr = IncrementalLongestPaths::new();
    let nodes = (0..100).map(|x| incr.new_node()).collect::<Vec<_>>();
  }

  #[test]
  pub fn test_activate() {
    let mut incr = IncrementalLongestPaths::new();
    let n1 = incr.new_node();
    let n2 = incr.new_node();
    assert!(incr.value(n1) == 0);
    assert!(incr.value(n2) == 0);
    
    let e1 = incr.new_edge(n1,n2,5);
    incr.activate(e1, &mut |_,_,_| {});
    assert!(incr.value(n1) == 0);
    assert!(incr.value(n2) == 5);

    let e2 = incr.new_edge(n1,n2,6);
    incr.activate(e2, &mut |_,_,_| {});
    assert!(incr.value(n1) == 0);
    assert!(incr.value(n2) == 6);

    incr.deactivate(e2, &mut |_,_,_| {});
    assert!(incr.value(n1) == 0);
    assert!(incr.value(n2) == 5);
    
    
  }
}
