use crate::orderheap::*;
use smallvec::*;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Node(u32);

impl Node {
    pub fn idx(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Edge(u32);

#[derive(Debug)]
struct EdgeData {
    source: i32,
    target: u32,
    distance: i32,
}

pub struct LongestPaths {
    n_nodes: usize,
    n_edges: usize,
    edge_data: Vec<EdgeData>,
    node_outgoing: Vec<SmallVec<[u32; 4]>>,
    node_incoming: Vec<SmallVec<[u32; 4]>>,
    node_updated_from: Vec<i32>,
    values: Vec<i32>,

    current_updates: Vec<(u32, i32)>, // node -> overwritten value
    queue: OrderHeap,
}

pub struct Values {
    values: Vec<i32>,
}

impl Values {
    pub fn get(&self, n: Node) -> i32 {
        self.values[n.0 as usize]
    }
}

impl LongestPaths {
    pub fn new() -> Self {
        let mut p = LongestPaths {
            n_nodes: 0,
            n_edges: 0,
            edge_data: Vec::new(),
            node_outgoing: Vec::new(),
            node_incoming: Vec::new(),
            node_updated_from: Vec::new(),
            values: Vec::new(),

            current_updates: Vec::new(),
            queue: OrderHeap::new(),
        };
        p.new_node(); // waste the first node because we need the sign bit
        p
    }

    pub fn new_node(&mut self) -> Node {
        let node = Node(self.n_nodes as u32);
        self.n_nodes += 1;
        self.node_outgoing.push(Default::default());
        self.node_incoming.push(Default::default());
        self.node_updated_from.push(-1);
        self.values.push(0);
        node
    }

    pub fn new_edge(&mut self, a: Node, b: Node, l: i32) -> Edge {
        let edge = Edge(self.n_edges as u32);
        self.n_edges += 1;
        self.edge_data.push(EdgeData {
            source: -(a.0 as i32), // negative because it is disabled
            target: b.0,
            distance: l,
        });
        self.node_outgoing[a.0 as usize].push(edge.0);
        self.node_incoming[b.0 as usize].push(edge.0);
        edge
    }

    pub fn value(&self, node: Node) -> i32 {
        self.values[node.0 as usize]
    }

    pub fn all_values(&self) -> Values {
        Values {
            values: self.values.clone(),
        }
    }

    pub fn critical_path<'a>(&'a self, node: Node) -> impl Iterator<Item = Edge> + 'a {
        CriticalPathIterator { graph: self, node }
    }

    pub fn critical_set<'a>(
        &'a self,
        nodes: impl IntoIterator<Item = Node>,
    ) -> impl Iterator<Item = Edge> + 'a {
        // Assuming here that self.values is a topological ordering.
        // That only works if we have no negative-time edges (?).
        let mut heap = OrderHeap::new();
        for node in nodes.into_iter() {
            debug_assert!(!heap.contains(node.0 as i32));
            let values = &self.values;
            heap.insert(
                node.0 as i32,
                |n| -values[*n as usize], /* largest first */
            );
        }

        CriticalSetIterator { graph: self, heap }
    }

    pub fn enable_edge<'a>(&'a mut self, edge: Edge) -> Result<(), CycleIterator<'a>> {
        self.enable_edge_cb(edge, |_, _, _| {})
    }

    pub fn enable_edge_cb<'a>(
        &'a mut self,
        Edge(add_idx): Edge,
        mut event: impl FnMut(Node, i32, i32),
    ) -> Result<(), CycleIterator<'a>> {
        let edge = &mut self.edge_data[add_idx as usize];

        //let mut debug = false; if add_idx == 6 { println!("adding edge 6"); debug=true; }

        let was_already_enabled = edge.source > 0;
        if was_already_enabled {
            //println!("enable_edge: was already enabled");
            return Ok(());
        }
        // Enable edge
        edge.source *= -1;

        let is_critical =
            self.values[edge.source as usize] + edge.distance > self.values[edge.target as usize];
        if !is_critical {
            //println!("enable_edge: was not critical");
            //println!(" edge: {:?}", edge);
            //println!(" values: {:?}", self.values);
            return Ok(());
        }

        //println!("enable_edge: nontrivial");
        self.current_updates.clear();
        debug_assert!(self.queue.is_empty());
        {
            let values = &self.values;
            let edges = &self.edge_data;
            self.queue.insert(add_idx as i32, |i| {
                values[edges[*i as usize].target as usize]
            });
        }

        let mut updated_root = false;
        while let Some(edge_idx) = {
            let values = &self.values;
            let edges = &self.edge_data;
            self.queue
                .remove_min(|i| values[edges[*i as usize].target as usize])
        } {
            let edge = &self.edge_data[edge_idx as usize];
            //if debug { println!("Enabling edge {:?}", edge); }
            let target_updated = self.values[edge.source as usize] + edge.distance
                > self.values[edge.target as usize];

            if target_updated {
                if updated_root && edge_idx == add_idx as i32 {
                    // Forget about the queued edges.
                    self.queue.clear();

                    // Backtrack updated node values
                    for (node, dist) in self.current_updates.iter().rev() {
                        self.values[*node as usize] = *dist;
                    }

                    // Backtrack on constraint-active-flag
                    self.edge_data[add_idx as usize].source *= -1;
                    debug_assert!(self.edge_data[add_idx as usize].source < 0);

                    // Return the cycle.
                    let node = Node(self.edge_data[add_idx as usize].target);
                    return Err(CycleIterator {
                        graph: self,
                        node: Some(node),
                        start_node: node,
                    });
                }

                updated_root = true;
                self.current_updates
                    .push((edge.target, self.values[edge.target as usize]));
                let old_value = self.values[edge.target as usize];
                let new_value = self.values[edge.source as usize] + edge.distance;
                self.values[edge.target as usize] = new_value;
                //if debug { println!(
                //    "enable: setting {:?} from {} to {}",
                //    Node(edge.target),
                //    old_value,
                //    new_value
                //); }
                event(Node(edge.target), old_value, new_value);

                self.node_updated_from[edge.target as usize] = edge_idx;
                //if debug { println!("edge.target {} updated from {}", edge.target, edge_idx); }

                for next_edge_idx in self.node_outgoing[edge.target as usize].iter() {
                    if self.edge_data[*next_edge_idx as usize].source < 0 {
                        continue;
                    }
                    if self.queue.contains(*next_edge_idx as i32) {
                        continue;
                    }
                    let values = &self.values;
                    let edges = &self.edge_data;
                    self.queue.insert(*next_edge_idx as i32, |i| {
                        values[edges[*i as usize].target as usize]
                    });
                }
            }
        }

        Ok(())
    }

    pub fn disable_edges(&mut self, edges: impl IntoIterator<Item = Edge>) {
        self.disable_edges_cb(edges, |_, _, _| {})
    }

    pub fn disable_edges_cb(
        &mut self,
        edges: impl IntoIterator<Item = Edge>,
        mut event: impl FnMut(Node, i32, i32),
    ) {
        //panic!();
        debug_assert!(self.queue.is_empty());

        // Add the edges-to-be-disabled to the heap.
        let mut i = 0;
        let mut j = 0;
        for Edge(edge_idx) in edges.into_iter() {
            i += 1;
            let edge = &mut self.edge_data[edge_idx as usize];

            // Was it already disabled?
            let was_enabled = edge.source > 0;
            if !was_enabled {
                //println!("disable {:?}: was already enabled", edge_idx);
                continue;
            }
            edge.source *= -1;

            let is_not_critical = self.values[-edge.source as usize] + edge.distance
                < self.values[edge.target as usize];
            if is_not_critical {
                //println!("disable {:?}: was not critical", edge_idx);
                continue;
            }

            if self.queue.contains(edge_idx as i32) {
                continue;
            }
            let values = &self.values;
            let edges = &self.edge_data;
            //println!("adding to queue {:?}", edge_idx);
            j += 1;
            self.queue.insert(edge_idx as i32, |i| {
                values[edges[*i as usize].target as usize]
            });
        }

        //println!("disabling {}/{} edges", j, i);

        while let Some(edge_idx) = {
            let values = &self.values;
            let edges = &self.edge_data;
            self.queue
                .remove_min(|i| values[edges[*i as usize].target as usize])
        } {
            let edge = &self.edge_data[edge_idx as usize];

            // The values should already be consistent with this edge.
            //debug_assert!(
            //    self.values[edge.source.abs() as usize] + edge.distance
            //        <= self.values[edge.target as usize]
            //);

            let is_critical = self.node_updated_from[edge.target as usize] == edge_idx;
            //println!(
            //    "popping heap: is edge {:?} critical: {:?}",
            //    edge, is_critical
            //);
            //println!("  node updated from: {:?}", self.node_updated_from);
            //println!("  values: {:?}", self.values);
            if is_critical {
                //let edge_min_value = self.values[edge.source.abs() as usize] + edge.distance;

                // This assertion is wrong, because the source node might be further back than it
                // used to be when the node_updated_from pointer was set.
                //debug_assert!(edge_min_value == self.values[edge.target as usize]);

                // Look backwards to find a critical edge
                let mut critical_edge = None;
                let mut critical_dist = 0;
                for prev_edge_idx in self.node_incoming[edge.target as usize].iter() {
                    let edge_data = &self.edge_data[*prev_edge_idx as usize];
                    if edge_data.source < 0 {
                        continue;
                    }
                    let new_value = self.values[edge_data.source as usize] + edge_data.distance;
                    if new_value > critical_dist {
                        critical_dist = new_value;
                        critical_edge = Some(*prev_edge_idx);
                    }
                }

                let old_value = self.values[edge.target as usize];
                if let Some(critical_edge) = critical_edge {
                    self.node_updated_from[edge.target as usize] = critical_edge as i32;
                    debug_assert!(critical_dist <= self.values[edge.target as usize]);
                    debug_assert!(self.edge_data[critical_edge as usize].source > 0);
                    debug_assert!(self.edge_data[critical_edge as usize].target == edge.target);
                } else {
                    self.node_updated_from[edge.target as usize] = -1;
                }

                let new_value = critical_dist;
                if new_value < old_value {
                    // Update the value
                    self.values[edge.target as usize] = new_value;
                    //println!(
                    //    "disable: setting {:?} from {} to {}",
                    //    Node(edge.target),
                    //    old_value,
                    //    new_value
                    //);
                    event(Node(edge.target), old_value, new_value);

                    // Add outgoing edges to the update queue.
                    for next_edge_idx in self.node_outgoing[edge.target as usize].iter() {
                        if self.edge_data[*next_edge_idx as usize].source < 0 {
                            continue;
                        }
                        if self.queue.contains(*next_edge_idx as i32) {
                            continue;
                        }
                        let values = &self.values;
                        let edges = &self.edge_data;
                        self.queue.insert(*next_edge_idx as i32, |i| {
                            values[edges[*i as usize].target as usize]
                        });
                    }
                }
            }
        }
        //println!("  disable-final-values: {:?}", self.values);
    }
}

pub struct CycleIterator<'a> {
    graph: &'a LongestPaths,
    start_node: Node,
    node: Option<Node>,
}

impl<'a> Iterator for CycleIterator<'a> {
    type Item = Edge;

    fn next(&mut self) -> Option<Edge> {
        if let Some(node) = self.node {
            let edge_idx = self.graph.node_updated_from[node.0 as usize];
            let edge = &self.graph.edge_data[edge_idx as usize];
            //debug_assert!(edge.source > 0);
            if edge.source.abs() == self.start_node.0 as i32 {
                // Iterator done
                self.node = None;
            } else {
                self.node = Some(Node(edge.source.abs() as u32));
            }
            Some(Edge(edge_idx as u32))
        } else {
            None
        }
    }
}

//
// TODO: if there are multiple critical paths that are all the same (maximal) length
// then the consumer could want all of them.
// For example, if the iterator is used for backtracking a search, there might be an
// efficiency gain in finding many paths here at the same time.
//

pub struct CriticalPathIterator<'a> {
    graph: &'a LongestPaths,
    node: Node,
}

impl<'a> Iterator for CriticalPathIterator<'a> {
    type Item = Edge;

    fn next(&mut self) -> Option<Edge> {
        let edge_idx = self.graph.node_updated_from[self.node.0 as usize];
        if edge_idx == -1 {
            None
        } else {
            debug_assert!(self.graph.edge_data[edge_idx as usize].source > 0);
            self.node = Node(self.graph.edge_data[edge_idx as usize].source as u32);
            Some(Edge(edge_idx as u32))
        }
    }
}

pub struct CriticalSetIterator<'a> {
    graph: &'a LongestPaths,
    heap: OrderHeap,
}

impl<'a> Iterator for CriticalSetIterator<'a> {
    type Item = Edge;

    fn next(&mut self) -> Option<Edge> {
        let values = &self.graph.values;
        if let Some(node_idx) = self.heap.remove_min(|n| -values[*n as usize]) {
            let edge_idx = self.graph.node_updated_from[node_idx as usize];
            if edge_idx != -1 {
                let edge = &self.graph.edge_data[edge_idx as usize];
                debug_assert!(edge.source > 0); // is enabled
                let values = &self.graph.values;
                if !self.heap.contains(edge_idx) {
                    self.heap.insert(edge_idx, |n| -values[*n as usize]);
                }
                return Some(Edge(edge_idx as u32));
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cycle() {
        let mut lp = LongestPaths::new();
        let n1 = lp.new_node();
        let n2 = lp.new_node();
        let n3 = lp.new_node();

        let e1 = lp.new_edge(n1, n2, 5);
        let _e2 = lp.new_edge(n2, n3, 5);
        let e3 = lp.new_edge(n1, n3, 6);
        let e4 = lp.new_edge(n3, n1, 1);

        assert!(lp.enable_edge(e1).is_ok());
        assert!(lp.enable_edge(e4).is_ok());
        if let Err(cycle) = lp.enable_edge(e3) {
            let cycle = cycle.collect::<Vec<_>>();
            assert_eq!(cycle, vec![e3, e4]);
        } else {
            panic!();
        }
    }

    #[test]
    fn basic() {
        let mut lp = LongestPaths::new();
        let n1 = lp.new_node();
        let n2 = lp.new_node();
        let n3 = lp.new_node();

        let e1 = lp.new_edge(n1, n2, 5);
        let e2 = lp.new_edge(n2, n3, 5);
        let e3 = lp.new_edge(n1, n3, 6);

        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 0);
        assert!(lp.value(n3) == 0);

        assert!(lp.enable_edge(e1).is_ok());
        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 5);
        assert!(lp.value(n3) == 0);

        lp.disable_edges(Some(e1));
        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 0);
        assert!(lp.value(n3) == 0);

        assert!(lp.enable_edge(e1).is_ok());
        assert!(lp.enable_edge(e2).is_ok());
        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 5);
        assert!(lp.value(n3) == 10);
        println!(
            "critical path from n3 {:?}",
            lp.critical_path(n3).collect::<Vec<_>>()
        );
        assert!(lp.critical_path(n3).collect::<Vec<_>>() == vec![e2, e1]);

        assert!(lp.enable_edge(e3).is_ok());
        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 5);
        assert!(lp.value(n3) == 10);

        lp.disable_edges(vec![e1, e2, e3]);
        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 0);
        assert!(lp.value(n3) == 0);

        assert!(lp.enable_edge(e3).is_ok());
        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 0);
        assert!(lp.value(n3) == 6);

        assert!(lp.enable_edge(e2).is_ok());
        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 0);
        assert!(lp.value(n3) == 6);

        println!("X");
        println!("values {:?}", lp.values);
        assert!(lp.enable_edge(e1).is_ok());
        println!("values {:?}", lp.values);
        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 5);
        assert!(lp.value(n3) == 10);

        lp.disable_edges(Some(e3));
        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 5);
        assert!(lp.value(n3) == 10);
        assert!(lp.enable_edge(e3).is_ok());
        lp.disable_edges(Some(e2));
        println!("values {:?}", lp.values);
        assert!(lp.value(n1) == 0);
        assert!(lp.value(n2) == 5);
        assert!(lp.value(n3) == 6);

        println!("parents: {:?}", lp.node_updated_from);
    }

    #[test]
    fn remove_root() {
        let mut lp = LongestPaths::new();
        let n1 = lp.new_node();
        let n2 = lp.new_node();
        let n3 = lp.new_node();
        let n4 = lp.new_node();

        let e1 = lp.new_edge(n1, n2, 5);
        let e2 = lp.new_edge(n2, n3, 5);
        let e3 = lp.new_edge(n3, n4, 5);

        for e in vec![e1, e2, e3] {
            assert!(lp.enable_edge(e).is_ok());
        }
        assert_eq!(lp.value(n1), 0);
        assert_eq!(lp.value(n2), 5);
        assert_eq!(lp.value(n3), 10);
        assert_eq!(lp.value(n4), 15);

        lp.disable_edges(Some(e1));
        assert_eq!(lp.value(n1), 0);
        assert_eq!(lp.value(n2), 0);
        assert_eq!(lp.value(n3), 5);
        assert_eq!(lp.value(n4), 10);
    }

    #[test]
    fn critical_set() {
        let mut lp = LongestPaths::new();

        let n1 = lp.new_node();
        let n2 = lp.new_node();
        let n3 = lp.new_node();
        let n4 = lp.new_node();

        let e1 = lp.new_edge(n1, n2, 5);
        let e2 = lp.new_edge(n2, n3, 5);
        let e3 = lp.new_edge(n2, n4, 6);

        assert!(lp.enable_edge(e3).is_ok());
        assert!(lp.enable_edge(e2).is_ok());
        assert!(lp.enable_edge(e1).is_ok());

        let critical_set = lp.critical_set(vec![n3, n4]).collect::<Vec<Edge>>();
        assert_eq!(critical_set, vec![e3, e2, e1]);
    }
}
