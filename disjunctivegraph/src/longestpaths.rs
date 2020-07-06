use smallvec::*;
use crate::orderheap::*;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Node(u32);

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Edge(u32);

struct EdgeData {
    source :i32,
    target :u32,
    distance :u32,
}

pub struct LongestPaths {
    n_nodes :usize,
    n_edges :usize,
    edge_data :Vec<EdgeData>,
    node_outgoing :Vec<SmallVec<[u32; 4]>>,
    node_incoming :Vec<SmallVec<[u32; 4]>>,
    node_updated_from :Vec<i32>,
    values :Vec<u32>,

    current_updates :Vec<(u32, u32)>, // node -> overwritten value
    queue :OrderHeap,
}

impl LongestPaths {
    pub fn new() -> Self {
        LongestPaths {
            n_nodes: 0,
            n_edges: 0,
            edge_data :Vec::new(),
            node_outgoing: Vec::new(),
            node_incoming: Vec::new(),
            node_updated_from :Vec::new(),
            values: Vec::new(),

            current_updates: Vec::new(),
            queue: OrderHeap::new(),
        }
    }

    pub fn new_node(&mut self) -> Node {
        let node = Node(self.n_nodes as u32 + 1);
        self.n_nodes += 1;
        self.node_outgoing.push(Default::default());
        self.node_incoming.push(Default::default());
        self.node_updated_from.push(-1);
        self.values.push(0);
        node
    }

    pub fn new_edge(&mut self, a :Node, b :Node, l :u32) -> Edge {
        let edge = Edge(self.n_edges as u32);
        self.n_edges += 1;
        self.edge_data.push(EdgeData {
            source: -(a.0 as i32), // negative because it is disabled
            target: b.0,
            distance: l,
        });
        edge
    }

    pub fn value(&self, node :Node) -> u32 { self.values[node.0 as usize] }

    pub fn enable_edge<'a>(&'a mut self, Edge(add_idx) :Edge, event :impl Fn(Node,u32,u32)) -> Result<(), CycleIterator<'a>> {
        let edge = &mut self.edge_data[add_idx as usize];

        let was_already_enabled = edge.source > 0;
        if was_already_enabled {
            return Ok(()); 
        }
        // Enable edge
        edge.source *= -1;

        let is_critical = self.values[edge.source as usize] + edge.distance < self.values[edge.target as usize];
        if !is_critical {
            return Ok(());
        }

        self.current_updates.clear();
        debug_assert!(self.queue.is_empty());
        {
            let values = &self.values;
            let edges = &self.edge_data;
            self.queue.insert(add_idx as i32, |i| values[edges[*i as usize].target as usize] as i32);
        }

        let mut updated_root = false;
        while let Some(edge_idx) = {
            let values = &self.values;
            let edges = &self.edge_data;
            self.queue.remove_min(|i| values[edges[*i as usize].target as usize] as i32)
        } {
            let edge = &self.edge_data[edge_idx as usize];
            let target_updated = self.values[edge.source as usize] + edge.distance < self.values[edge.target as usize];

            if target_updated {
                if updated_root && edge_idx == add_idx as i32 {
                    // Backtrack updated node values
                    for (node,dist) in self.current_updates.iter().rev() {
                        self.values[*node as usize] = *dist;
                    }

                    // Backtrack on constraint-active-flag
                    self.edge_data[add_idx as usize].source *= -1;
                    debug_assert!(self.edge_data[add_idx as usize].source < 0);

                    // Return the cycle.
                    return Err(CycleIterator { graph: self });
                }

                updated_root = true;
                self.current_updates.push((edge.target, self.values[edge.target as usize]));
                let old_value = self.values[edge.target as usize];
                let new_value = self.values[edge.source as usize] + edge.distance;
                self.values[edge.target as usize] = new_value;
                event(Node(edge.target), old_value, new_value);

                self.node_updated_from[edge.target as usize] = edge.source;

                for next_edge_idx in self.node_outgoing[edge.target as usize].iter() {
                    if self.edge_data[*next_edge_idx as usize].source < 0 { continue; }
                    if self.queue.contains(*next_edge_idx as i32) { continue; }
                    let values = &self.values;
                    let edges = &self.edge_data;
                    self.queue.insert(*next_edge_idx as i32,
                                      |i| values[edges[*i as usize].target as usize] as i32);
                }

            }

        }

        Ok(())
    }

    pub fn disable_edges(&mut self, edges :impl IntoIterator<Item = Edge>, event :impl Fn(Node, u32, u32)) {

        debug_assert!(self.queue.is_empty());

        // Add the edges-to-be-disabled to the heap.
        for Edge(edge_idx) in edges.into_iter() {
            let edge = &mut self.edge_data[edge_idx as usize];

            // Was it already disabled?
            let was_enabled = edge.source > 0;
            if !was_enabled {
                continue; 
            }
            edge.source *= -1;

            let is_critical = self.values[edge.source as usize] + edge.distance < self.values[edge.target as usize];
            if !is_critical {
                continue;
            }

            if self.queue.contains(edge_idx as i32) { continue; }
            let values = &self.values;
            let edges = &self.edge_data;
            self.queue.insert(edge_idx as i32, 
                              |i| values[edges[*i as usize].target as usize] as i32);
        }


        while let Some(edge_idx) = {
            let values = &self.values;
            let edges = &self.edge_data;
            self.queue.remove_min(|i| values[edges[*i as usize].target as usize] as i32)
        } {
            let edge = &self.edge_data[edge_idx as usize];

            // The values should already be consistent with this edge.
            debug_assert!(self.values[-edge.source as usize] + edge.distance <= self.values[edge.target as usize]);

            let is_critical = self.node_updated_from[edge.target as usize] == edge_idx;
            if is_critical {
                let edge_min_value = self.values[-edge.source as usize] + edge.distance;
                debug_assert!(edge_min_value == self.values[edge.target as usize]);

                // Look backwards to find a critical edge
                let mut critical_edge = None;
                let mut critical_dist = 0;
                for prev_edge_idx in self.node_incoming[edge.target as usize].iter() {
                    let edge_data = &self.edge_data[*prev_edge_idx as usize];
                    if edge_data.source < 0 { continue; }
                    let new_value = self.values[edge_data.source as usize] + edge_data.distance;
                    if new_value > critical_dist {
                        critical_dist = new_value;
                        critical_edge = Some(*prev_edge_idx);
                    }
                }

                if let Some(critical_edge) = critical_edge {

                    self.node_updated_from[edge.target as usize] = critical_edge as i32;

                    debug_assert!(critical_dist <= self.values[edge.target as usize]);
                    debug_assert!(self.edge_data[critical_edge as usize].source > 0);
                    debug_assert!(self.edge_data[critical_edge as usize].target == edge.target);

                    let target_updated = critical_dist < self.values[edge.target as usize];
                    if target_updated {

                        // Update the value
                        let old_value = self.values[edge.target as usize];
                        let new_value = critical_dist;
                        debug_assert!(new_value < old_value);
                        self.values[edge.target as usize] = new_value;
                        event(Node(edge.target), old_value, new_value);

                        // Add outgoing edges to the update queue.
                        for next_edge_idx in self.node_outgoing[edge.target as usize].iter() {
                            if self.edge_data[*next_edge_idx as usize].source < 0 { continue; }
                            if self.queue.contains(*next_edge_idx as i32) { continue; }
                            let values = &self.values;
                            let edges = &self.edge_data;
                            self.queue.insert(*next_edge_idx as i32,
                                              |i| values[edges[*i as usize].target as usize] as i32);
                        }
                    }

                } else {
                    self.values[edge.target as usize] = 0;
                    self.node_updated_from[edge.target as usize] = -1;
                }
            }
        }
    }
}

pub struct CycleIterator<'a> {
   graph :&'a LongestPaths,
}

