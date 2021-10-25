use std::collections::VecDeque;

use crate::{prelude::Unary, Bool, Lit, SatInstance};

/// A tree-formed unary number relationship (totalizer constraint) with:
///  - equality constraints,
///  - bottom-up and top-down extensibility (increasing bounds)
pub struct EqTotalizer<L: Lit> {
    nodes: Vec<Node<L>>,
    original_n_nodes: usize,
    bound: usize,
}

struct Node<L: Lit> {
    number: Unary<L>,
    parent: Option<usize>,
    left: Option<usize>,
    right: Option<usize>,

    total_lits: usize,
    this_constraints: usize,
    left_constraints: usize,
    right_constraints: usize,
}

impl<L: Lit> Node<L> {
    fn new(unary: Unary<L>) -> Self {
        Node {
            total_lits: unary.bound(),
            number: unary,
            parent: None,
            left: None,
            right: None,
            this_constraints: 0,
            left_constraints: 0,
            right_constraints: 0,
        }
    }
}

impl<L: Lit> EqTotalizer<L> {
    pub fn new(nums: Vec<Unary<L>>) -> Self {
        let original_n_nodes = nums.len();
        assert!(original_n_nodes > 0);
        let mut nodes = nums.into_iter().map(Node::new).collect::<Vec<_>>();
        let mut unmerged_nodes = (0..nodes.len()).collect::<Vec<_>>();
        unmerged_nodes.sort_by_key(|n| nodes[*n].number.bound());
        let mut unmerged_nodes = unmerged_nodes.into_iter().collect::<VecDeque<_>>();

        while unmerged_nodes.len() >= 2 {
            let n1 = unmerged_nodes.pop_front().unwrap();
            let n2 = unmerged_nodes.pop_front().unwrap();

            let new_node_idx = nodes.len();
            nodes.push(Node {
                number: Unary::constant(0),
                parent: None,
                total_lits: nodes[n1].total_lits + nodes[n2].total_lits,
                left: Some(n1),
                right: Some(n2),
                this_constraints: 0,
                left_constraints: 0,
                right_constraints: 0,
            });
            nodes[n1].parent = Some(new_node_idx);
            nodes[n2].parent = Some(new_node_idx);
            unmerged_nodes.push_back(new_node_idx);
        }

        // The last node added is the root of the tree.
        assert!(unmerged_nodes.len() == 1);
        assert!(unmerged_nodes[0] + 1 == nodes.len());

        // This is now a valid totalizer tree, although with bound zero, so it has no constraints or new literals at all.
        EqTotalizer {
            nodes,
            original_n_nodes,
            bound: 0,
        }
    }

    pub fn bound(&self) -> usize {
        self.bound
    }

    pub fn number(&self) -> &Unary<L> {
        assert!(!self.nodes.is_empty());
        let node_idx = self.nodes.len() - 1;
        assert!(self.nodes[node_idx].parent.is_none());

        &self.nodes[node_idx].number
    }

    pub fn input_number(&self, node: usize) -> &Unary<L> {
        assert!(node < self.nodes.len());
        &self.nodes[node].number
    }

    pub fn increase_bound(&mut self, s: &mut impl SatInstance<L>, bound: usize) {
        assert!(!self.nodes.is_empty());
        let node_idx = self.nodes.len() - 1;
        assert!(self.nodes[node_idx].parent.is_none());
        debug_assert!(self
            .nodes
            .iter()
            .take(self.nodes.len() - 1)
            .all(|n| n.parent.is_some()));

        assert!(self.bound <= bound); // cannot decrease bound.
        self.bound = bound;
        self.increase_node_bound_topdown(s, node_idx);
    }

    pub fn add_literal(&mut self, s: &mut impl SatInstance<L>, node: usize) -> Bool<L> {
        // This is one of the original unary numbers.
        assert!(node < self.original_n_nodes);
        // This is a leaf node.
        assert!(self.nodes[node].left.is_none());
        assert!(self.nodes[node].right.is_none());

        let lit = self.nodes[node].number.extend(s);
        self.increase_node_bound_bottomup(s, node);
        lit
    }

    fn increase_node_bound_topdown(&mut self, s: &mut impl SatInstance<L>, node: usize) {
        if !self.leaf_node(node) {
            self.increase_node_bound_topdown(s, self.nodes[node].left.unwrap());
            self.increase_node_bound_topdown(s, self.nodes[node].right.unwrap());
        }
        let _new_constraint = self.add_node_constraints(s, node);
    }

    fn increase_node_bound_bottomup(&mut self, s: &mut impl SatInstance<L>, node: usize) {
        println!(
            "Node={} parent={:?} left={:?} right={:?}",
            node, self.nodes[node].parent, self.nodes[node].left, self.nodes[node].right
        );

        self.nodes[node].total_lits += 1;
        let _new_constraints = self.add_node_constraints(s, node);

        if !self.root_node(node) {
            self.increase_node_bound_bottomup(s, self.nodes[node].parent.unwrap());
        }
    }

    fn leaf_node(&self, node: usize) -> bool {
        let has_left = self.nodes[node].left.is_some();
        let has_right = self.nodes[node].left.is_some();
        assert!(has_left == has_right);
        !has_left
    }

    fn root_node(&self, node: usize) -> bool {
        self.nodes[node].parent.is_none()
    }

    fn add_node_constraints(&mut self, s: &mut impl SatInstance<L>, node: usize) {
        let node_bound = self.bound.min(self.nodes[node].total_lits);
        println!("node {} node_bound {:?}", node, node_bound);

        if self.leaf_node(node) {
            assert!(self.nodes[node].number.bound() >= node_bound);
            return;
        }

        while self.nodes[node].number.bound() < node_bound {
            self.nodes[node].number.extend(s);
            println!(
                "Extending node{} bound{}",
                node,
                self.nodes[node].number.bound()
            );
        }

        let left_idx = self.nodes[node].left.unwrap();
        let right_idx = self.nodes[node].right.unwrap();

        let old_left_bound = self.nodes[node].left_constraints;
        let old_right_bound = self.nodes[node].right_constraints;
        let old_bound = self.nodes[node].this_constraints;
        let new_left_bound = self.nodes[left_idx].number.bound();
        let new_right_bound = self.nodes[right_idx].number.bound();

        // let mut new_constraints = false;

        for i in 0..=new_left_bound {
            for j in 0..=new_right_bound {
                let k = i + j;

                if k > node_bound {
                    continue;
                }

                if i <= old_left_bound && j <= old_right_bound && k <= old_bound {
                    continue;
                }

                eprintln!(
                    "adding node={} ({},{},{}) {}/{}/{}",
                    node,
                    i,
                    j,
                    k,
                    self.nodes[left_idx].number.bound(),
                    self.nodes[right_idx].number.bound(),
                    self.nodes[node].number.bound()
                );

                println!("left gte i{} = {:?}", i, self.nodes[left_idx].number.gte_const(i as isize).constant());
                println!("left lte i{} = {:?}", i, self.nodes[left_idx].number.lte_const(i as isize).constant());
                println!("rhgt gte j{} = {:?}", j,self.nodes[right_idx].number.gte_const(j as isize).constant());
                println!("rhgt lte j{} = {:?}", j,self.nodes[right_idx].number.lte_const(j as isize).constant());
                println!("node gte k{} = {:?}", k,self.nodes[node].number.gte_const(k as isize).constant());
                // println!("node lte k{} = {:?}", k,self.nodes[node].number.lte_const(k as isize).constant());

                s.add_clause(vec![
                    !self.nodes[left_idx].number.gte_const(i as isize),
                    !self.nodes[right_idx].number.gte_const(j as isize),
                    self.nodes[node].number.gte_const(k as isize),
                ]);


                if j > 0 {
                assert!(self.nodes[left_idx].number.lte_const(i as isize).constant() != Some(true));

                s.add_clause(vec![
                    !self.nodes[left_idx].number.lte_const(i as isize),
                    self.nodes[right_idx].number.gte_const(j as isize),
                    !self.nodes[node].number.gte_const(k as isize),
                ]);
            }

                //  l+r >= i+j && r <= j  =>  l >= i
                //  l + r >= 1 + 1 && r <= 1  => l >= 1

                if i > 0 {
                assert!(self.nodes[right_idx].number.lte_const(j as isize).constant() != Some(true));

                s.add_clause(vec![
                    self.nodes[left_idx].number.gte_const(i as isize),
                    !self.nodes[right_idx].number.lte_const(j as isize),
                    !self.nodes[node].number.gte_const(k as isize),
                ]);
            }

                // new_constraints = true;
            }
        }

        println!("Extended node={}  lc{} rc{} tc{}  ->  lc{} rc{} tc{}",
        node, old_left_bound, old_right_bound, old_bound, new_left_bound, new_right_bound, node_bound);

        self.nodes[node].left_constraints = new_left_bound;
        self.nodes[node].right_constraints = new_right_bound;
        self.nodes[node].this_constraints = node_bound;

        // assert!(
        //     new_constraints
        //         == (old_left_bound != new_left_bound
        //             || old_right_bound != new_right_bound
        //             || old_bound != node_bound)
        // );

        // new_constraints
    }
}

#[cfg(test)]
mod tests {
    use crate::{prelude::SymbolicModel, solvers};

    use super::*;

    #[test]
    pub fn test_eqtot_1() {
        let mut s = solvers::minisat::Solver::new();
        let u1 = Unary::new(&mut s, 2);
        let u2 = Unary::new(&mut s, 2);
        let u3 = Unary::new(&mut s, 2);

        let mut eqt = EqTotalizer::new(vec![u1, u2, u3]);

        eqt.increase_bound(&mut s, 6);
        println!("add_literal");
        eqt.add_literal(&mut s, 1);
        eqt.add_literal(&mut s, 2);
        eqt.add_literal(&mut s, 2);
        println!("bound6");

        eqt.increase_bound(&mut s, 7);

        SatInstance::add_clause(&mut s, vec![eqt.number().gte_const(6)]);
        SatInstance::add_clause(&mut s, vec![eqt.input_number(2).lte_const(1)]);

        println!("model {:?}", s);
        let m = s.solve().unwrap();
        dbg!(m.value(eqt.input_number(0)));
        dbg!(m.value(eqt.input_number(1)));
        dbg!(m.value(eqt.input_number(2)));
        dbg!(m.value(eqt.number()));
    }

    #[test]
    pub fn test_eqtot_2() {
        let mut s = solvers::minisat::Solver::new();
        let u1 = Unary::new(&mut s, 2);
        let u2 = Unary::new(&mut s, 2);
        let u3 = Unary::new(&mut s, 2);
        // let u2 = Unary::new(&mut s, 0);

        let mut eqt = EqTotalizer::new(vec![u1, u2, u3]);
        eqt.increase_bound(&mut s, 7);
        eqt.add_literal(&mut s, 1);
        eqt.add_literal(&mut s, 2);
        eqt.add_literal(&mut s, 2);
        
        SatInstance::add_clause(&mut s, vec![eqt.number().gte_const(7)]);
        SatInstance::add_clause(&mut s, vec![eqt.input_number(2).lte_const(2)]);


        println!("model {:?}", s);
        let m = s.solve().unwrap();
        dbg!(m.value(eqt.input_number(0)));
        dbg!(m.value(eqt.input_number(1)));
        dbg!(m.value(eqt.input_number(2)));
        dbg!(m.value(eqt.number()));
    }

    #[test]
    pub fn test_eqtot_3() {
        let mut s = solvers::minisat::Solver::new();
        let u1 = Unary::new(&mut s, 1);
        let u2 = Unary::new(&mut s, 1);
        let u3 = Unary::new(&mut s, 1);
        // let u2 = Unary::new(&mut s, 0);

        let mut eqt = EqTotalizer::new(vec![u1, u2, u3]);
        eqt.increase_bound(&mut s, 2);

        println!("model {:?}", s);
        let m = s.solve().unwrap();
        dbg!(m.value(eqt.input_number(0)));
        dbg!(m.value(eqt.input_number(1)));
        dbg!(m.value(eqt.input_number(2)));
        dbg!(m.value(eqt.number()));
    }
}
