use std::collections::HashMap;

use crate::{prelude::Unary, Bool, Lit, SatInstance};
use itertools::Itertools;

#[derive(Debug)]
pub struct LinearConstraintLte<L: Lit> {
    pub terms: Vec<(i32, Unary<L>)>,
    pub rhs: i32,
}

#[derive(Clone, Copy, Debug)]
struct Interval(i32, i32);

impl Interval {
    pub fn intersect(&self, b: &Self) -> Self {
        Interval(self.0.max(b.0), self.1.min(b.1))
    }

    pub fn add_const(&self, x: i32) -> Self {
        Interval(self.0.saturating_add(x), self.1.saturating_add(x))
    }

    pub fn contains(&self, x: i32) -> bool {
        self.0 <= x && x <= self.1
    }

    pub fn is_empty(&self) -> bool {
        self.0 > self.1
    }
}

type NodeRef = usize;

#[derive(Debug)]
struct Mdd<L: Lit> {
    levels: Vec<Vec<NodeRef>>,
    nodes: Vec<(Interval, Option<Bool<L>>, usize)>,
    edges: Vec<Vec<(i32, NodeRef)>>,
}

pub fn group_coeffs<L: Lit + std::fmt::Debug>(
    sat: &mut impl SatInstance<L>,
    constraint: LinearConstraintLte<L>,
) -> LinearConstraintLte<L> {
    let mut groups: HashMap<i32, Vec<&Unary<L>>> = HashMap::new();
    for (coeff, unary) in constraint.terms.iter() {
        groups.entry(*coeff).or_default().push(unary);
    }

    if groups.iter().map(|(c, us)| us.len()).max().unwrap() < 10 {
        return constraint;
    }

    // println!("reducing {:?}", constraint);
    let terms = groups
        .into_iter()
        .map(|(coeff, unaries)| {
            if unaries.len() == 1 {
                return (coeff, unaries[0].clone());
            }

            let sum_bounds = unaries.iter().map(|x| x.bound() as i32).sum::<i32>();
            let bound = sum_bounds.min(constraint.rhs / coeff);

            (
                coeff,
                Unary::sum_truncate(sat, unaries.into_iter().cloned().collect(), bound as usize),
            )
        })
        .collect();

    LinearConstraintLte {
        terms,
        rhs: constraint.rhs,
    }
}

pub fn make_lhs_positive<L: Lit>(constraint: &LinearConstraintLte<L>) -> LinearConstraintLte<L> {
    let mut rhs = constraint.rhs;
    let terms = constraint
        .terms
        .iter()
        .map(|(coeff, x)| {
            assert!(*coeff != 0);
            if *coeff < 0 {
                rhs -= *coeff * (x.bound() as i32);
                (-*coeff, x.invert())
            } else {
                (*coeff, x.clone())
            }
        })
        .collect();
    // println!("rhs changed from {} to {} ", constraint.rhs, rhs);
    LinearConstraintLte { terms, rhs }
}

pub fn mdd_size<L: Lit + std::fmt::Debug>(constraint: &LinearConstraintLte<L>) -> usize {
    let mut mdd = initial_mdd(constraint);
    if mdd_construct(&mut mdd, constraint, false).is_none() {
        return MAX_MDD_SIZE;
    }

    mdd.edges.iter().map(|e| e.len()).sum()
}

pub fn mdd_linear_constraint<L: Lit + std::fmt::Debug>(
    sat: &mut impl SatInstance<L>,
    constraint: &LinearConstraintLte<L>,
    // debug: bool,
) -> bool {
    let debug = false;
    // println!("mdd_linear_constraint {:?}", constraint);
    // let is_positive = constraint.terms.iter().all(|(c, _)| *c >= 0);
    // let constraint = group_coeffs(sat, make_lhs_positive(constraint));
    let constraint = make_lhs_positive(constraint);
    // if (!is_positive) {
    // println!("translated linear constraint to positive {:?}", constraint);
    // }

    let mut mdd = initial_mdd(&constraint);

    const USE_RECURSIVE: bool = false;

    if USE_RECURSIVE {
        mdd_construct_recursive(&mut mdd, sat, 0, &constraint.terms, constraint.rhs);
    } else {
        if debug {
            println!("constructing non-recusrively");
        }
        if mdd_construct(&mut mdd, &constraint, debug).is_none() {
            return false;
        }
    }
    if debug {
        println!("encoding to sat");
    }
    assert!(mdd.levels[0].len() == 1);

    for node_idx in 0..mdd.nodes.len() {
        if mdd.edges[node_idx].is_empty() {
            assert!(mdd.nodes[node_idx].1.unwrap().lit().is_none());
        } else if mdd.edges[node_idx].len() == 1 && mdd.levels[0][0] != node_idx {
            // Redundant node
            // println!("Redundant node {}", node_idx);
        } else {
            if mdd.nodes[node_idx].1.is_none() {
                mdd.nodes[node_idx].1 = Some(sat.new_var());
            }

            let node_var = mdd.nodes[node_idx].1.unwrap();
            let term_idx = mdd.nodes[node_idx].2;

            for (bound, mut child_node) in mdd.edges[node_idx].iter() {
                while mdd.edges[child_node].len() == 1 {
                    // TODO check that bound is equal to the variable's upper bound?
                    // assert!({
                    //     let child_var =
                    //     let child_bound = mdd.edges[child_node][0].0;
                    // });
                    child_node = mdd.edges[child_node][0].1;
                }

                // if mdd.nodes[child_node].1.is_none() {
                //     mdd.nodes[child_node].1 = Some(sat.new_var());
                // }

                assert!(mdd.nodes[child_node].1.is_some());

                sat.add_clause(vec![
                    !node_var,
                    !constraint.terms[term_idx].1.gte_const(*bound as isize),
                    mdd.nodes[child_node].1.unwrap(),
                ]);
            }
        }
    }
    // println!(
    //     "MDD {:?}\n    {:?}\n    {:?}",
    //     mdd.levels, mdd.nodes, mdd.edges
    // );

    true
}

fn initial_mdd<L: Lit>(constraint: &LinearConstraintLte<L>) -> Mdd<L> {
    let mut levels = (0..constraint.terms.len())
        .map(|_| vec![])
        .collect::<Vec<_>>();
    let last_level = levels.len();
    levels.push(vec![0, 1]);
    let node_vars = vec![
        (Interval(i32::MIN, -1), Some(false.into()), last_level),
        (Interval(0, i32::MAX), Some(true.into()), last_level),
    ];
    let mut mdd = Mdd {
        levels,
        nodes: node_vars,
        edges: vec![vec![], vec![]],
    };
    mdd
}

const MAX_MDD_SIZE: usize = 100000;

fn mdd_construct<L: Lit + std::fmt::Debug>(
    mdd: &mut Mdd<L>,
    constraint: &LinearConstraintLte<L>,
    debug: bool,
) -> Option<NodeRef> {
    let mut total_size = 0;

    #[derive(Debug)]
    struct StackEntry {
        level: usize,
        rhs: i32,
        next_value: i32,
        children: Vec<(i32, usize)>,
        interval: Interval,
    }
    let mut stack = vec![StackEntry {
        level: 0,
        rhs: constraint.rhs,
        next_value: 0,
        children: Vec::new(),
        interval: Interval(i32::MIN, i32::MAX),
    }];

    'stack: while let Some(StackEntry {
        level,
        rhs,
        next_value,
        children,
        interval,
    }) = stack.last_mut()
    {
        if debug {
            println!(
                "level {}, rhs {} next_value {}, interval {:?}",
                level, rhs, next_value, interval
            );
        }
        let domain = 0..=(constraint.terms[*level].1.bound() as i32);
        let coeff = constraint.terms[*level].0;

        while domain.contains(next_value) {
            let child_rhs = *rhs - *next_value * coeff;
            if let Some(existing) = mdd.levels[*level + 1]
                .iter()
                .find(|n| mdd.nodes[**n].0.contains(child_rhs))
            {
                // there was such an interval already, just push it to the children
                // println!("   foudn value {} in existing noe {} interval {:?}", next_value, existing, &mdd.nodes[*existing].0);
                children.push((*next_value, *existing));
                total_size += 1;
                if total_size > MAX_MDD_SIZE {
                    return None;
                }
                // println!("   size {}", total_size);
                // TODO calculate the jump directly
                while domain.contains(next_value)
                    && mdd.nodes[*existing].0.contains(*rhs - *next_value * coeff)
                {
                    *interval = interval
                        .intersect(&mdd.nodes[*existing].0.add_const(coeff * (*next_value)));
                    // println!("   this interval {:?}", interval);

                    *next_value += 1;
                }
            } else {
                // // We need to push to the stack and come back later
                // stack.push(StackEntry {
                //     level, rhs, next_value, children
                // });
                // Create a new interval on the lower level
                let level = *level + 1;
                stack.push(StackEntry {
                    level,
                    rhs: child_rhs,
                    next_value: 0,
                    children: Vec::new(),
                    interval: Interval(i32::MIN, i32::MAX),
                });
                // println!("Stack {:?}", stack);

                continue 'stack;
            }
        }
        let new_node = mdd.nodes.len();
        let var = if *level == 0 { Some(true.into()) } else { None };

        // println!(
        //     "  node  {} interval {:?} level {}",
        //     new_node, interval, level
        // );
        mdd.nodes.push((*interval, var, *level));

        let mut new_edges: Vec<(i32, usize)> = Vec::new();
        for (value, node) in children.iter() {
            if let Some((_, prev_node)) = new_edges.last_mut() {
                if prev_node == node {
                    continue;
                }
            }
            new_edges.push((*value, *node));
        }

        // println!(
        //     "insert node at level {} rhs {} interval {:?} edges {:?}",
        //     level, rhs, interval, new_edges
        // );

        mdd.edges.push(new_edges);

        debug_assert!(mdd.nodes.len() == mdd.edges.len());
        debug_assert!(mdd.levels[*level]
            .iter()
            .all(|i| interval.intersect(&mdd.nodes[*i].0).is_empty()));

        let level_idx = mdd.levels[*level].partition_point(|i| mdd.nodes[*i].0 .0 <= interval.0);
        mdd.levels[*level].insert(level_idx, new_node);

        stack.pop();
        // println!("Stack {:?}", stack);
    }

    Some(mdd.levels[0][0])
}

fn mdd_construct_recursive<L: Lit + std::fmt::Debug>(
    mdd: &mut Mdd<L>,
    sat: &mut impl SatInstance<L>,
    level: usize,
    terms: &[(i32, Unary<L>)],
    rhs: i32,
) -> NodeRef {
    if let Some(existing) = mdd.levels[level]
        .iter()
        .find(|n| mdd.nodes[**n].0.contains(rhs))
    {
        return *existing;
    }

    debug_assert!(!terms.is_empty());
    // let mut prefix = String::new();
    // for _ in 0..level {
    //     prefix.push_str("  ");
    // }
    // println!("{}level {}", prefix, level);

    let domain = 0..=(terms[0].1.bound() as i32);
    let coeff = terms[0].0;
    let children = domain
        .map(|j| {
            // println!("{}value={}", prefix, j);
            (
                j,
                mdd_construct_recursive(mdd, sat, level + 1, &terms[1..], rhs - j as i32 * coeff),
            )
        })
        .collect::<Vec<_>>();

    // println!("{}Chidlren {:?}", prefix, children);

    let new_node = mdd.nodes.len();
    let var = if level == 0 { Some(true.into()) } else { None };

    let interval = children
        .iter()
        .map(|(val, node)| mdd.nodes[*node].0.add_const(coeff * (*val)))
        .fold1(|a, b| a.intersect(&b))
        .unwrap();

    // println!("  node {} level {} interval {:?}", new_node, level, interval);
    mdd.nodes.push((interval, var, level));

    let mut new_edges: Vec<(i32, usize)> = Vec::new();
    for (value, node) in children.iter() {
        if let Some((_, prev_node)) = new_edges.last_mut() {
            if prev_node == node {
                continue;
            }
        }
        new_edges.push((*value, *node));
    }

    // println!(
    //     "insert node at level {} rhs {} interval {:?} edges {:?}",
    //     level, rhs, interval, new_edges
    // );

    mdd.edges.push(new_edges);

    debug_assert!(mdd.nodes.len() == mdd.edges.len());
    debug_assert!(mdd.levels[level]
        .iter()
        .all(|i| interval.intersect(&mdd.nodes[*i].0).is_empty()));

    let level_idx = mdd.levels[level].partition_point(|i| mdd.nodes[*i].0 .0 <= interval.0);
    mdd.levels[level].insert(level_idx, new_node);

    // println!("updated mdd {:?}", mdd);
    new_node
}

#[cfg(test)]
mod tests {
    use crate::{constraints::mddlinear, dimacsoutput::DimacsOutput, solvers::minisat};

    use super::*;
    use crate::symbolic::SymbolicModel;

    #[test]
    pub fn mdd_coeffs() {
        let mut solver = minisat::Solver::new();

        let x = Unary::new(&mut solver, 1);
        let y = Unary::new(&mut solver, 2);
        mdd_linear_constraint(
            &mut solver,
            &LinearConstraintLte {
                terms: vec![(1, x.clone()), (1, y.clone())],
                rhs: 0,
            },
        );
        SatInstance::add_clause(&mut solver, vec![y.gte_const(1)]);
        assert!(solver.solve().is_err());
    }

    #[test]
    pub fn mdd_coeffs_eq() {
        let mut solver = minisat::Solver::new();

        let x = Unary::new(&mut solver, 1);
        let y = Unary::new(&mut solver, 10);
        let z = Unary::new(&mut solver, 10);

        mdd_linear_constraint(
            &mut solver,
            &LinearConstraintLte {
                terms: vec![(1, x.clone()), (1, y.clone()), (1, z.clone())],
                rhs: 10,
            },
        );

        mdd_linear_constraint(
            &mut solver,
            &LinearConstraintLte {
                terms: vec![(-1, x.clone()), (-1, y.clone()), (-1, z.clone())],
                rhs: -10,
            },
        );

        SatInstance::add_clause(&mut solver, vec![y.gte_const(4)]);
        SatInstance::add_clause(&mut solver, vec![z.gte_const(4)]);

        let model = solver.solve().unwrap();
        println!(
            "x={} y={} z={}",
            model.value(&x),
            model.value(&y),
            model.value(&z)
        );
        assert!(model.value(&x) + model.value(&y) + model.value(&z) == 10);
    }

    #[test]
    pub fn testmddclause() {
        let mut out = DimacsOutput::new();

        // Create three binary variables
        let x = Unary::new(&mut out, 1);
        let y = Unary::new(&mut out, 1);
        let z = Unary::new(&mut out, 1);

        // Create a linear constraint representation of a clause on these.
        let constraint = LinearConstraintLte {
            terms: vec![(-1, x), (-1, y), (-1, z)],
            rhs: -1,
        };

        mdd_linear_constraint(&mut out, &constraint);

        let mut dimacs = String::new();
        out.write(&mut dimacs);
        println!("{}", dimacs);
    }

    #[test]
    pub fn mdd_enc_size_clause() {
        for n in 1..100 {
            let mut out = DimacsOutput::new();

            let xs = (0..n).map(|_| Unary::new(&mut out, 1)).collect::<Vec<_>>();

            println!("vars {} clauses {}", out.num_vars(), out.num_clauses());

            // Clause  x1 v x2 v x3 v ..
            let constraint = LinearConstraintLte {
                terms: xs.iter().map(|v| (-1, v.clone())).collect(),
                rhs: -1,
            };

            mdd_linear_constraint(&mut out, &constraint);

            println!("vars {} clauses {}", out.num_vars(), out.num_clauses());
            let mut dimacs = String::new();
            out.write(&mut dimacs);
            // println!("{}", dimacs);
        }
    }
}
