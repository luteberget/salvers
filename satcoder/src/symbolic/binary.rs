use crate::{constraints::*, symbolic::*, *};
use std::iter::once;

#[derive(Debug,Clone)]
pub struct Binary<L:Lit>(Vec<Bool<L>>);

impl<L:Lit + 'static> Binary<L> {
    pub fn new(solver: &mut impl SatInstance<L>, size: usize) -> Binary<L> {
        let (mut bits, mut n) = (0, size);
        while n > 0 {
            bits += 1;
            n /= 2;
        }
        let lits = (0..bits).map(|_| solver.new_var()).collect::<Vec<_>>();
        Binary(lits)
    }

    pub fn into_list(self) -> Vec<Bool<L>> { self.0 }

    pub fn constant(x: usize) -> Binary<L> {
        let mut v = Vec::new();
        let mut i = x;
        while i > 0 {
            v.push(if i % 2 == 1 {
                true.into()
            } else {
                false.into()
            });
            i /= 2;
        }
        Binary(v)
    }

    pub fn invert(&self) -> Binary<L> {
        Binary(self.0.iter().cloned().map(|x| !x).collect())
    }

    pub fn from_list<I: IntoIterator<Item = Bool<L>>>(xs: I) -> Binary<L> {
        Binary(xs.into_iter().collect())
    }

    pub fn count(&self, solver: &mut impl SatInstance<L>) -> Binary<L> {
        let bins = self.0
            .iter()
            .cloned()
            .map(|d| Binary::from_list(once(d)))
            .collect::<Vec<_>>();
        Binary::add_list(solver, bins.iter())
    }

    pub fn add(&self, solver: &mut impl SatInstance<L>, other: &Binary<L>) -> Binary<L> {
        Binary::add_list(solver, once(self).chain(once(other)))
    }

    pub fn add_list<'a, I: IntoIterator<Item = &'a Binary<L>>>(solver: &mut impl SatInstance<L>, xs: I) -> Binary<L> {
        Binary::add_bits(solver,
                         xs.into_iter()
                             .flat_map(|x| {
                                 x.0
                                     .iter()
                                     .cloned()
                                     .enumerate()
                             })
                             .collect())
    }

    pub fn add_bits(solver: &mut impl SatInstance<L>, xs: Vec<(usize, Bool<L>)>) -> Binary<L> {
        #[derive(Debug)]
        struct Item<L:Lit> {
            bit: usize,
            val: Bool<L>,
        }
        let mut xs = xs.into_iter()
            .map(|(bit, val)| {
                Item {
                    bit: bit,
                    val: val,
                }
            })
            .collect::<Vec<_>>();
        xs.sort_by_key(|&Item { bit, .. }| bit);
        let mut out = Vec::new();
        let mut i = 0;

        while xs.len() > 0 {
            if i < xs[0].bit {
                out.push(false.into());
                i = i + 1;
            } else if xs.len() >= 3 && xs[0].bit == xs[1].bit && xs[1].bit == xs[2].bit {
                let Item { bit, val: a_val } = xs.remove(0);
                let Item { bit: _, val: b_val } = xs.remove(0);
                let Item { bit: _, val: c_val } = xs.remove(0);
                let (v, c) = Binary::full_add(solver, a_val, b_val, c_val);
                xs.push(Item { bit: bit, val: v });
                xs.push(Item {
                    bit: bit + 1,
                    val: c,
                });
                xs.sort_by_key(|&Item { bit, .. }| bit);
                i = bit;
            } else if xs.len() >= 2 && xs[0].bit == xs[1].bit {
                let Item { bit, val: a_val } = xs.remove(0);
                let Item { bit: _, val: b_val } = xs.remove(0);
                let (v, c) = Binary::full_add(solver, a_val, b_val, false.into());
                out.push(v);
                xs.push(Item {
                    bit: bit + 1,
                    val: c,
                });
                xs.sort_by_key(|&Item { bit, .. }| bit);
                i = bit + 1;
            } else {
                let Item { bit, val } = xs.remove(0);
                out.push(val);
                i = bit + 1;
            }
        }

        Binary(out)
    }

    fn full_add(solver: &mut impl SatInstance<L>, a: Bool<L>, b: Bool<L>, c: Bool<L>) -> (Bool<L>, Bool<L>) {
        let v = solver.xor_literal(once(a).chain(once(b)).chain(once(c)));
        let c = Binary::at_least_two(solver, a, b, c);
        (v, c)
    }

    #[allow(clippy::if_same_then_else)]
    fn at_least_two(solver: &mut impl SatInstance<L>, a: Bool<L>, b: Bool<L>, c: Bool<L>) -> Bool<L> {
        if a == true.into() {
            solver.or_literal(once(b).chain(once(c)))
        } else if b == true.into() {
            solver.or_literal(once(a).chain(once(c)))
        } else if c == true.into() {
            solver.or_literal(once(a).chain(once(b)))
        } else if a == false.into() {
            solver.and_literal(once(b).chain(once(c)))
        } else if b == false.into() {
            solver.and_literal(once(a).chain(once(c)))
        } else if c == false.into() {
            solver.and_literal(once(a).chain(once(b)))
        } else if a == b {
            a
        } else if b == c {
            b
        } else if a == c {
            c
        } else if a == !b {
            c
        } else if b == !c {
            a
        } else if a == !c {
            b
        } else {
            let v = solver.new_var();
            solver.add_clause(once(!a).chain(once(!b)).chain(once(v)));
            solver.add_clause(once(!a).chain(once(!c)).chain(once(v)));
            solver.add_clause(once(!b).chain(once(!c)).chain(once(v)));
            solver.add_clause(once(a).chain(once(b)).chain(once(!v)));
            solver.add_clause(once(a).chain(once(c)).chain(once(!v)));
            solver.add_clause(once(b).chain(once(c)).chain(once(!v)));
            v
        }
    }

    pub fn bound(&self) -> usize {
        (2 as usize).pow(self.0.len() as u32) - 1
    }

    pub fn mul_digit(&self, solver: &mut impl SatInstance<L>, y: Bool<L>) -> Binary<L> {
        Binary(self.0.iter().cloned().map(|x| solver.and_literal(once(x).chain(once(y)))).collect())
    }

    pub fn mul(&self, solver: &mut impl SatInstance<L>, other: &Binary<L>) -> Binary<L> {
        let mut out = Vec::new();
        for (i, x) in self.0.iter().cloned().enumerate() {
            for (j, y) in other.0.iter().cloned().enumerate() {
                let z = solver.and_literal(once(x).chain(once(y)));
                out.push(((i + j), z));
            }
        }

        Binary::add_bits(solver, out)
    }
    
    pub fn assert_lt(solver: &mut impl SatInstance<L>,
                      //prefix: Vec<Bool<L>>,
                      a: &Binary<L>,
                      b: &Binary<L>) {
        use std::iter::repeat;
        let len = a.0.len().max(b.0.len());
        let mut a_bits = a.0
            .iter()
            .cloned()
            .chain(repeat(false.into()))
            .take(len)
            .collect::<Vec<_>>();
        a_bits.reverse();
        let mut b_bits = b.0
            .iter()
            .cloned()
            .chain(repeat(false.into()))
            .take(len)
            .collect::<Vec<_>>();
        b_bits.reverse();

        let lt = lt_literal(solver, &a_bits, &b_bits);
        solver.add_clause(vec![lt]);
    }
}

fn lt_literal<L:Lit>(solver :&mut impl SatInstance<L>, //prefix :Vec<Bool<L>>, 
                         a :&[Bool<L>], b :&[Bool<L>]) -> Bool<L> {
    assert!(a.len() == b.len());
    let n = a.len();

    if n == 1 {
        return solver.and_literal(vec![!a[0], b[0]]);
    }

    let rest = lt_literal(solver, &a[1..], &b[1..]);
    let lt_lit = solver.new_var();

    solver.add_clause(vec![!lt_lit, b[0], rest]);
    solver.add_clause(vec![!lt_lit, !a[0], rest]);
    solver.add_clause(vec![!lt_lit, !a[0], b[0]]);

    return lt_lit;
}

impl<L :Lit> Symbolic<'_, L> for Binary<L> {
    type T = usize;

    fn interpret(&self, m :&dyn SatModel<Lit =L>) -> Self::T {
        self.0
            .iter()
            .enumerate()
            .map(|(i, x)| if m.value(x) {
                (2 as usize).pow(i as u32)
            } else {
                0
            })
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn test_binary_lt_const() {
        let mut solver = crate::solvers::minisat::Solver::new();
        let bin = Binary::new(&mut solver, 1000);
        Binary::assert_lt(&mut solver, &Binary::constant(500), &bin);
        Binary::assert_lt(&mut solver, &bin, &Binary::constant(525));
        let model = solver.solve().unwrap();

        let value = model.value(&bin);
        println!("value = {:?}", value);
        assert!(value >= 500 && value <= 525);
    }

    #[test]
    pub fn test_binary_unsat() {
        let mut solver = crate::solvers::minisat::Solver::new();
        let bin = Binary::new(&mut solver, 1000);
        Binary::assert_lt(&mut solver, &Binary::constant(500), &bin);
        Binary::assert_lt(&mut solver, &bin, &Binary::constant(499));
        assert!(solver.solve().is_err());
    }
}

//impl<'a> ModelValue<'a> for Binary<L> {
//    type T = usize;
//    fn value(&self, m: &Model) -> usize {
//        self.0
//            .iter()
//            .enumerate()
//            .map(|(i, x)| if m.value(x) {
//                (2 as usize).pow(i as u32)
//            } else {
//                0
//            })
//            .sum()
//    }
//}


//impl ModelOrd for Binary<L> {
//    fn assert_less_or(solver: &mut impl SatInstance<L>,
//                      prefix: Vec<Bool<L>>,
//                      inclusive: bool,
//                      a: &Binary<L>,
//                      b: &Binary<L>) {
//        use std::iter::repeat;
//        let len = a.0.len().max(b.0.len());
//        let mut a_bits = a.0
//            .iter()
//            .cloned()
//            .chain(repeat(false.into()))
//            .take(len)
//            .collect::<Vec<_>>();
//        a_bits.reverse();
//        let mut b_bits = b.0
//            .iter()
//            .cloned()
//            .chain(repeat(false.into()))
//            .take(len)
//            .collect::<Vec<_>>();
//        b_bits.reverse();
//        <&[Bool<L>]>::assert_less_or(solver,
//                                  prefix,
//                                  inclusive,
//                                  &&a_bits.as_slice(),
//                                  &&b_bits.as_slice());
//    }
//}



//impl ModelEq for Binary<L> {
//    fn assert_equal_or(solver: &mut impl SatInstance<L>, prefix: Vec<Bool<L>>, a: &Binary<L>, b: &Binary<L>) {
//        let mut i = 0;
//        while i < a.0.len() || i < b.0.len() {
//            Bool<L>::assert_equal_or(solver,
//                                  prefix.clone(),
//                                  a.0.get(i).unwrap_or(&false.into()),
//                                  b.0.get(i).unwrap_or(&false.into()));
//            i += 1;
//        }
//    }
//
//    fn assert_not_equal_or(solver: &mut impl SatInstance<L>, mut prefix: Vec<Bool<L>>, a: &Binary<L>, b: &Binary<L>) {
//        let mut i = 0;
//        let mut q = solver.new_var();
//        prefix.push(q);
//
//        while i < a.0.len() || i < b.0.len() {
//            let ai = a.0.get(i).cloned().unwrap_or(false.into());
//            let bi = b.0.get(i).cloned().unwrap_or(false.into());
//
//            Bool<L>::assert_not_equal_or(solver, prefix.clone(), &ai, &bi);
//            prefix.clear();
//            prefix.push(!q);
//
//            q = solver.new_var();
//            i += 1;
//        }
//        solver.add_clause(prefix);
//    }
//}
