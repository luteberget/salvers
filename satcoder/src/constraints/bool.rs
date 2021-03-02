use crate::*;
use std::iter::{empty, once};

pub trait BooleanFormulas<L: Lit> {
    fn and_literal(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>) -> Bool<L>;
    fn or_literal(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>) -> Bool<L>;
    fn xor_literal(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>) -> Bool<L>;
    fn implies_literal(&mut self, a: Bool<L>, b: Bool<L>) -> Bool<L>;
    fn eq_literal(&mut self, a: Bool<L>, b: Bool<L>) -> Bool<L>;

    fn assert_at_most_one(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>);
    fn assert_at_most_one_or(
        &mut self,
        prefix: &[Bool<L>],
        xs: impl IntoIterator<Item = impl Into<Bool<L>>>,
    );
    fn assert_exactly_one(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>);
    fn assert_parity(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>, c: bool);
    fn assert_parity_or(
        &mut self,
        prefix: impl IntoIterator<Item = impl Into<Bool<L>>>,
        xs: impl IntoIterator<Item = impl Into<Bool<L>>>,
        c: bool,
    );
}

impl<L: Lit, S: SatInstance<L>> BooleanFormulas<L> for S {
    fn and_literal(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>) -> Bool<L> {
        use std::collections::HashSet;
        let mut lits = Vec::new();
        let mut posneg = [HashSet::new(), HashSet::new()];
        for v in xs {
            match v.into() {
                Bool::Const(false) => return false.into(),
                Bool::Const(true) => {}
                Bool::Lit(l) => {
                    let (var, s) = l.into_var();
                    if posneg[s as usize].contains(&var) {
                        return false.into();
                    }
                    if posneg[(s as usize + 1) % 2].insert(var) {
                        lits.push(l);
                    }
                }
            }
        }

        if lits.len() == 0 {
            return true.into();
        }

        if lits.len() == 1 {
            return Bool::Lit(lits[0]);
        }

        let y = self.new_var();
        for x in &mut lits {
            self.add_clause(once(!y).chain(once(Bool::Lit(*x))));
        }
        let mut lits = lits.into_iter().map(|x| !Bool::Lit(x)).collect::<Vec<_>>();
        lits.push(y);
        self.add_clause(lits.into_iter());
        y
    }

    fn or_literal(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>) -> Bool<L> {
        !(self.and_literal(xs.into_iter().map(|l| !(l.into()))))
    }

    fn assert_at_most_one(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>) {
        self.assert_at_most_one_or(&[], xs);
    }

    fn assert_at_most_one_or(
        &mut self,
        prefix: &[Bool<L>],
        xs: impl IntoIterator<Item = impl Into<Bool<L>>>,
    ) {
        let xs = xs.into_iter().map(|l| l.into()).collect::<Vec<_>>();
        if xs.len() <= 5 {
            for i in 0..xs.len() {
                for j in (i + 1)..xs.len() {
                    self.add_clause(
                        once(!xs[i])
                            .chain(once(!xs[j]))
                            .chain(prefix.iter().copied()),
                    );
                }
            }
        } else {
            let x = self.new_var();
            let k = xs.len() / 2;
            self.assert_at_most_one(once(x).chain(xs.iter().take(k).cloned()));
            self.assert_at_most_one(once(!x).chain(xs.iter().skip(k).cloned()));
        }
    }

    fn assert_exactly_one(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>) {
        let xs = xs.into_iter().map(|x| x.into()).collect::<Vec<_>>();
        self.add_clause(xs.iter().copied());
        self.assert_at_most_one(xs.iter().copied());
    }

    fn implies_literal(&mut self, a: Bool<L>, b: Bool<L>) -> Bool<L> {
        self.or_literal(once(!a).chain(once(b)))
    }

    fn eq_literal(&mut self, a: Bool<L>, b: Bool<L>) -> Bool<L> {
        self.xor_literal(once(!a).chain(once(b)))
    }

    fn xor_literal(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>) -> Bool<L> {
        use std::collections::HashSet;
        let mut posneg = [HashSet::new(), HashSet::new()];
        let mut const_parity = false;
        for x in xs {
            match x.into() {
                Bool::Const(b) => const_parity ^= b,
                Bool::Lit(l) => {
                    let (var, s) = l.into_var();
                    let s = s as usize;
                    if !posneg[s].insert(var) {
                        posneg[s].remove(&var);
                    }

                    if posneg[s].contains(&var) && posneg[(s + 1) % 2].contains(&var) {
                        const_parity = !const_parity;
                        posneg[0].remove(&var);
                        posneg[1].remove(&var);
                    }
                }
            }
        }

        let out = posneg[0]
            .iter()
            .map(|x| Bool::Lit(Lit::from_var_sign(*x, false)))
            .chain(
                posneg[1]
                    .iter()
                    .map(|x| Bool::Lit(Lit::from_var_sign(*x, true))),
            )
            .collect::<Vec<_>>();
        if out.len() == 0 {
            const_parity.into()
        } else if out.len() == 1 {
            if const_parity {
                !out[0]
            } else {
                out[0]
            }
        } else {
            let y = self.new_var();
            self.assert_parity(once(y).chain(out.into_iter()), const_parity);
            y
        }
    }

    fn assert_parity(&mut self, xs: impl IntoIterator<Item = impl Into<Bool<L>>>, c: bool) {
        self.assert_parity_or(empty::<Bool<L>>(), xs, c)
    }

    fn assert_parity_or(
        &mut self,
        prefix: impl IntoIterator<Item = impl Into<Bool<L>>>,
        xs: impl IntoIterator<Item = impl Into<Bool<L>>>,
        c: bool,
    ) {
        let mut xs = xs.into_iter().map(|l| l.into()).collect::<Vec<_>>();
        let prefix = prefix.into_iter().map(|l| l.into()).collect::<Vec<_>>();
        if xs.len() == 0 {
            if c {
                self.add_clause(prefix);
            } // else nothing
        } else if xs.len() <= 5 {
            let x = xs.pop().unwrap();
            self.assert_parity_or(
                prefix.iter().cloned().chain(once(!x)),
                xs.iter().cloned(),
                !c,
            );
            self.assert_parity_or(prefix.iter().cloned().chain(once(x)), xs.iter().cloned(), c);
        } else {
            let x = self.new_var();
            let k = xs.len() / 2;
            self.assert_parity_or(
                prefix.iter().cloned(),
                xs.iter().cloned().take(k).chain(once(x)),
                c,
            );
            self.assert_parity_or(
                prefix.iter().cloned(),
                xs.iter()
                    .cloned()
                    .skip(k)
                    .chain(once(if c { !x } else { x })),
                c,
            );
        }
    }
}
