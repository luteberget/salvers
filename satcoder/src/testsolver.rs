#![allow(dead_code, unused_variables)]
use crate::*;

pub struct Test {}
impl Test {
    fn l(&mut self) -> TestLit {
        todo!()
    }
}
#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TestLit(isize);
impl std::ops::Not for TestLit {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(-self.0)
    }
}
impl Lit for TestLit {
    type Var = i32;

    fn into_var(self) -> (Self::Var, bool) {
        todo!()
    }

    fn from_var_sign(v :Self::Var, sign :bool) -> Self {
        todo!()
    }
}

impl SatInstance<TestLit> for Test {
    fn new_var(&mut self) -> Bool<TestLit> {
        let x: TestLit = self.l();
        Bool::from_lit(x)
    }

    fn add_clause<IL: Into<Bool<TestLit>>, I: IntoIterator<Item = IL>>(&mut self, clause: I) {
        todo!()
    }
}

pub struct TestModel<'a> {
    internal: &'a Test,
}

impl<'a> SatModel for TestModel<'a> {
    type L = TestLit;

    fn lit_value(&self, l: &Self::L) -> bool {
        todo!()
    }
}

impl SatSolver for Test {
    type Lit = TestLit;
    fn solve<'a>(&'a mut self) -> SatResult<'a, Self::Lit> {
        let model = Box::new(TestModel { internal: self });
        SatResult::Sat(model)
    }
}

fn test_solver() {
    let mut solver = Test {};
    let a = solver.new_var();
    let b = solver.new_var();
    let v = vec![a, b];
    let finset = FinSet::new(&mut solver, vec![9,8,7]);
    solver.assert_parity(vec![finset.has_value(&7)], false);
    solver.add_clause(v);
    if let SatResult::Sat(model) = solver.solve() {
        let v1 = model.value(&a);
        let v2 = model.value(&b);
        //let v2 = b.interpret(&*model);
        drop(model);
    };
    if let SatResult::Sat(model) = solver.solve() {
        let v1 = model.value(&a);
        let v2 = model.value(&b);
    };
}

