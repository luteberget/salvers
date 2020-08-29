use mysatsolver;

#[test]
fn splitting_propagation_unsat() {
    use mysatsolver::*;

    struct UnsatTheory {
        have_added: bool,
    }

    impl Theory for UnsatTheory {
        fn check(&mut self, _ch: Check, lits: &[Lit], buf: &mut Refinement) {
            assert!(!self.have_added);
            assert!(lits.len() == 0);
            let var = buf.new_var();
            buf.add_clause(vec![var]);
            buf.add_clause(vec![!var]);
            self.have_added = true;
        }
        fn explain(&mut self, _: Lit, _: u32, _: &mut Refinement) {
            panic!()
        }
        fn new_decision_level(&mut self) {}
        fn backtrack(&mut self, _: i32) {}
    }

    let mut s = DplltSolver::new(UnsatTheory { have_added: false });
    assert!(s.solve() == LBOOL_FALSE);
}

#[test]
fn splitting_decision_unsat() {
    use mysatsolver::*;

    struct UnsatTheory {
        have_added: bool,
    }

    impl Theory for UnsatTheory {
        fn check(&mut self, ch: Check, lits: &[Lit], buf: &mut Refinement) {
            eprintln!("{:?} {:?}", ch, lits);
            if !self.have_added {
	        self.have_added = true;
                let a = buf.new_var();
                let b = buf.new_var();
                let c = buf.new_var();
                buf.add_clause(vec![!a,!b,c]);
                buf.add_clause(vec![ a,!b,c]);
                buf.add_clause(vec![!a, b,c]);
                buf.add_clause(vec![ a, b,c]);
                buf.add_clause(vec![!a,!b,!c]);
                buf.add_clause(vec![ a,!b,!c]);
                buf.add_clause(vec![!a, b,!c]);
                buf.add_clause(vec![ a, b,!c]);
	    }
        }

        fn explain(&mut self, _: Lit, _: u32, _: &mut Refinement) {
            panic!()
        }

        fn new_decision_level(&mut self) {}
        fn backtrack(&mut self, _: i32) {}
    }

    let mut s = DplltSolver::new(UnsatTheory { have_added: false });
    assert!(s.solve() == LBOOL_FALSE);
}
