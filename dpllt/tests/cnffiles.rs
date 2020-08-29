use dpllt;

fn for_each_cnf_filename(mut f: impl FnMut(&str)) {
    use std::{fs, path};
    let mut d = path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/cnfs");
    for direntry in fs::read_dir(d).unwrap() {
        let path = direntry.unwrap().path();
        let s = path.to_str().unwrap();
        println!("Test file: {:?}", s);

        f(s);
    }
}

fn verify_model<T: dpllt::Theory>(solver: &mut dpllt::DplltSolver<T>) -> bool {
    if solver.solve().as_bool().unwrap() {
        // check that each clause is satisfied
        let model = solver
            .get_model()
            .unwrap()
            .iter()
            .map(|l| l.as_bool().unwrap())
            .collect::<Vec<bool>>();
        for c in solver.get_clauses() {
            if !c.iter().any(|l| {
                if l.sign() {
                    !model[l.var().idx()]
                } else {
                    model[l.var().idx()]
                }
            }) {
                println!("  clause not sat: {:?}", c);
                return false;
            }
        }
        println!(
            "  ok -- sat model, checked {} clauses against {} variables",
            solver.get_clauses().count(),
            solver.get_model().unwrap().len()
        );
        // TODO check clauses directly from original dimacs
    }
    true
}

#[test]
fn hidden_clause_propagated_using_theory() {
    use dpllt::*;
    use std::collections::HashSet;
    #[derive(Default)]
    struct HiddenClauseTheory {
        clauses: Vec<Vec<Lit>>,
        trail: Vec<Lit>,
        trail_lim: Vec<usize>,
        lits: HashSet<i32>,
        //print: bool,
        propagate_on_conflict: bool,
        check_only_relevant: bool,
        qhead: usize,
    }

    impl HiddenClauseTheory {
        pub fn add_clause(&mut self, lits: &[Lit]) {
            assert!(self.trail_lim.len() == 0); // add clauses on top-level
            self.clauses.push(lits.to_vec());
            self.qhead = 0; // check everything from the beginning
            self.lits = std::iter::empty().collect();
        }
    }

    impl Theory for HiddenClauseTheory {
        fn check(&mut self, check: Check, lits: &[Lit], r: &mut Refinement) {
            //println!("Check {:?} {:?} print={}, nc={}", check, lits,self.print,self.clauses.len());
            for l0 in lits {
                self.trail.push(*l0);
            }

            while self.qhead < self.trail.len() {
                let l0 = self.trail[self.qhead];
                self.qhead += 1;
                self.lits.insert(l0.0);

                // for every assigned lit, check every clause.
                for (rref, c) in self.clauses.iter().enumerate() {
                    let is_relevant = c.iter().any(|l| *l == l0 || l.inverse() == l0);

                    //if self.print { println!(" relevant={} for {:?} in  {:?}", is_relevant, l0, c); }
                    if self.check_only_relevant && !is_relevant {
                        continue;
                    }
                    let is_unsat = c.iter().all(|l| self.lits.contains(&l.inverse().0));
                    let is_sat = c.iter().any(|l| self.lits.contains(&l.0));
                    if is_unsat {
                        // need to add either a conflicting assignment by propagation...
                        if self.propagate_on_conflict {
                            let unsat_lit = c[0];
                            //println!("  !! confl add_deduced({:?},{})", unsat_lit.inverse(), rref as u32);
                            r.add_deduced(unsat_lit, rref as u32);
                        } else {
                            // ... or just give the clause directly
                            //println!("  !! confl add_clause({:?})", c);
                            r.add_clause(c.iter().cloned());
                        }
                    } else {
                        if !is_sat {
                            let unassigned_lits = c
                                .iter()
                                .cloned()
                                .filter(|l| {
                                    !self.lits.contains(&l.0) && !self.lits.contains(&l.inverse().0)
                                })
                                .collect::<Vec<_>>();
                            if unassigned_lits.len() == 1 {
                                // There is exactly one lit in the clause which is not violated, so it
                                // must become true. The lits array argument could already contain this
                                // lit or its inverse, but the main solver should handle that.
                                r.add_deduced(unassigned_lits[0], rref as u32);
                                //println!("  !! prop add_deduced({:?},{})", unassigned_lits[0], rref as u32);
                                //println!("  !!   from {:?}", c);
                            }
                        }
                    }
                }
            }

            // if we check only reelvant clauses, unit clauses may be forgotten
            if let Check::Final = check {
                if self.check_only_relevant {
                    for (rref, unit_clause) in self
                        .clauses
                        .iter()
                        .enumerate()
                        .filter(|(_, c)| c.len() == 1)
                    {
                        match (
                            self.lits.contains(&unit_clause[0].0),
                            self.lits.contains(&unit_clause[0].inverse().0),
                        ) {
                            (true, false) => {
                                // it is satisfied
                            }
                            (false, true) => {
                                // it is not satisfied
                                if self.propagate_on_conflict {
                                    r.add_clause(unit_clause.iter().cloned());
                                } else {
                                    r.add_deduced(unit_clause[0], rref as u32);
                                }
                            }
                            _ => {
                                panic!();
                            }
                        }
                    }
                }
            }
        }

        fn explain(&mut self, _l: Lit, rref: u32, r: &mut Refinement) {
            r.add_clause(self.clauses[rref as usize].iter().cloned());
        }

        fn new_decision_level(&mut self) {
            self.trail_lim.push(self.trail.len());
        }

        fn backtrack(&mut self, level: i32) {
            if self.trail_lim.len() > level as usize {
                self.trail.truncate(self.trail_lim[level as usize]);
                self.trail_lim.truncate(level as usize);
                self.qhead = self.trail.len();
                self.lits = self.trail.iter().map(|l| l.0).collect();
            }
        }
    }

    for check_only_relevant in [true, false].iter().cloned() {
        for hidden_ratio in [0.0, 0.01, 0.3].iter().cloned() {
            for propagate_on_conflict in [false, true].iter().cloned() {
                let external_solver_path = std::path::PathBuf::from(env!("SATSOLVER"));
                let mut rnd_seed_var = 0.5;
                let rnd_seed = &mut rnd_seed_var;
                for_each_cnf_filename(move |filename| {
                    println!("rnd seed {:?}", rnd_seed);
                    //if !filename.contains("unit7") { return; }
                    if filename.contains("add") || filename.contains("prime65537") {
                        //if filename.contains("add") {
                        // some cases are too slow to be useful as default tests
                        return;
                    }
                    println!(
                        "CASE hidden={}, propagate_on_conflict={}, check_only_relevant={}",
                        hidden_ratio, propagate_on_conflict, check_only_relevant
                    );
                    let mut solver: DplltSolver<HiddenClauseTheory> =
                        DplltSolver::new(Default::default());
                    solver.theory.propagate_on_conflict = propagate_on_conflict;
                    solver.theory.check_only_relevant = check_only_relevant;

                    //if filename.contains("unit4") {
                    //    solver.theory.print = true;
                    //    println!("UNIT4 SOLVER THEORY PRINT=true");
                    //}

                    let text = std::fs::read_to_string(filename).unwrap();
                    let dimacs = dimacs::parse_dimacs(&text).unwrap();
                    let mut all_clauses = Vec::new();
                    match dimacs {
                        dimacs::Instance::Cnf { clauses, .. } => {
                            for c in clauses.iter() {
                                // add the vars
                                for l in c.lits() {
                                    let var = Var(l.var().to_u64() as i32 - 1);
                                    while solver.num_vars() <= var.0 as usize {
                                        solver.new_var(dpllt::LBOOL_UNDEF, true);
                                    }
                                }

                                let lits = c.lits().iter().map(|l| {
                                    Lit::new(
                                        Var(l.var().to_u64() as i32 - 1),
                                        l.sign() == dimacs::Sign::Neg,
                                    )
                                });

                                let rnd = dpllt::drand(rnd_seed);
                                let lits = lits.collect::<Vec<_>>();
                                if rnd < hidden_ratio {
                                    // add to hidden clauses
                                    solver.theory.add_clause(&lits);
                                } else {
                                    // add normally
                                    solver.add_clause(lits.iter().cloned());
                                }
                                all_clauses.push(lits.clone());
                            }
                        }
                        _ => panic!(),
                    }

                    let (in_clauses, out_clauses) = (
                        solver.num_clauses() + solver.num_learnts(),
                        solver.theory.clauses.len(),
                    );
                    //solver.theory.print = true;
                    let r = solver.solve();
                    //solver.theory.print = false;
                    println!("  solve finished = {:?}.", r.as_bool());

                    // verify internal model
                    assert!(verify_model(&mut solver));
                    println!(
                        "  before: {} regular clauses, {} hidden clauses",
                        in_clauses, out_clauses
                    );
                    let (in_clauses, out_clauses) = (
                        solver.num_clauses() + solver.num_learnts(),
                        solver.theory.clauses.len(),
                    );
                    println!(
                        "  after: {} regular clauses, {} hidden clauses",
                        in_clauses, out_clauses
                    );

                    // verify model against hidden clauses
                    //
                    if solver.solve().as_bool().unwrap() {
                        let model = solver
                            .get_model()
                            .unwrap()
                            .iter()
                            .map(|l| l.as_bool().unwrap())
                            .collect::<Vec<bool>>();
                        for c in solver.theory.clauses.iter() {
                            if !c.iter().any(|l| {
                                if l.sign() {
                                    !model[l.var().idx()]
                                } else {
                                    model[l.var().idx()]
                                }
                            }) {
                                println!("clause not sat: {:?}", c);
                                assert!(false);
                            }
                        }
                        println!(
                            "  ok -- checked {} HIDDEN clauses against {} variables",
                            solver.theory.clauses.len(),
                            solver.get_model().unwrap().len()
                        );
                        // TODO check clauses directly from original dimacs
                    }
                    //
                    // verify model against ALL clauses
                    //
                    if solver.solve().as_bool().unwrap() {
                        let model = solver
                            .get_model()
                            .unwrap()
                            .iter()
                            .map(|l| l.as_bool().unwrap())
                            .collect::<Vec<bool>>();
                        for c in all_clauses.iter() {
                            if !c.iter().any(|l| {
                                if l.sign() {
                                    !model[l.var().idx()]
                                } else {
                                    model[l.var().idx()]
                                }
                            }) {
                                println!("clause not sat: {:?}", c);
                                assert!(false);
                            }
                        }
                        println!(
                            "  ok -- checked {} HIDDEN clauses against {} variables",
                            all_clauses.len(),
                            solver.get_model().unwrap().len()
                        );
                        // TODO check clauses directly from original dimacs
                    }

                    // verify sat/unsat with external solver
                    assert!(verify_external_solver(
                        &mut solver,
                        &external_solver_path,
                        filename
                    ));
                });
            }
        }
    }
}

#[test]
fn hidden_clauses_added_using_theory() {
    use dpllt::*;
    #[derive(Default)]
    struct HiddenClauseTheory {
        clauses: Vec<Vec<Lit>>,
        trail: Vec<Lit>,
        trail_lim: Vec<usize>,
        print: bool,
        eager_pruning: bool,
    }

    impl dpllt::Theory for HiddenClauseTheory {
        fn check(&mut self, check: Check, lits: &[Lit], r: &mut Refinement) {
            let print = self.print;
            self.trail.extend(lits);
            //if print { println!("  check({:?},l={},r)", check,lits.len()); }
            let is_final = if let Check::Final = check {
                true
            } else {
                false
            };

            if is_final || self.eager_pruning {
                use std::collections::HashSet;
                let lit_set = self.trail.iter().map(|l| l.0).collect::<HashSet<i32>>();
                let mut any = false;
                for c in self.clauses.iter() {
                    if c.iter().all(|l| lit_set.contains(&(l.inverse().0))) {
                        //if print {println!("  adding {:?}", c); }
                        any = true;
                        r.add_clause(c.iter().cloned());
                    }
                }

                if !self.eager_pruning && !any && print {
                    println!(" all good in {} hidden clauses", self.clauses.len());
                }
            }
        }
        fn explain(&mut self, _l: Lit, _rref: u32, _r: &mut Refinement) {}
        fn new_decision_level(&mut self) {
            self.trail_lim.push(self.trail.len());
        }
        fn backtrack(&mut self, level: i32) {
            if self.trail_lim.len() > level as usize {
                self.trail.truncate(self.trail_lim[level as usize]);
                self.trail_lim.truncate(level as usize);
            }
        }
    }

    for hidden_ratio in [0.0, 0.01, 0.3].iter().cloned() {
        for eager_pruning in [false, true].iter().cloned() {
            let external_solver_path = std::path::PathBuf::from(env!("SATSOLVER"));
            let mut rnd_seed_var = 0.5;
            let rnd_seed = &mut rnd_seed_var;
            for_each_cnf_filename(move |filename| {
                if filename.contains("add") {
                    return;
                } // the "add" files are very slow with hidden clauses.
                println!("CASE hidden={}, eager={}", hidden_ratio, eager_pruning);
                let mut solver: DplltSolver<HiddenClauseTheory> =
                    DplltSolver::new(Default::default());
                solver.theory.eager_pruning = eager_pruning;
                let text = std::fs::read_to_string(filename).unwrap();
                let dimacs = dimacs::parse_dimacs(&text).unwrap();
                let mut all_clauses = Vec::new();
                match dimacs {
                    dimacs::Instance::Cnf { clauses, .. } => {
                        for c in clauses.iter() {
                            // add the vars
                            for l in c.lits() {
                                let var = Var(l.var().to_u64() as i32 - 1);
                                while solver.num_vars() <= var.0 as usize {
                                    solver.new_var(dpllt::LBOOL_UNDEF, true);
                                }
                            }

                            let lits = c.lits().iter().map(|l| {
                                Lit::new(
                                    Var(l.var().to_u64() as i32 - 1),
                                    l.sign() == dimacs::Sign::Neg,
                                )
                            });

                            let rnd = dpllt::drand(rnd_seed);
                            let lits = lits.collect::<Vec<_>>();
                            if rnd < hidden_ratio {
                                // add to hidden clauses
                                solver.theory.clauses.push(lits.clone());
                            } else {
                                // add normally
                                solver.add_clause(lits.iter().cloned());
                            }
                            all_clauses.push(lits.clone());
                        }
                    }
                    _ => panic!(),
                }

                let (in_clauses, out_clauses) = (
                    solver.num_clauses() + solver.num_learnts(),
                    solver.theory.clauses.len(),
                );
                solver.theory.print = true;
                let r = solver.solve();
                solver.theory.print = false;
                println!("  solve finished = {:?}.", r.as_bool());

                // verify internal model
                assert!(verify_model(&mut solver));
                println!(
                    "  before: {} regular clauses, {} hidden clauses",
                    in_clauses, out_clauses
                );
                let (in_clauses, out_clauses) = (
                    solver.num_clauses() + solver.num_learnts(),
                    solver.theory.clauses.len(),
                );
                println!(
                    "  after: {} regular clauses, {} hidden clauses",
                    in_clauses, out_clauses
                );

                // verify model against hidden clauses
                //
                if solver.solve().as_bool().unwrap() {
                    let model = solver
                        .get_model()
                        .unwrap()
                        .iter()
                        .map(|l| l.as_bool().unwrap())
                        .collect::<Vec<bool>>();
                    for c in solver.theory.clauses.iter() {
                        if !c.iter().any(|l| {
                            if l.sign() {
                                !model[l.var().idx()]
                            } else {
                                model[l.var().idx()]
                            }
                        }) {
                            println!("clause not sat: {:?}", c);
                            assert!(false);
                        }
                    }
                    println!(
                        "  ok -- checked {} HIDDEN clauses against {} variables",
                        solver.theory.clauses.len(),
                        solver.get_model().unwrap().len()
                    );
                    // TODO check clauses directly from original dimacs
                }
                //
                // verify model against ALL clauses
                //
                if solver.solve().as_bool().unwrap() {
                    let model = solver
                        .get_model()
                        .unwrap()
                        .iter()
                        .map(|l| l.as_bool().unwrap())
                        .collect::<Vec<bool>>();
                    for c in all_clauses.iter() {
                        if !c.iter().any(|l| {
                            if l.sign() {
                                !model[l.var().idx()]
                            } else {
                                model[l.var().idx()]
                            }
                        }) {
                            println!("clause not sat: {:?}", c);
                            assert!(false);
                        }
                    }
                    println!(
                        "  ok -- checked {} HIDDEN clauses against {} variables",
                        all_clauses.len(),
                        solver.get_model().unwrap().len()
                    );
                    // TODO check clauses directly from original dimacs
                }

                // verify sat/unsat with external solver
                assert!(verify_external_solver(
                    &mut solver,
                    &external_solver_path,
                    filename
                ));
            });
        }
    }
}

#[test]
fn correct_results_on_cnf_file_tests() {
    let external_solver_path = std::path::PathBuf::from(env!("SATSOLVER"));
    for_each_cnf_filename(|filename| {
        let mut solver = dpllt::solver_from_dimacs_filename(filename);
        let _is_sat = solver.prop.solve().as_bool().unwrap();
        println!("  solve finished.");
        assert!(verify_model(&mut solver.prop));
        assert!(verify_external_solver(
            &mut solver.prop,
            &external_solver_path,
            filename
        ));
    });
}

fn verify_external_solver<T: dpllt::Theory>(
    solver: &mut dpllt::DplltSolver<T>,
    ext_solver: &std::path::Path,
    filename: &str,
) -> bool {
    // check with external sat solver
    // the solver should return 10 for sat, 20 for unsat.
    let is_sat = solver.solve().as_bool().unwrap();
    use std::process::{Command, Stdio};
    let mut cmd = Command::new(&ext_solver);
    cmd.arg(filename);
    cmd.stderr(Stdio::null());
    cmd.stdout(Stdio::null());
    println!("  exec {:?}", cmd);
    let status = cmd.status().expect("external solver failed");
    if status.code().unwrap() != if is_sat { 10 } else { 20 } {
        return false;
    }
    println!("  ok  - external solver has same status");
    true
}
