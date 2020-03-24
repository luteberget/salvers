use mysatsolver;

#[test]
fn correct_results_on_cnf_file_tests() {
    use std::{fs,io,path};
    let mut d = path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/cnfs");
    let external_solver_path = path::PathBuf::from(env!("SATSOLVER"));
    for direntry in fs::read_dir(d).unwrap() {
        let path = direntry.unwrap().path();
        let s = path.to_str().unwrap();
        println!("Test file: {:?}", s);
        let mut solver = mysatsolver::solver_from_dimacs_filename(s);
        let is_sat = solver.prop.solve().as_bool().unwrap();

        if is_sat { 
            // check that each clause is satisfied
            let model = solver.prop.get_model().unwrap().iter().map(|l| l.as_bool().unwrap()).collect::<Vec<bool>>();
            for c in solver.prop.get_clauses() {
                assert!(c.iter().any(|l| if l.sign() { !model[l.var().idx()] } else { model[l.var().idx()] }));
            }
            println!("  ok -- sat model, checked {} clauses against {} variables", 
                     solver.prop.get_clauses().count(),
                     solver.prop.get_model().unwrap().len());
        }

        // check with external sat solver
        // the solver should return 10 for sat, 20 for unsat.
        use std::process::{ Command, Stdio };
        let mut cmd = Command::new(&external_solver_path);
        cmd.arg(s);
        cmd.stderr(Stdio::null());
        cmd.stdout(Stdio::null());
        println!("  exec {:?}", cmd);
        let status = cmd.status().expect("external solver failed");
        assert_eq!(status.code().unwrap(), if is_sat { 10 } else { 20 });
        println!("  ok  - external solver has same status");
    }
}
