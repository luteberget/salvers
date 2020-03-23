use mysatsolver::*;
use log::*;

fn solver_from_dimacs_filename(filename: &str) -> SatSolver {
    let mut s = SatSolver::new();
    let text = std::fs::read_to_string(filename).unwrap();
    let dimacs = dimacs::parse_dimacs(&text).unwrap();
    match dimacs {
        dimacs::Instance::Cnf { clauses, .. } => {
            //info!("DIMACS NUM VARS {:?}", num_vars);
            //info!("DIMACS NUM CLAUSES {:?}", clauses.len());
            for c in clauses.iter() {
                for l in c.lits() {
                    let var = Var(l.var().to_u64() as i32 - 1);
                    while s.prop.num_vars() <= var.0 as usize {
                        s.prop.new_var(LBOOL_UNDEF, true);
                    }
                }
                trace!("clause {:?}", c);
                trace!("l0 var {:?}", c.lits().iter().nth(0).unwrap().var());
                trace!("l0 sign {:?}", c.lits().iter().nth(0).unwrap().sign());
                s.prop.add_clause(c.lits().iter().map(|l| {
                    Lit::new(Var(l.var().to_u64() as i32 - 1), l.sign() == dimacs::Sign::Neg)
                }));
            }
        }
        _ => {}
    }
    s
}

fn main() {
    simple_logger::init().unwrap();
    info!("* rust minisat port starting.");
    let args: Vec<String> = std::env::args().collect();
    let filename = &args[1];
    info!("* reading file {}", filename);
    let time_start = cpu_time::ProcessTime::now();
    let mut solver = solver_from_dimacs_filename(filename);

    solver.prop.tracelog_file = Some(
            std::io::BufWriter::new(
            std::fs::File::create("sat2.log").unwrap()));

    info!(" - parse time: {:.2}s", cpu_time::ProcessTime::now().duration_since(time_start).as_millis() as f64 / 1000.0);
    info!("* problem statistics:");
    info!("  - vars: {}", solver.prop.num_vars());
    info!("  - clauses: {}", solver.prop.num_clauses());

    let solve_start = cpu_time::ProcessTime::now();
    let result = solver.prop.solve();
    solver.prop.stats_info(solve_start);
    info!("");
    info!("* result: {}", if result == LBOOL_TRUE { "SAT" } else if result == LBOOL_FALSE { "UNSAT" } else { "UNKNOWN" });
}
