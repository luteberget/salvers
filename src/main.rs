use mysatsolver::*;
use log::*;


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
