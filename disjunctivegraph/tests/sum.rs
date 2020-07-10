use disjunctivegraph;

#[test]
fn basic_sums() {
    let mut s = disjunctivegraph::SchedulingSolver::new();
    let x = s.new_int();
    let y = s.new_int();
    let z = s.new_int();

    let x2 = s.new_bool();
    let x1 = s.new_bool();
    s.add_diff(Some(x1), x, y, 7);
    s.add_diff(Some(x2), x, z, 5);

    s.add_clause(&vec![x1, x2]);

    let m = s.solve().unwrap();
    println!(
        "x1={} x2={} x={} y={} z={}",
        m.get_bool_value(x1),
        m.get_bool_value(x2),
        m.get_int_value(x),
        m.get_int_value(y),
        m.get_int_value(z)
    );
    drop(m);

    // x + y <= 6
    let sumlit = s.new_bool();
    s.add_clause(&vec![sumlit]);
    let sum = s.new_sum_constraint(sumlit, 6);
    s.add_constraint_coeff(sum, x, 1);
    s.add_constraint_coeff(sum, y, 1);

    let m = s.solve().unwrap();
    println!(
        "x1={} x2={} x={} y={} z={}",
        m.get_bool_value(x1),
        m.get_bool_value(x2),
        m.get_int_value(x),
        m.get_int_value(y),
        m.get_int_value(z)
    );
    drop(m);
}
