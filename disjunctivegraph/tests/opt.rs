use disjunctivegraph;

#[test]
fn rclike() {
    let mut s = disjunctivegraph::SchedulingSolver::new();
    let x = s.new_int();
    let y = s.new_int();
    let z = s.new_int();
    s.add_diff(None, x, y, 5);
    s.add_diff(None, y, z, 5);

    let sum1_lit = s.new_bool();
    let sum1 = s.new_sum_constraint(sum1_lit, 9);
    s.add_constraint_coeff(sum1, x, 1);
    s.add_constraint_coeff(sum1, y, 1);
    s.add_constraint_coeff(sum1, z, 1);

    let (cost, model) = s.optimize().unwrap();
    println!(" ** DONE ");
    println!("cost {}", cost);
    println!(
        "x={} y={} z={}",
        model.get_int_value(x),
        model.get_int_value(y),
        model.get_int_value(z)
    );
}
