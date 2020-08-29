use scheduleopt;

#[test]
fn consts() {
    let mut s = scheduleopt::SchedulingSolver::new();
    let x = s.new_int();
    let y = s.new_int();
    let z = s.new_int();
    s.add_diff(None, y, z, 5);
    s.add_diff(None, x, y, 5);
    let m = s.solve().unwrap();
    assert!(m.get_int_value(x) + 5 <= m.get_int_value(y));
    assert!(m.get_int_value(y) + 5 <= m.get_int_value(z));
}
