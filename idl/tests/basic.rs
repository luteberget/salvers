use idl;

#[test]
fn consts() {
    let mut s = idl::IdlSolver::new();
    let x = s.new_int();
    let y = s.new_int();
    let z = s.new_int();
    s.add_diff(None, y, z, -5);
    s.add_diff(None, x, y, -5);
    assert!(s.solve().is_ok());
    assert!(s.get_int_value(x) + 5 <= s.get_int_value(y));
    assert!(s.get_int_value(y) + 5 <= s.get_int_value(z));
}
