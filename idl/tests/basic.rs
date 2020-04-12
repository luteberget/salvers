use idl;

#[test]
fn consts() {
    let mut s = idl::IdlSolver::new();
    let x = s.new_int();
    let y = s.new_int();
    let z = s.new_int();
    s.add_diff(None, y, z, -5);
    s.add_diff(None, x, y, -5);
    assert!(s.solve());
    assert!(s.get_value(x) + 5 <= s.get_value(y));
    assert!(s.get_value(y) + 5 <= s.get_value(z));
}
