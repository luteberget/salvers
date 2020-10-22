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

#[test]
fn unsat() {
  // a < b && b < a
  let mut s = idl::IdlSolver::new();
  let a = s.new_int();
  let b = s.new_int();
  // a - b <= -1  --> a + 1 <= b  --> a < b 
  let x = s.new_bool();
  let y = s.new_bool();
  s.add_diff(Some(x), a, b, -1);
  // .. and the opposite
  s.add_diff(Some(y), b, a, -1);
  let result = s.solve();
  println!("sat={}", result.is_ok());
  assert!(result.is_ok());

  s.add_clause(&vec![x]);
  s.add_clause(&vec![y]);
  let result = s.solve();
  println!("sat={}", result.is_ok());
  assert!(result.is_err());
}

#[test]
fn level0_unsat() {
  // a < b && b < a
  let mut s = idl::IdlSolver::new();
  let a = s.new_int();
  let b = s.new_int();
  // a - b <= -1  --> a + 1 <= b  --> a < b 
  s.add_diff(None, a, b, -1);
  // .. and the opposite
  s.add_diff(None, b, a, -1);
  let result = s.solve();
  println!("sat={}", result.is_ok());
  assert!(result.is_err());
}
