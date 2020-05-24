//! Optimization and difference logic.

use idl;
use rc2;

#[test]
pub fn opt() {
  let mut solver = idl::IdlSolver::new();
  let a = solver.new_int();
  let b = solver.new_int();

  let x1 = solver.new_bool();
  let x2 = solver.new_bool();

  solver.add_diff(Some(x1), a, b, -5); // x1 => a < b
  solver.add_diff(Some(x2), b, a, -6); // x2 => b < a

  let mut opt = rc2::RC2SoftClauses::new();
  opt.add_soft_clause(&mut solver, vec![x1]);
  opt.add_soft_clause(&mut solver, vec![x2]);

  let opt_result = opt.increase_cost(&mut solver);

  if let Some((cost,_)) = opt_result {
    println!("Cost {}", cost);
    drop(opt_result);
    println!("a = {}", solver.get_int_value(a));
    println!("b = {}", solver.get_int_value(b));
  } else {
    panic!("unsat");
  };

  solver.add_clause(&[!x1]);

  let opt_result = opt.increase_cost(&mut solver);

  if let Some((cost,_)) = opt_result {
    println!("Cost {}", cost);
    drop(opt_result);
    println!("a = {}", solver.get_int_value(a));
    println!("b = {}", solver.get_int_value(b));
  } else {
    panic!("unsat");
  };

  solver.add_clause(&[!x2]);

  let opt_result = opt.increase_cost(&mut solver);

  if let Some((cost,_)) = opt_result {
    println!("Cost {}", cost);
    drop(opt_result);
    println!("a = {}", solver.get_int_value(a));
    println!("b = {}", solver.get_int_value(b));
  } else {
    panic!("unsat");
  };

}
