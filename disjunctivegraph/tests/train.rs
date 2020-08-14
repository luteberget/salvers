use disjunctivegraph;

#[test]
fn trains_test() {
    for t_d in 87..93 { trains(t_d); println!("\n");}
}

fn trains(t_d :i32) {
    let mut s = disjunctivegraph::SchedulingSolver::new();

    // first train arrives/leaves station A at t=0, arrives at B (at least) 60 sec later,
    // leaves B 30 sec later, arrives at C 60 sec later.
    // second train arrives C at t_d=85 or t_d=95, leaves (at least) 0 sec later, arrives at B 60 sec later,
    // leaves B 30 sec later, arrives at A 60 sec later.
    // t_d determines which train should go first to minimise delays.
    //
    // if A goes into BC first, then C is delayed by max(0, 90-t_d) at B.
    // if B goes into BC first, then A is delayed by max(0, t_d-90) at C.

    // Timing variables
    let tr_a_enter = s.new_int();
    let tr_a_leave_A = s.new_int();
    let tr_a_enter_B = s.new_int();
    let tr_a_leave_B = s.new_int();
    let tr_a_enter_C = s.new_int();

    let tr_b_enter = s.new_int();
    let tr_b_leave_C = s.new_int();
    let tr_b_enter_B = s.new_int();

    // Per-train (constant) constraints
    //

    //s.add_diff(None, tr_a_enter, tr_a_leave_A, 0); // This one does nothing at all, leave it out
    //as we maybe won't support zero length edges.
    s.add_diff(None, tr_a_leave_A, tr_a_enter_B, 60);
    s.add_diff(None, tr_a_enter_B, tr_a_leave_B, 30);
    s.add_diff(None, tr_a_leave_B, tr_a_enter_C, 60);

    s.add_diff(None, tr_b_enter, tr_b_leave_C, t_d);
    s.add_diff(None, tr_b_leave_C, tr_b_enter_B, 60);

    // Who goes first? (conflict constraints)
    let b_first = s.new_bool();
    let a_first = !b_first;
    //s.add_clause(vec![a_first, b_first]);  -- this is already implicit here, but would be required if
    // a_first and b_first were independent variables.
    s.add_diff(Some(a_first), tr_a_enter_C, tr_b_leave_C, 1); // set one second to avoid zero-length-edge problems.
    s.add_diff(Some(b_first), tr_b_enter_B, tr_a_leave_B, 1);


    // minmize the delays
    let mut delay_cost_after = |timevar, expected| {
        let sum = s.new_bool();
        println!("bool={:?} int={:?} expected={}", sum, timevar, expected );
        let sum1 = s.new_sum_constraint(sum, expected);
        s.add_constraint_coeff(sum1, timevar, 1);
    };

    print!("delay cost for t_a_enter_B ");
    delay_cost_after(tr_a_enter_B, 60);
    print!("delay cost for t_a_enter_C ");
    delay_cost_after(tr_a_enter_C, 60+30+60);
    print!("delay cost for t_b_enter_B ");
    delay_cost_after(tr_b_enter_B, t_d as u32 +60);

    let (cost, model) = s.optimize().unwrap();
    println!(" ** DONE ");
    println!(" t_d: {}", t_d);
    println!("cost {}", cost);

    let a_first = model.get_bool_value(a_first);
    let b_first = model.get_bool_value(b_first);
    assert!((a_first && !b_first) || (b_first && !a_first));
    if a_first { println!("Train A goes first"); } else { println!("Train B goes first"); }

    let tr_a_enter   = model.get_int_value(tr_a_enter  );
    let tr_a_leave_A = model.get_int_value(tr_a_leave_A);
    let tr_a_enter_B = model.get_int_value(tr_a_enter_B);
    let tr_a_leave_B = model.get_int_value(tr_a_leave_B);
    let tr_a_enter_C = model.get_int_value(tr_a_enter_C);
                                                       
    let tr_b_enter   = model.get_int_value(tr_b_enter  );
    let tr_b_leave_C = model.get_int_value(tr_b_leave_C);
    let tr_b_enter_B = model.get_int_value(tr_b_enter_B);

    println!("Train A:  {} (a) {}  --  {} (b) {}  --  {} (c)", tr_a_enter, tr_a_leave_A, tr_a_enter_B, tr_a_leave_B, tr_a_enter_C);
    println!("Train B:  {} (c) {}  --  {} (b)", tr_b_enter, tr_b_leave_C, tr_b_enter_B);


    //println!(
    //    "x={} y={} z={}",
    //    model.get_int_value(x),
    //    model.get_int_value(y),
    //    model.get_int_value(z)
    //);
}
