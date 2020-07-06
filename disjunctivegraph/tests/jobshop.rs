use disjunctivegraph;
use itertools::Itertools;

#[test]
pub fn jobshop1() {
    // makespan 9
    let sa = vec![vec![9]];

    // makespan 19
    let sb = vec![vec![9], vec![10]];

    // makespan 6
    let s1 = vec![vec![2, 2], vec![2, 2]];

    // makespan 28
    let s2 = vec![vec![13, 3], vec![2, 5], vec![1, 3], vec![4, 6], vec![5, 7]];

    // makespan 21
    let s3 = vec![vec![4, 3], vec![1, 2], vec![5, 4], vec![2, 3], vec![5, 6]];

    assert_eq!(jobshop(sa).unwrap(), 9);
    assert_eq!(jobshop(sb).unwrap(), 19);
    assert_eq!(jobshop(s1).unwrap(), 6);
    assert_eq!(jobshop(s2).unwrap(), 28);
    assert_eq!(jobshop(s3).unwrap(), 21);

    fn jobshop(job_times: Vec<Vec<u32>>) -> Option<u32> {
        let mut s = disjunctivegraph::SchedulingSolver::new();
        // process 5 jobs, each first on machine 1, then on machine 2.

        let zero = s.new_int();

        // start/end times:
        let jobs = job_times
            .iter()
            .map(|machine_times| {
                let machine_times = machine_times
                    .iter()
                    .map(|processing_time| {
                        let start_time = s.new_int();
                        let end_time = s.new_int();
                        // Constraint: times are greater than zero
                        //s.add_diff(None, zero, start_time, 0);
                        // Constraint: processing takes (at least) specified amount of time.
                        s.add_diff(None, start_time, end_time, *processing_time); // start + proc <= end
                        (start_time, end_time)
                    })
                    .collect::<Vec<_>>();

                // Contraint: processing needs to happen on machines in given order
                for ((_, end_prev), (start_next, _)) in
                    machine_times.iter().zip(machine_times.iter().skip(1))
                {
                    s.add_diff(None, *end_prev, *start_next, 0); // end_prev <= start_next
                }

                machine_times
            })
            .collect::<Vec<_>>();

        let num_machines = jobs.iter().map(|j| j.len()).max().unwrap();
        for machine_idx in 0..num_machines {
            // all the jobs which use this machine
            let jobs = jobs
                .iter()
                .flat_map(|j| j.get(machine_idx))
                .collect::<Vec<&_>>();
            for ((a_start, a_end), (b_start, b_end)) in jobs.iter().tuple_combinations() {
                let a = s.new_bool();
                let b = s.new_bool();
                s.add_diff(Some(a), *a_end, *b_start, 0); // a_end <= b_start
                s.add_diff(Some(b), *b_end, *a_start, 0); // b_end <= a_start
                                                          // Constraint: machine time cannot overlap
                s.add_clause(&vec![a, b]);
            }
        }

        let max_time = s.new_int();
        for job in jobs.iter() {
            for (_, end) in job.iter() {
                s.add_diff(None, *end, max_time, 0); // end <= max_time
            }
        }

        if let Ok(m) = s.solve() {
            println!("SAT");
            let val = m.get_int_value(max_time);
            let mut output: Vec<Vec<u8>> = vec![vec!['_' as u8; val as usize]; num_machines];
            for (job_idx, job) in jobs.iter().enumerate() {
                for (machine_idx, (machine_start, machine_end)) in job.iter().enumerate() {
                    let t1 = m.get_int_value(*machine_start);
                    let t2 = m.get_int_value(*machine_end);
                    println!("j{} m{} t{}-t{}", job_idx, machine_idx, t1, t2);
                    for c in &mut output[machine_idx][t1 as usize..t2 as usize] {
                        *c = std::char::from_digit(job_idx as u32, 10).unwrap() as u8;
                    }
                }
            }

            for (machine, schedule) in output.iter().enumerate() {
                println!(
                    "M{}: {}",
                    machine,
                    String::from_utf8(schedule.clone()).unwrap()
                );
            }
            Some(val as u32)
	} else {
            panic!();
        }


	// TODO optimization using binary search:
        
        //let mut lo = 0;
        //let mut best = None;
        //let mut hi = s.get_int_value(max_time);
        //let (b, val) = loop {
        //    let mid = (lo + hi) / 2;
        //    println!("binsearch {} {} {}", lo, mid, hi);
        //    let x = s.new_bool();
        //    s.add_diff(Some(x), max_time, s.zero(), mid); // max_time <= 5   --> max_time >= 5
        //    if s.solve_with_assumptions(&vec![x]).is_ok() {
        //        println!("mid={} success", mid);
        //        best = Some(x);
        //        hi = mid;
        //    } else {
        //        println!("mid={} failed", mid);
        //        lo = mid + 1;
        //    }
        //    if hi <= lo {
        //        println!("done {} {} {}", lo, mid, hi);
        //        break (x, lo);
        //    }
        //};
        //s.add_diff(None, max_time, s.zero(), val); // max_time <= 5   --> max_time >= 5

        //if s.solve().is_ok() {
        //    println!("SAT");
        //    let mut output: Vec<Vec<u8>> = vec![vec!['_' as u8; val as usize]; num_machines];
        //    for (job_idx, job) in jobs.iter().enumerate() {
        //        for (machine_idx, (machine_start, machine_end)) in job.iter().enumerate() {
        //            let t1 = s.get_int_value(*machine_start);
        //            let t2 = s.get_int_value(*machine_end);
        //            println!("j{} m{} t{}-t{}", job_idx, machine_idx, t1, t2);
        //            for c in &mut output[machine_idx][t1 as usize..t2 as usize] {
        //                *c = std::char::from_digit(job_idx as u32, 10).unwrap() as u8;
        //            }
        //        }
        //    }

        //    for (machine, schedule) in output.iter().enumerate() {
        //        println!(
        //            "M{}: {}",
        //            machine,
        //            String::from_utf8(schedule.clone()).unwrap()
        //        );
        //    }
        //    Some(val as u32)
        //} else {
        //    println!("UNSAT");
        //    panic!();
        //}
    }
}
