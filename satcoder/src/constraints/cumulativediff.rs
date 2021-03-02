use crate::prelude::*;

/// Constraint for a sequence of `n` choices between the numbers `a \in {-1, 0, 1}`, where
///   \sum_{i=0}^j a_i <= c , for each j in [0,n].
/// The RHS bound can be increased incrementally.
pub struct CumulativeDiff<L: Lit> {
    steps: Vec<Step<L>>,
    limits: Vec<Bool<L>>,
}

#[derive(Copy, Clone)]
pub struct UpDown<L: Lit> {
    pub up: Bool<L>,
    pub stay: Bool<L>,
    pub down: Bool<L>,
}

struct Step<L: Lit> {
    updown: UpDown<L>,
    values: Vec<Bool<L>>,
}

impl<L: Lit + std::fmt::Debug> CumulativeDiff<L> {
    pub fn values(&self) -> Vec<Vec<Bool<L>>> {
        self.steps.iter().map(|s| s.values.clone()).collect()
    }

    pub fn new(
        solver: &mut impl SatInstance<L>,
        lits: impl IntoIterator<Item = (Bool<L>, Bool<L>)>,
        limit: u32,
    ) -> Self {
        let lits = lits
            .into_iter()
            .map(|(h1, h2)| {
                let up = SatInstance::new_var(solver);
                let stay = SatInstance::new_var(solver);
                let down = SatInstance::new_var(solver);
                solver.assert_exactly_one(vec![up, stay, down]);

                SatInstance::add_clause(solver, vec![!h1, !h2, stay]);
                SatInstance::add_clause(solver, vec![h1, h2, stay]);
                SatInstance::add_clause(solver, vec![!h1, h2, up]);
                SatInstance::add_clause(solver, vec![h1, !h2, down]);
                UpDown { up, stay, down }
            })
            .collect::<Vec<_>>();
        let mut c = Self::new_zero(solver, lits);
        c.extend(solver, limit);
        c
    }

    fn new_zero(
        solver: &mut impl SatInstance<L>,
        slots: impl IntoIterator<Item = UpDown<L>>,
    ) -> Self {
        let exceeds_zero = SatInstance::new_var(solver);
        let mut prev_d0: Bool<L> = true.into();
        let mut prev_d1: Bool<L> = false.into();
        let mut steps = Vec::new();
        for updown in slots {
            let d0 = SatInstance::new_var(solver);
            let d1 = SatInstance::new_var(solver);

            // Unary number consistency (order encoding)
            SatInstance::add_clause(solver, vec![!d1, d0]);

            // max jump by one
            SatInstance::add_clause(solver, vec![!prev_d1, d0]);
            SatInstance::add_clause(solver, vec![prev_d0, !d1]);

            // UP
            SatInstance::add_clause(solver, vec![!updown.up, !prev_d0, d1]);
            // DOWN
            SatInstance::add_clause(solver, vec![!updown.down, prev_d1, !d0]);
            // STAY
            SatInstance::add_clause(solver, vec![!updown.stay, prev_d1, !d1]);
            SatInstance::add_clause(solver, vec![!updown.stay, !prev_d0, d0]);

            // exceeds limit?
            SatInstance::add_clause(solver, vec![d0, exceeds_zero]);
            SatInstance::add_clause(solver, vec![!d1, exceeds_zero]);

            steps.push(Step {
                updown,
                values: vec![d0, d1],
            });

            prev_d0 = d0;
            prev_d1 = d1;
        }

        Self {
            steps,
            limits: vec![exceeds_zero],
        }
    }

    pub fn exceeds(&self, limit: u32) -> Bool<L> {
        self.limits[limit as usize]
    }

    pub fn extend(&mut self, solver: &mut impl SatInstance<L>, limit: u32) {
        while self.limits.len() <= limit as usize {
            self.extend_one(solver);
        }
    }

    fn extend_one(&mut self, solver: &mut impl SatInstance<L>) {
        let exceeds = SatInstance::new_var(solver);

        let n = self.limits.len();
        let mut prev = (0..(n + 1))
            .map(|_| true.into())
            .chain((0..(n + 1)).map(|_| false.into()))
            .collect::<Vec<Bool<_>>>();

        for step in self.steps.iter_mut() {
            let updown = &step.updown;
            let values = &mut step.values;

            values.insert(0, SatInstance::new_var(solver));
            values.push(SatInstance::new_var(solver));

            assert!(values.len() == prev.len());
            let n = values.len();

            // Unary number consistency (order encoding)
            SatInstance::add_clause(solver, vec![!values[1], values[0]]);
            SatInstance::add_clause(solver, vec![!values[n - 1], values[n - 2]]);

            // Can max jump by one per step
            // v0>=y => v1>=y-1
            // v0<=y => v1<=y+1
            //
            // TODO is this necessary?

            SatInstance::add_clause(solver, vec![!prev[1], values[0]]);
            SatInstance::add_clause(solver, vec![prev[1], !values[2]]);
            SatInstance::add_clause(solver, vec![prev[n - 2], !values[n - 1]]);
            SatInstance::add_clause(solver, vec![!prev[n - 2], values[n - 3]]);

            // prev[-2]=T and prev[-1]=F became a valid value
            //  - up
            SatInstance::add_clause(solver, vec![!updown.up, !prev[n - 2], values[n - 1]]);
            //  - down
            SatInstance::add_clause(solver, vec![!updown.down, prev[n - 1], !values[n - 2]]);
            //  - straight
            SatInstance::add_clause(solver, vec![!updown.stay, !prev[n - 2], values[n - 2]]);
            SatInstance::add_clause(solver, vec![!updown.stay, prev[n - 1], !values[n - 1]]);
            //
            // prev[ 1]=F and prev[0]=T became a valid value
            //  - up
            SatInstance::add_clause(solver, vec![!updown.up, !prev[0], values[1]]);
            //  - down
            SatInstance::add_clause(solver, vec![!updown.down, prev[1], !values[0]]);
            //  - straight
            SatInstance::add_clause(solver, vec![!updown.stay, !prev[0], values[0]]);
            SatInstance::add_clause(solver, vec![!updown.stay, prev[1], !values[1]]);

            // exceeds limit?
            SatInstance::add_clause(solver, vec![values[0], exceeds]);
            SatInstance::add_clause(solver, vec![!values[n - 1], exceeds]);

            prev = values.clone();
        }

        self.limits.push(exceeds);
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    pub fn test_cumulative_diff_param_matrix() {
        for n_forced in vec![0, 1, 2, 3, 4, 5, 6] {
            for forced_up in vec![true, false] {
                let mut solver = minisat::Solver::new();

                fn negate(n: usize, var: Bool<minisat::Lit>) -> Bool<minisat::Lit> {
                    if n % 3 == 0 || n % 5 == 0 {
                        return !var;
                    }
                    return var;
                }

                let n = 30;
                let team1home = (0..n)
                    .map(|n| negate(n + 5, solver.new_var()))
                    .collect::<Vec<_>>();
                let team2home = (0..n)
                    .map(|n| negate(n, solver.new_var()))
                    .collect::<Vec<_>>();
                //println!("team1home {:?}", team1home);
                //println!("team2home {:?}", team2home);

                for i in (4..(4 + n_forced)).chain(20..(20 + n_forced)) {
                    if forced_up {
                        SatInstance::add_clause(&mut solver, vec![team1home[i]]);
                        SatInstance::add_clause(&mut solver, vec![!team2home[i]]);
                    } else {
                        SatInstance::add_clause(&mut solver, vec![!team1home[i]]);
                        SatInstance::add_clause(&mut solver, vec![team2home[i]]);
                    }
                }

                //if n_forced > 0 {
                //    let i = 20+n_forced+2;
                //    if forced_up {
                //        SatInstance::add_clause(&mut solver, vec![team1home[i]]);
                //        SatInstance::add_clause(&mut solver, vec![!team2home[i]]);
                //    } else {
                //        SatInstance::add_clause(&mut solver, vec![!team1home[i]]);
                //        SatInstance::add_clause(&mut solver, vec![team2home[i]]);
                //    }

                //}

                let updowns = team1home
                    .iter()
                    .copied()
                    .zip(team2home.iter().copied())
                    .collect::<Vec<_>>();

                let mut width = 0;
                let mut constraint =
                    CumulativeDiff::new(&mut solver, updowns.iter().copied(), width);
                loop {
                    let longest_run = 2*width;
                    let should_be_sat = n_forced <= longest_run as usize;

                    println!("solving {:?}", solver);
                    println!(
                        "width={:?}, n_forced={:?} should be sat = {:?}",
                        width, n_forced, should_be_sat
                    );
                    let result = SatSolverWithCore::solve_with_assumptions(
                        &mut solver,
                        vec![!constraint.exceeds(width)],
                    )
                    .as_result();
                    let sat = result.is_ok();

                    if let Some(model) = result.ok() {
                        let t1h = team1home
                            .iter()
                            .map(|v| model.value(v))
                            .collect::<Vec<bool>>();
                        let t2h = team2home
                            .iter()
                            .map(|v| model.value(v))
                            .collect::<Vec<bool>>();

                        let matrix = constraint.values();

                        let mut cumdiff = 0;
                        let mut row1 = String::new();
                        let mut row2 = String::new();
                        let mut row3 = String::new();

                        let mut rows = (0..(matrix[0].len()))
                            .map(|_| String::new())
                            .collect::<Vec<String>>();

                        for i in 0..n {
                            row1.push_str(if t1h[i] { "H   " } else { "A   " });
                            row2.push_str(if t2h[i] { "H   " } else { "A   " });

                            for j in 0..(matrix[i].len()) {
                                rows[j].push_str(if model.value(&matrix[i][j]) {
                                    "### "
                                } else {
                                    "___ "
                                });
                            }

                            cumdiff += if t1h[i] { 1 } else { 0 };
                            cumdiff += if t2h[i] { -1 } else { 0 };
                            row3.push_str(&format!("{:>03} ", cumdiff));
                        }

                        println!("{}\n{}\n{}", row1, row2, row3);
                        for row in rows.iter().rev() {
                            println!("{}", row);
                        }
                    }

                    if !should_be_sat {
                        assert!(!sat);
                        width += 1;
                        println!("correctly unsat, Extending");
                        constraint.extend(&mut solver, width);
                        continue;
                    } else {
                        assert!(sat);
                        break;
                    }
                }
            }
        }
    }
}
