use crate::prelude::*;

/// Constraint for a sequence of `n` choices between the numbers `a \in {-1, 0, 1}`, where
///   \sum_{i=0}^j a_i <= c , for each j in [0,n].
/// The RHS bound can be increased incrementally.
pub struct CumulativeDiff<L:Lit> {
    steps :Vec<Step<L>>,
    limits :Vec<Bool<L>>,
}

#[derive(Copy, Clone)]
pub struct UpDown<L : Lit> {
    pub up :Bool<L>,
    pub stay :Bool<L>,
    pub down :Bool<L>,
}

struct Step<L:Lit> {
    updown :UpDown<L>,
    values :Vec<Bool<L>>,
}


impl<L :Lit+std::fmt::Debug> CumulativeDiff<L> {

    pub fn values(&self) -> Vec<Vec<Bool<L>>> {
        self.steps.iter().map(|s| s.values.clone()).collect()
    }

    pub fn new(solver :&mut impl SatInstance<L>, 
           lits :impl IntoIterator<Item = UpDown<L>>,
           limit :u32) -> Self {

        let mut c = Self::new_zero(solver, lits);
        c.extend(solver, limit);
        c
    }

    fn new_zero(solver :&mut impl SatInstance<L>, 
           slots :impl IntoIterator<Item = UpDown<L>>) -> Self {

        let exceeds_zero = SatInstance::new_var(solver);
        let mut prev_d0 :Bool<L> = true.into();
        let mut prev_d1 :Bool<L> = false.into();
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
            SatInstance::add_clause(solver, vec![!updown.up,   !prev_d0, d1]);
            // DOWN 
            SatInstance::add_clause(solver, vec![!updown.down,  prev_d1, !d0]);
            // STAY
            SatInstance::add_clause(solver, vec![!updown.stay,  prev_d1, !d1]);
            SatInstance::add_clause(solver, vec![!updown.stay,  !prev_d0, d0]);



            // exceeds limit?
            SatInstance::add_clause(solver, vec![d0, exceeds_zero]);
            SatInstance::add_clause(solver, vec![!d1, exceeds_zero]);

            steps.push(Step {
                updown,
                values: vec![d0,d1],
            });

            prev_d0 = d0;
            prev_d1 = d1;
        }

        Self { steps, limits: vec![exceeds_zero] }
    }

    pub fn exceeds(&self, limit :u32) -> Bool<L> {
        self.limits[limit as usize]
    }

    pub fn extend(&mut self, solver :&mut impl SatInstance<L>, limit :u32) {
        while self.limits.len() <= limit as usize {
            self.extend_one(solver);
        }
    }

    fn extend_one(&mut self, solver :&mut impl SatInstance<L>) {
        let exceeds = SatInstance::new_var(solver);

        let n = self.limits.len();
        let mut prev_values = (0..(n+1)).map(|_| true.into())
            .chain((0..(n+1)).map(|_| false.into())).collect::<Vec<Bool<_>>>();

        for step in self.steps.iter_mut() {
            let updown = &step.updown;
            let values = &mut step.values;

            values.insert(0, SatInstance::new_var(solver));
            values.push(SatInstance::new_var(solver));

            assert!(values.len() == prev_values.len());

            // Unary number consistency (order encoding)
            SatInstance::add_clause(solver, vec![!values[1], values[0]]);
            SatInstance::add_clause(solver, vec![!values[values.len()-1], values[values.len()-2]]);

            // Can max jump by one per step
            // v0>=y => v1>=y-1
            // v0<=y => v1<=y+1
            //
            // TODO is this necessary?

            SatInstance::add_clause(solver, vec![!prev_values[1], values[0]]);
            SatInstance::add_clause(solver, vec![ prev_values[1], !values[2]]);
            SatInstance::add_clause(solver, vec![ prev_values[prev_values.len()-2], !values[values.len()-1]]);
            SatInstance::add_clause(solver, vec![!prev_values[prev_values.len()-2],  values[values.len()-3]]);


            // prev_values[-2]=T and prev_values[-1]=F became a valid value
            //  - up
            SatInstance::add_clause(solver, vec![!updown.up, !prev_values[prev_values.len()-2], values[values.len()-1]]);
            //  - down
            SatInstance::add_clause(solver, vec![!updown.down, prev_values[prev_values.len()-1], !values[values.len()-2]]);
            //  - straight
            SatInstance::add_clause(solver, vec![!updown.stay, !prev_values[prev_values.len()-2], values[values.len()-2]]);
            SatInstance::add_clause(solver, vec![!updown.stay,  prev_values[prev_values.len()-1], !values[values.len()-1]]);
            //
            // prev_values[ 1]=F and prev_values[0]=T became a valid value
            //  - up
            SatInstance::add_clause(solver, vec![!updown.up, !prev_values[0], values[1]]);
            //  - down
            SatInstance::add_clause(solver, vec![!updown.down,  prev_values[1], !values[0]]);
            //  - straight
            SatInstance::add_clause(solver, vec![!updown.stay, !prev_values[0], values[0]]);
            SatInstance::add_clause(solver, vec![!updown.stay,  prev_values[1], !values[1]]);

            // exceeds limit?
            SatInstance::add_clause(solver, vec![values[0], exceeds]);
            SatInstance::add_clause(solver, vec![!values[values.len()-1], exceeds]);

            prev_values = values.clone();
        }

        self.limits.push(exceeds);
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use crate::prelude::*;

    #[test]
    pub fn test_cumulative_diff_simple() {

        let mut solver = minisat::Solver::new();


        fn negate(n :usize, var :Bool<minisat::Lit>) -> Bool<minisat::Lit> {
            if n % 3 == 0 || n % 5 == 0 { return !var; }
            return var;
        }

        let n = 30;
        let team1home = (0..n).map(|n| negate(n+5,solver.new_var())).collect::<Vec<_>>();
        let team2home = (0..n).map(|n| negate(n,  solver.new_var())).collect::<Vec<_>>();
        println!("team1home {:?}", team1home);
        println!("team2home {:?}", team2home);

        for i in vec![1,2,4,6,8,11,12,20,21,22,23] {
            SatInstance::add_clause(&mut solver, vec![team1home[i]]);
            SatInstance::add_clause(&mut solver, vec![!team2home[i]]);
        }


        let updowns = team1home.iter().copied().zip(team2home.iter().copied()).map(|(h1,h2)| {
            let up = SatInstance::new_var(&mut solver);
            let stay = SatInstance::new_var(&mut solver);
            let down = SatInstance::new_var(&mut solver);
            solver.assert_exactly_one(vec![up,stay,down]);

            SatInstance::add_clause(&mut solver, vec![!h1, !h2, stay]);
            SatInstance::add_clause(&mut solver, vec![ h1,  h2, stay]);
            SatInstance::add_clause(&mut solver, vec![!h1,  h2, up]);
            SatInstance::add_clause(&mut solver, vec![ h1, !h2, down]);
            UpDown { up, stay, down }
        }).collect::<Vec<_>>();

        let mut constraint = CumulativeDiff::new(&mut solver, updowns.iter().copied(), 3);
        SatInstance::add_clause(&mut solver, vec![!constraint.exceeds(2)]);


        let model = solver.solve().unwrap();
        let t1h = team1home.iter().map(|v| model.value(v)).collect::<Vec<bool>>();
        let t2h = team2home.iter().map(|v| model.value(v)).collect::<Vec<bool>>();

        let matrix = constraint.values();

        let mut cumdiff = 0;
        let mut row1 = String::new();
        let mut row2 = String::new();
        let mut row3 = String::new();
        let mut row4 = String::new();

        let mut rows = (0..(matrix[0].len())).map(|_| String::new()).collect::<Vec<String>>();

        for i in 0..n {
            row1.push_str(if t1h[i] { "H   " } else { "A   "});
            row2.push_str(if t2h[i] { "H   " } else { "A   "});
            row4.push_str(if model.value(&updowns[i].up) { "Up  " } else if model.value(&updowns[i].stay) { "St  " } else { assert!(model.value(&updowns[i].down)); "Dn  " });

            for j in 0..(matrix[i].len()) {
                rows[j].push_str(if model.value(&matrix[i][j]) { "### "} else {"___ "});
            }

            cumdiff += if t1h[i] { 1 } else { 0 };
            cumdiff += if t2h[i] { -1 } else { 0 };
            row3.push_str(&format!("{:>03} ", cumdiff));
        }


        println!("{}\n{}\n{}\n{}", row1, row2, row3, row4);
        for row in rows.iter().rev() {
            println!("{}", row);
        }


    }

}
