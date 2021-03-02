use crate::*;

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Lit(i32);

impl std::ops::Not for Lit {
    type Output = Lit;
    fn not(self) -> Self::Output {
        Lit(-self.0)
    }
}

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Var(u32);

impl crate::Var for Var {}

impl crate::Lit for Lit {
    type Var = Var;

    fn into_var(self) -> (Self::Var, bool) {
        (Var(self.0.abs() as u32), self.0 < 0)
    }

    fn from_var_sign(v: Self::Var, sign: bool) -> Self {
        Lit(if sign { -(v.0 as i32) } else { v.0 as i32 })
    }
}

pub struct DimacsOutput {
    next_var: u32,
    clauses: Vec<Vec<Lit>>,
}

impl DimacsOutput {
    pub fn new() -> Self {
        DimacsOutput {
            clauses: Vec::new(),
            next_var: 1,
        }
    }

    pub fn write(&self, file: &mut impl std::fmt::Write) -> std::fmt::Result {
        writeln!(file, "p cnf {} {}", self.next_var - 1, self.clauses.len())?;
        for clause in self.clauses.iter() {
            for lit in clause.iter() {
                write!(file, "{} ", lit.0)?;
            }
            writeln!(file, "0")?;
        }
        Ok(())
    }
}

impl SatInstance<Lit> for DimacsOutput {
    fn new_var(&mut self) -> Bool<Lit> {
        let l = Bool::Lit(Lit(self.next_var as i32));
        self.next_var += 1;
        l
    }

    fn add_clause<IL: Into<Bool<Lit>>, I: IntoIterator<Item = IL>>(&mut self, clause: I) {
        let lits = clause
            .into_iter()
            .filter_map(|l| match l.into() {
                Bool::Const(false) => None,
                Bool::Const(true) => Some(Err(())),
                Bool::Lit(x) => Some(Ok(x)),
            })
            .collect::<Result<Vec<_>, ()>>();
        if let Ok(lits) = lits {
            self.clauses.push(lits);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn test_dimacs_output() {
        let mut string = String::new();
        let mut dimacs = DimacsOutput::new();
        let x1 = dimacs.new_var();
        let x2 = dimacs.new_var();
        dimacs.add_clause(vec![x1, x2]);
        dimacs.add_clause(vec![!x1, x2]);
        dimacs.write(&mut string).unwrap();
        println!("{}", string);
        assert_eq!("p cnf 2 2\n1 2 0\n-1 2 0\n", string);
    }
}
