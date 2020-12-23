use crate::Lit;

/// A boolean value -- either a variable in a SAT problem, or a constant boolean value.
#[derive(Debug, Copy, Clone, Hash)]
pub enum Bool<L: Lit> {
    Lit(L),
    Const(bool),
}

impl <L:Lit> From<L> for Bool<L> {
    fn from(l: L) -> Self {
        Bool::Lit(l)
    }
}

impl <L:Lit> From<bool> for Bool<L> {
    fn from(b: bool) -> Self {
        Bool::Const(b)
    }
}

impl<L: Lit> Bool<L> {
    pub fn from_lit(l: L) -> Bool<L> {
        Bool::Lit(l)
    }
}

impl<L: Lit> std::ops::Not for Bool<L> {
    type Output = Bool<L>;

    fn not(self) -> Self::Output {
        match self {
            Bool::Lit(l) => Bool::Lit(!l),
            Bool::Const(b) => Bool::Const(!b),
        }
    }
}
