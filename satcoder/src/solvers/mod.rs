#[cfg(feature="minisat")]
mod minisat;

#[cfg(feature="minisat")]
pub use ::minisat::Solver as Minisat;

#[cfg(feature="cadical")]
mod cadical;

#[cfg(feature="cadical")]
pub use self::cadical::{Cadical, CdcLit, CdcVar};
