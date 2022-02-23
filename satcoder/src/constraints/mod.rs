mod bool;
pub use self::bool::*;

pub mod mddlinear;

mod totalizer;
pub use self::totalizer::*;

mod cumulativediff;
pub use self::cumulativediff::{CumulativeDiff, UpDown};

mod eqtotalizer;
pub use self::eqtotalizer::EqTotalizer;