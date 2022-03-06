mod bool;
pub use self::bool::*;

pub mod eqtotalizer;
pub mod mddlinear;

mod totalizer;
pub use self::totalizer::*;

mod cumulativediff;
pub use self::cumulativediff::{CumulativeDiff, UpDown};

pub use self::eqtotalizer::EqTotalizer;
