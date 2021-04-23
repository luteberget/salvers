// ------
// Variables and literals
// ------

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(pub i32);
pub const VAR_UNDEF: Var = Var(-1);

impl Var {
    pub fn idx(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(pub i32);

impl Lit {
    pub fn new(Var(var): Var, sign: bool) -> Lit {
        Lit(2 * var + sign as i32)
    }

    pub fn sign(&self) -> bool {
        ((self.0) & 1) != 0
    }

    pub fn var(&self) -> Var {
        Var(self.0 >> 1)
    }

    pub fn inverse(&self) -> Lit {
        Self::new(self.var(), !self.sign())
    }
}

impl std::ops::Not for Lit {
  type Output = Lit;
  fn not(self) -> Lit { self.inverse() }
}

pub const LIT_UNDEF: Lit = Lit(-2);
pub const LIT_ERROR: Lit = Lit(-1);

//#[repr(u8)]
//#[derive(Debug)]
//#[derive(Copy, Clone, PartialEq, Eq)]
//pub enum LBool {
//    False = 0,
//    True = 1,
//    Undef = 2,
//}

#[derive(Debug, Copy, Clone)]
pub struct LBool(u8);

impl PartialEq for LBool {
    fn eq(&self, rhs: &LBool) -> bool {
        ((rhs.0 & 2) & (self.0 & 2)) != 0 || (((rhs.0 & 2) == 0) && rhs.0 == self.0)
    }
}

pub const LBOOL_TRUE: LBool = LBool(0);
pub const LBOOL_FALSE: LBool = LBool(1);
pub const LBOOL_UNDEF: LBool = LBool(2);

impl LBool {
    pub fn xor(&self, b: bool) -> LBool {
        //trace!("xor {} ^ {} = {}", self.0, (b as u8), self.0 ^ (b as u8));
        LBool(self.0 ^ (b as u8))
        //unsafe { std::mem::transmute((*self as u8) ^ (b as u8)) }
    }
    pub fn from_bool(b: bool) -> LBool {
        LBool(b as u8)
        //unsafe { std::mem::transmute(b) }
    }

    pub fn as_bool(&self) -> Option<bool> {
        if *self == LBOOL_TRUE { return Some(true); }
        if *self == LBOOL_FALSE { return Some(false); }
        None
    }
}

impl Default for LBool {
    fn default() -> Self {
        LBOOL_UNDEF
    }
}

