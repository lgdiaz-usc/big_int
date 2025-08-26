use std::ops::{BitOr, BitOrAssign};

use crate::BigInt;

//TODO: Implement binary arthmatic operations on BigInt inputs
impl BitOr for BigInt {
    type Output = BigInt;

    fn bitor(self, rhs: Self) -> Self::Output {
        let mut output = self.deep_clone();
        output |= rhs;
        
        output
    }
}

impl BitOrAssign for BigInt {
    fn bitor_assign(&mut self, rhs: Self) {
        let mut inner_l = self.inner.borrow_mut();
        let inner_r = rhs.inner.borrow();

        for i in 0..(inner_l.len().min(inner_r.len())) {
            inner_l[i] |= inner_r[i];
        }

        for i in inner_l.len()..inner_r.len() {
            inner_l.push(inner_r[i]);
        }
    }
}