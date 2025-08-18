use std::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Div, DivAssign, Rem, RemAssign};

use crate::BigInt;

macro_rules! impl_ops {
    ($f:ty) => {
        impl Add<BigInt> for $f {
            type Output = BigInt;

            fn add(self, rhs: BigInt) -> Self::Output {
                BigInt::from(self) + rhs
            }
        }

        impl Add<$f> for BigInt {
            type Output = Self;
        
            fn add(self, rhs: $f) -> Self::Output {
                self + BigInt::from(rhs)
            }
        }

        impl AddAssign<$f> for BigInt {
            fn add_assign(&mut self, rhs: $f) {
                *self += BigInt::from(rhs);
            }
        }

        impl Sub<BigInt> for $f {
            type Output = BigInt;

            fn sub(self, rhs: BigInt) -> Self::Output {
                BigInt::from(self) - rhs
            }
        }

        impl Sub<$f> for BigInt {
            type Output = Self;
        
            fn sub(self, rhs: $f) -> Self::Output {
                self - BigInt::from(rhs)
            }
        }

        impl SubAssign<$f> for BigInt {
            fn sub_assign(&mut self, rhs: $f) {
                *self -= BigInt::from(rhs);
            }
        }

        impl Mul<BigInt> for $f {
            type Output = BigInt;

            fn mul(self, rhs: BigInt) -> Self::Output {
                BigInt::from(self) * rhs
            }
        }

        impl Mul<$f> for BigInt {
            type Output = Self;
        
            fn mul(self, rhs: $f) -> Self::Output {
                self * BigInt::from(rhs)
            }
        }

        impl MulAssign<$f> for BigInt {
            fn mul_assign(&mut self, rhs: $f) {
                *self *= BigInt::from(rhs);
            }
        }

        impl Div<BigInt> for $f {
            type Output = BigInt;

            fn div(self, rhs: BigInt) -> Self::Output {
                BigInt::from(self) / rhs
            }
        }

        impl Div<$f> for BigInt {
            type Output = Self;
        
            fn div(self, rhs: $f) -> Self::Output {
                self / BigInt::from(rhs)
            }
        }

        impl DivAssign<$f> for BigInt {
            fn div_assign(&mut self, rhs: $f) {
                *self /= BigInt::from(rhs);
            }
        }

        impl Rem<BigInt> for $f {
            type Output = BigInt;

            fn rem(self, rhs: BigInt) -> Self::Output {
                BigInt::from(self) % rhs
            }
        }

        impl Rem<$f> for BigInt {
            type Output = Self;
        
            fn rem(self, rhs: $f) -> Self::Output {
                self % BigInt::from(rhs)
            }
        }

        impl RemAssign<$f> for BigInt {
            fn rem_assign(&mut self, rhs: $f) {
                *self %= BigInt::from(rhs);
            }
        }
    };
}

impl_ops!(u8); impl_ops!(u16); impl_ops!(u32); impl_ops!(u64); impl_ops!(u128); impl_ops!(usize);
impl_ops!(i8); impl_ops!(i16); impl_ops!(i32); impl_ops!(i64); impl_ops!(i128); impl_ops!(isize); 