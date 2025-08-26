/*
* 
* BINARY TRAITS
*
*/

use std::ops::{BitOr, BitOrAssign, Shl, ShlAssign, Shr, ShrAssign};

use crate::{BigInt, BITS};

macro_rules! shl_impl {
    ($f:ty) => {
        impl Shl<$f> for BigInt {
            type Output = BigInt;

            fn shl(self, rhs: $f) -> BigInt {
                let mut output = self.deep_clone();
                output <<= rhs;
                
                output
            }
        }

        impl ShlAssign<$f> for BigInt {
            fn shl_assign(&mut self, rhs: $f) {
                //TODO: Try to make this comperison only for signed integers
                #[allow(unused_comparisons)]
                if rhs < 0 {
                    *self >>= rhs.abs_diff(0);
                    return;
                }

                let small_shift = rhs % BITS as $f;
                let big_shift = rhs as usize / BITS as usize;

                let mut inner = self.inner.borrow_mut();

                let mut big = vec![0; big_shift + 1];
                inner.append(&mut big);

                for i in (0..inner.len() - 1 - big_shift).rev() {
                    let byte = inner[i] << small_shift;
                    let will_carry = byte.count_ones() != inner[i].count_ones();

                    let carry = if will_carry {inner[i] >> (BITS as $f - small_shift)} else {0};

                    inner[i+1+big_shift] |= carry;
                    inner[i+big_shift] = byte;
                }

                for i in 0..big_shift {
                    inner[i] = 0;
                }

                drop(inner);
                self.trim();
            }
        }
    };
}

shl_impl!{u8} shl_impl! {u16} shl_impl! {u32} shl_impl! {u64} shl_impl! {u128} shl_impl! {usize}
shl_impl!{i8} shl_impl! {i16} shl_impl! {i32} shl_impl! {i64} shl_impl! {i128} shl_impl! {isize}

macro_rules! shr_impl {
    ($f:ty) => {
        impl Shr<$f> for BigInt {
            type Output = BigInt;

            fn shr(self, rhs: $f) -> BigInt {
                let mut output = self.deep_clone();
                output >>= rhs;
                
                output
            }
        }

        impl ShrAssign<$f> for BigInt {
            fn shr_assign(&mut self, rhs: $f) {
                //TODO: Try to make this comperison only for signed integers
                #[allow(unused_comparisons)]
                if rhs < 0 {
                    *self <<= rhs.abs_diff(0);
                    return;
                }

                let small_shift = rhs % BITS as $f;
                let big_shift = rhs as usize / BITS as usize;

                let mut inner = self.inner.borrow_mut();

                if big_shift as usize >= inner.len() {
                    inner.clear();
                    inner.push(0);
                    return;
                }

                inner[0] = inner[big_shift] >> small_shift;
                for i in big_shift + 1..inner.len() {
                    let byte = inner[i] >> small_shift;
                    let will_carry = byte.count_ones() != inner[i].count_ones();

                    let carry = if will_carry {inner[i] << (BITS as $f - small_shift)} else {0};

                    inner[i-1-big_shift] |= carry;
                    inner[i-big_shift] = byte;
                }

                for _ in 0..big_shift {
                    inner.pop();
                }

                drop(inner);
                self.trim();
            }
        }
    };
}

shr_impl!{u8} shr_impl! {u16} shr_impl! {u32} shr_impl! {u64} shr_impl! {u128} shr_impl! {usize}
shr_impl!{i8} shr_impl! {i16} shr_impl! {i32} shr_impl! {i64} shr_impl! {i128} shr_impl! {isize}

macro_rules! impl_ops {
    ($f:ty) => {
        impl BitOr<BigInt> for $f {
            type Output = BigInt;

            fn bitor(self, rhs: BigInt) -> Self::Output {
                BigInt::from(self) | rhs
            }
        }

        impl BitOr<$f> for BigInt {
            type Output = Self;
        
            fn bitor(self, rhs: $f) -> Self::Output {
                self | BigInt::from(rhs)
            }
        }

        impl BitOrAssign<$f> for BigInt {
            fn bitor_assign(&mut self, rhs: $f) {
                *self |= BigInt::from(rhs);
            }
        }
    };
}

impl_ops!(u8); impl_ops!(u16); impl_ops!(u32); impl_ops!(u64); impl_ops!(u128); impl_ops!(usize);
impl_ops!(i8); impl_ops!(i16); impl_ops!(i32); impl_ops!(i64); impl_ops!(i128); impl_ops!(isize); 