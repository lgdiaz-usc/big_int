/*
 *
 *  ARITHMETIC TRAITS
 * 
*/

use std::{cell::RefCell, ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign}, rc::Rc};

use crate::{BigInt, DoubleWord, Word, BITS};

impl Add for BigInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let mut output = self.deep_clone();
        output += rhs;

        output
    }
}

impl AddAssign for BigInt {
    fn add_assign(&mut self, rhs: Self) {
        match (self.is_negative, rhs.is_negative) {
            (true, true) => { // -(self.abs() + rhs.abs())
                self.is_negative = false;
                *self += rhs.abs();
                self.is_negative = !self.is_negative;
                return;
            },
            (true, false) => { // -(self.abs() - rhs)
                self.is_negative = false;
                *self -= rhs;
                self.is_negative = !self.is_negative;
                return;
            },
            (false, true) => { // self - rhs.abs()
                *self -= rhs.abs();
                return;
            },
            _ => {}
        }

        let mut inner_l = self.inner.borrow_mut();
        let inner_r = rhs.inner.borrow();

        let mut will_carry = false;

        // For the portion where inner_l and inner_r overlap, add values form the two with carry bits
        let min_length = inner_l.len().min(inner_r.len());
        for i in 0..min_length {
            (inner_l[i], will_carry) = inner_l[i].overflowing_add(inner_r[i] + if will_carry {1} else {0});
        }

        //if inner_r is longer than inner_l, copy inner_r to inner_l and propagate carry bits
        for i in inner_l.len()..inner_r.len() {
            inner_l.push(inner_r[i]);
            if will_carry {
                (inner_l[i], will_carry) = inner_l[i].overflowing_add(1);
            }
        }

        //if inner_l is longer than inner_r, propagate carry bits through the rest of inner_l
        for i in inner_r.len()..inner_l.len() {
            if will_carry {
                (inner_l[i], will_carry) = inner_l[i].overflowing_add(1);
            }
            else {
                break;
            }
        }

        //if there is still a carry bit left after all this, stick it at the end of inner_l
        if will_carry {
            inner_l.push(1);
        }
    }
}

impl Sub for BigInt {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        let mut output = self.deep_clone();
        output -= rhs;

        output
    }
}

impl SubAssign for BigInt {
    fn sub_assign(&mut self, rhs: Self) {
        match (self.is_negative, rhs.is_negative) {
            (true, true) => { // -(self.abs() - rhs.abs())
                self.is_negative = false;
                *self -= rhs.abs();
                self.is_negative = !self.is_negative;
                return;
            },
            (true, false) => { // -(self.abs() + rhs)
                self.is_negative = false;
                *self += rhs;
                self.is_negative = !self.is_negative;
                return;
            },
            (false, true) => { // self + rhs.abs()
                *self += rhs.abs();
                return;
            },
            (false, false) => {
                if *self < rhs { // -(rhs - self)
                    let mut rhs = rhs.deep_clone();
                    std::mem::swap(self, &mut rhs);
                    *self -= rhs;
                    self.is_negative = !self.is_negative;
                    return;
                }
            }
        }

        let mut inner_l = self.inner.borrow_mut();
        let inner_r = rhs.inner.borrow();

        let mut will_borrow = false;

        //for the portion where inner_l and inner_r overlap, subtract values from the twwo while keeping track of borrow bits
        for i in 0..inner_r.len() {
            (inner_l[i], will_borrow) = inner_l[i].overflowing_sub(inner_r[i] + if will_borrow {1} else {0});
        }

        //if inner_l is longer than inner_r, propagate borrow bits throughout rest of inner_l
        for i in inner_r.len()..inner_l.len() {
            if will_borrow {
                (inner_l[i], will_borrow) = inner_l[i].overflowing_sub(1);
            }
            else {
                break;
            }
        }

        //remove any extra 0 bytes from the end of inner_l
        drop(inner_l);
        self.trim();
    }
}

impl Mul for BigInt {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut output = self.deep_clone();
        output *= rhs;

        output
    }
}

impl MulAssign for BigInt {
    fn mul_assign(&mut self, rhs: Self) {
        match (self.is_negative, rhs.is_negative) {
            (true, true) => { // self.abs() * rhs.abs()
                self.is_negative = false;
                *self *= rhs.abs();
                return;
            }
            (true, false) |
            (false, true) => { // -(self.abs() * rhs.abs())
                self.is_negative = false;
                *self *= rhs.abs();
                self.is_negative = true;
                return;
            }
            _ => {}
        }

        let inner_l = self.inner.borrow();
        let inner_r = rhs.inner.borrow();

        let mut carry = 0;

        let mut sum = BigInt::from(0);
        let mut product_to_sum = BigInt::from(0);
        for i in 0..inner_l.len() {
            let mut inner_p = product_to_sum.inner.borrow_mut();
            inner_p.clear();
            for _ in 0..i {
                inner_p.push(0);
            }
            
            let left = inner_l[i];
            for right in inner_r.iter() {
                let byte;
                let double_byte = (left as DoubleWord * *right as DoubleWord + carry as DoubleWord).to_le();
                (carry, byte) = unsafe {
                    let words: [Word; 2] = std::mem::transmute(double_byte);
                    #[cfg(target_endian = "big")]
                    let words = [words[0].swap_bytes, words[1].swap_bytes];
                    (words[1], words[0])
                };
                inner_p.push(byte);
            }
            
            if carry > 0 {
                inner_p.push(carry);
                carry = 0;
            }

            drop(inner_p);
            product_to_sum.trim();
            sum += product_to_sum.clone();
        }
        
        drop(inner_l);
        *self = sum;
    }
}

impl Div for BigInt {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let mut output = self.deep_clone();
        output /= rhs;

        output
    }
}

impl DivAssign for BigInt {
    fn div_assign(&mut self, rhs: Self) {
        match (self.is_negative, rhs.is_negative) {
            (true, true) => { // self.abs / rhs.abs
                self.is_negative = false;
                *self /= rhs.abs();
                return;
            },
            (true, false) |
            (false, true) => { // -(self.abs / rhs.abs())
                self.is_negative = false;
                *self /= rhs.abs();
                self.is_negative = true;
            }
            _ => {}
        }

        (*self, _) = self.div_with_remainder(&rhs);
    }
}

impl Rem for BigInt {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        let mut output = self.deep_clone();
        output %= rhs;

        output
    }
}

impl RemAssign for BigInt {
    fn rem_assign(&mut self, rhs: Self) {
        match (self.is_negative, rhs.is_negative) {
            (true, true) => { // self.abs / rhs.abs
                self.is_negative = false;
                *self %= rhs.abs();
                return;
            },
            (true, false) |
            (false, true) => { // -(self.abs / rhs.abs())
                self.is_negative = false;
                *self %= rhs.abs();
                self.is_negative = true;
            }
            _ => {}
        }

        (_, *self) = self.div_with_remainder(&rhs);
    }
}

impl BigInt {
    pub fn div_with_remainder(&self, denominator: &BigInt) -> (BigInt, BigInt) {
        if denominator.is_zero() {
            panic!("Cannot divide by zero!");
        }
        else if self.is_zero() {
            return (self.deep_clone(), self.deep_clone());
        }
        else if self < denominator {
            return (BigInt::new_16("0"), self.deep_clone());
        }
    
        let inner_l = self.inner.borrow();
        let inner_r = denominator.inner.borrow();
        let mut iter = inner_l
            .iter()
            .map(|x| *x)
            .rev();
    
        let mut quotient = BigInt::new_16("0");
        let mut remainder = {
            let mut inner = if inner_r.len() > 1 {
                iter
                    .by_ref()
                    .take(inner_r.len() - 1)
                    .collect()
            } 
            else {
                vec![0]
            };
        
            inner.reverse();
            BigInt { inner: Rc::new(RefCell::new(inner)), is_negative: false }
        };
    
        for i in iter {
            remainder <<= BITS;
            remainder += i;
            
            let mut q_digit = 0;

            if remainder >= *denominator {
                let mut shift_amount = {
                    let inner_denom = denominator.inner.borrow();
                    let inner_rem = remainder.inner.borrow();
                    let get_bit = |x: Vec<Word>| -> Option<u32> {
                        let x = x.last()?;
                        x.checked_ilog2()
                    };
                    let small_shift = if let (Some(rem_bit), Some(denom_bit)) = (get_bit(inner_rem.to_vec()), get_bit(inner_denom.to_vec())) {
                        rem_bit - denom_bit
                    }
                    else 
                    {
                        0
                    };
                    BITS * (inner_rem.len() - inner_denom.len()) as u32 + small_shift
                };
                let mut denom_temp: BigInt = denominator.deep_clone() << shift_amount;

                
                while remainder >= *denominator {
                    while denom_temp > remainder {
                        denom_temp >>= 1;
                        shift_amount -= 1;
                    }

                    remainder -= denom_temp.clone();
                    q_digit += 1 << shift_amount;
                }
            }

            /*while remainder >= *denominator {
                remainder -= denominator.clone();
                q_digit += 1;
            }*/
        
            quotient <<= BITS;
            quotient += q_digit;
        }
    
        (quotient, remainder)
    }
}

impl Neg for BigInt {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            inner: self.inner.clone(),
            is_negative: !self.is_negative
        }
    }
}