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
                let mut shift_amount = remainder.ilog2() - denominator.ilog2();
                let mut denom_temp = denominator.deep_clone() << shift_amount;

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

    pub fn checked_ilog2(&self) -> Option<u32> {
        if !self.is_zero() && !self.is_negative {
            let inner = self.inner.borrow();
            Some(inner.last()?.checked_ilog2()? + (inner.len() - 1) as u32 * BITS)
        }
        else {
            None
        }
    }

    pub fn checked_ilog10(&self) -> Option<u32> {
        if !self.is_zero() && !self.is_negative {
            let mut val = self.deep_clone();
            let mut log = 0;

            let pow10 = (100_000_000_000_000_000_000_000_000_000_000 as u128).into();
            while val >= pow10 {
                val /= pow10.clone();
                log += 32
            }

            let pow10 = (10_000_000_000_000_000 as u64).into();
            while val >= pow10 {
                val /= pow10.clone();
                log += 16
            }

            let pow10 = (10_000_000_000 as u64).into();
            while val >= pow10 {
                val /= pow10.clone();
                log += 10
            }

            let pow10 = 100_000.into();
            while val >= pow10 {
                val /= pow10.clone();
                log += 5
            }

            let pow10 = 10.into();
            while val >= pow10 {
                val /= pow10.clone();
                log += 1
            }

            Some(log)
        }
        else {
            None
        }
    }

    pub fn checked_ilog(&self, base: &Self) -> Option<u32> {
        if *self <= 0.into() || *base <= 0.into() {
            None
        }
        else if self < base {
            Some(0)
        }
        else {
            let mut n = self.ilog2() / (base.ilog2() + 1);
            let mut r = base.pow(&n.into());

            let ratio = self.clone() / base.clone();
            while r <= ratio {
                n += 1;
                r *= base.clone();
            }

            Some(n)
        }
    }

    pub fn checked_pow(&self, exponent: &BigInt) -> Option<BigInt> {
        if exponent.is_zero() {
            return Some(1.into())
        }
        else if exponent.is_negative {
            let one = 1.into();
            if *self == one {
                return Some(one)
            }
            else if self.is_zero() {
                return None
            }
            else if *self == -one.clone() {
                return Some(BigInt {inner: one.inner, is_negative: exponent.inner.borrow()[0] & 1 == 1})
            }
            else {
                return Some(0.into())
            }
        }

        let mut product = self.deep_clone();

        let mut i: BigInt = 1.into();
        while i < *exponent {
            product *= self.clone();
            i += 1;
        }

        Some(product)
    }

    pub fn checked_isqrt(&self) -> Option<BigInt> {
        if self.is_negative {
            return None
        }
        else if *self == 1.into() {
            return Some(self.deep_clone())
        }
        else {
            let mut root: BigInt = self.clone() >> 1;

            let mut i: BigInt = root.clone() >> 1;
            while !i.is_zero() {
                match (root.clone() * root.clone()).cmp(&self.clone()) {
                    std::cmp::Ordering::Less => root += i.clone(),
                    std::cmp::Ordering::Equal => return Some(root),
                    std::cmp::Ordering::Greater => root -= i.clone(),
                }
                i >>= 1;
            }

            if (root.clone() * root.clone()) <= *self {
                return Some(root)
            }
            else {
                return Some(root - 1)
            }
        }
    }

    #[track_caller]
    pub fn ilog2(&self) -> u32 {
        if let Some(log) = self.checked_ilog2() {
            log
        }
        else {
            panic!("argument of integer logarithm must be positive")
        }
    }

    #[track_caller]
    pub fn ilog10(&self) -> u32 {
        if let Some(log) = self.checked_ilog10() {
            log
        }
        else {
            panic!("argument of integer logarithm must be positive")
        }
    }

    #[track_caller]
    pub fn ilog(&self, base: &Self) -> u32 {
        if let Some(log) = self.checked_ilog(base) {
            log
        }
        else {
            panic!("argument of integer logarithm must be positive")
        }
    }
    
    #[track_caller]
    pub fn pow(&self, exponent: &BigInt) -> BigInt {
        if let Some(product) = self.checked_pow(exponent) {
            product
        }
        else {
            panic!("cannot divide by zero")
        }
    }

    #[track_caller]
    pub fn isqrt(&self) -> BigInt {
        if let Some(root) = self.checked_isqrt() {
            root
        }
        else {
            panic!("argument of integer square root must not be negative")
        }
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