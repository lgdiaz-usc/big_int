use std::{cell::RefCell, cmp::Ordering, fmt, ops::{Add, AddAssign, Neg, Sub, SubAssign}, process::Output, rc::Rc};

#[derive(Clone, Debug)]
struct BigInt {
    inner: Rc<RefCell<Vec<u8>>>,
    is_negative: bool
}

impl BigInt {
    fn new_16(input: &str) -> Self {
        let mut data = Vec::new();

        let mut input_iter = input
            .chars()
            .rev()
            .map(|c| {
                if let Some(hex_digit) = c.to_digit(16) {
                    hex_digit as u8
                }
                else {
                    panic!("ERROR: Invalid Hexdigit \'{}\'", c);
                }
            });

        while let Some(hex_digit_0) = input_iter.next() {
            if let Some(hex_digit_1) = input_iter.next() {
                data.push(hex_digit_0 | (hex_digit_1 << 4));
            }
            else {
                data.push(hex_digit_0);
            }
        }

        Self {
            inner: Rc::new(RefCell::new(data)),
            is_negative: false,
        }
    }

    fn deep_clone(&self) -> Self {
        let inner = self.inner.borrow().clone();
        Self {
            inner: Rc::new(RefCell::new(inner)),
            is_negative: self.is_negative
        }
    }

    fn trim(&mut self) {
        let mut inner = self.inner.borrow_mut();
        while inner[inner.len() - 1] == 0 && inner.len() > 1 {
            inner.pop();
        }
    }

    fn abs(&self) -> Self {
        BigInt {inner: self.inner.clone(), is_negative: false }
    }

    fn is_zero(&self) -> bool {
        self.inner.borrow().cmp(&vec![0]) == Ordering::Equal
    }
}

/*
 *
 *  COMPARISON TRAITS
 * 
 */

impl Ord for BigInt {
    fn cmp(&self, rhs: &Self) -> Ordering {
        let inner_l = self.inner.borrow();
        let inner_r = rhs.inner.borrow();
        if inner_l[..] == [0] && inner_r[..] == [0] {
            return Ordering::Equal;
        }

        match self.is_negative.cmp(&rhs.is_negative) {
            Ordering::Equal => {
                let iter_l = inner_l.iter().rev();
                let iter_r = inner_r.iter().rev();
                let order = inner_l.len().cmp(&inner_r.len())
                    .then(iter_l.cmp(iter_r));

                if self.is_negative {
                    return order.reverse();
                }

                order
            },
            x => x.reverse()
        }
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl PartialEq for BigInt {
    fn eq(&self, rhs: &Self) -> bool {
        self.cmp(rhs) == Ordering::Equal
    }
}

impl Eq for BigInt {}

/*
 *
 *  ARITHMETIC TRAITS
 * 
*/

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
        }

        //remove any extra 0 bytes from the end of inner_l
        drop(inner_l);
        self.trim();
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

/*
 *
 * FORMATTING TRAITS
 * 
 */

impl fmt::Display for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "test")
    }
}

impl fmt::Binary for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = self.inner.borrow();
        let mut inner_iter = inner.iter().rev();
        let mut output = String::new();

        if let Some(byte) = inner_iter.next() {
            output.extend(format!("{:b}", byte).chars());
        }
        
        for byte in inner_iter {
            output.extend(format!("{:0>8b}", byte).chars());
        }

        f.pad_integral(!self.is_negative || self.is_zero(), "0b", &output)
    }
}

impl fmt::UpperHex for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = self.inner.borrow();
        let mut inner_iter = inner.iter().rev();
        let mut output = String::new();

        if let Some(byte) = inner_iter.next() {
            output.extend(format!("{:X}", byte).chars());
        }
        
        for byte in inner_iter {
            output.extend(format!("{:0>2X}", byte).chars());
        }

        f.pad_integral(!self.is_negative || self.is_zero(), "0X", &output)
    }
}

impl fmt::LowerHex for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = self.inner.borrow();
        let mut inner_iter = inner.iter().rev();
        let mut output = String::new();

        if let Some(byte) = inner_iter.next() {
            output.extend(format!("{:x}", byte).chars());
        }
        
        for byte in inner_iter {
            output.extend(format!("{:0>2x}", byte).chars());
        }

        f.pad_integral(!self.is_negative || self.is_zero(), "0x", &output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format() {
        let format_works = BigInt::new_16("1A");
        let binary_test = BigInt::new_16("1F1A");
        let hex_test = BigInt::new_16("4A609");
        let neg_test = -BigInt::new_16("A1");
        let neg_zero = -BigInt::new_16("0");

        assert_eq!(format!("{}", format_works), "test");
        assert_eq!(format!("{:b}", binary_test), "1111100011010");
        assert_eq!(format!("{:016b}", binary_test), "0001111100011010");
        assert_eq!(format!("{:X}", hex_test), "4A609");
        assert_eq!(format!("{:06X}", hex_test), "04A609");
        assert_eq!(format!("{:x}", hex_test), "4a609");
        assert_eq!(format!("{:06x}", hex_test), "04a609");
        assert_eq!(format!("{:#x}", neg_test), "-0xa1");
        assert_eq!(format!("{:x}", neg_zero), "0");
    }

    #[test]
    fn test_addition() {
        let mut basic_adder = BigInt::new_16("2");
        let overflow_adder = BigInt::new_16("FF");
        let bigger_num_overflow_adder = BigInt::new_16("FFFF");
        let even_bigger_num_adder = BigInt::new_16("10FFFFFF");

        assert_eq!(format!("{:x}", basic_adder.clone() + basic_adder.clone()), "4");
        assert_eq!(format!("{:x}", basic_adder.clone() + overflow_adder.clone()), "101");
        assert_eq!(format!("{:x}", basic_adder.clone() + bigger_num_overflow_adder.clone()), "10001");
        assert_eq!(format!("{:x}", basic_adder.clone() + even_bigger_num_adder.clone()), "11000001");
        assert_eq!(format!("{:x}", even_bigger_num_adder.clone() + basic_adder.clone()), "11000001");

        basic_adder += even_bigger_num_adder.clone();
        assert_eq!(format!("{:x}", basic_adder), "11000001");

        let basic_adder = BigInt::new_16("2");
        assert_eq!(format!("{:x}", basic_adder.clone() + -basic_adder.clone()), "0");
        assert_eq!(format!("{:x}", -basic_adder.clone() + basic_adder.clone()), "0");
        assert_eq!(format!("{:x}", -basic_adder.clone() + -basic_adder.clone()), "-4");

        let mut assign_sign_1 = -basic_adder.deep_clone();
        let mut assign_sign_2 = -basic_adder.deep_clone();
        let mut assign_sign_3 = basic_adder.deep_clone();
        assign_sign_1 += basic_adder.clone();
        assign_sign_2 += -basic_adder.clone();
        assign_sign_3 += -basic_adder.clone();
        assert_eq!(format!("{:x}", assign_sign_1), "0");
        assert_eq!(format!("{:x}", assign_sign_2), "-4");
        assert_eq!(format!("{:x}", assign_sign_3), "0");
    }

    #[test]
    fn test_comparison() {
        let eq_1 = BigInt::new_16("AA1");
        let eq_2 = BigInt::new_16("AA1");
        let eq_3 = BigInt::new_16("AA2");
        let eq_4 = BigInt::new_16("1AA1");
        let eq_5 = BigInt {
            inner: Rc::new(RefCell::new(vec![0xA1, 0x1A])),
            is_negative: true
        };

        let zero_1 = BigInt {
            inner: Rc::new(RefCell::new(vec![0])),
            is_negative: false
        };
        let zero_2 = -(zero_1.clone());

        assert!(eq_1.clone() == eq_2.clone());
        assert!(eq_1.clone() == eq_1.clone());
        assert!(eq_1.clone() != eq_3.clone());
        assert!(eq_3.clone() < eq_4.clone());
        assert!(eq_5.clone() < eq_4.clone());
        assert!(zero_1 == zero_2)
    }

    #[test]
    fn test_subtraction() {
        let basic_sub_1 = BigInt::new_16("4");
        let basic_sub_2 = BigInt::new_16("2");
        let bigger_sub = BigInt::new_16("10002");

        assert_eq!(format!("{:x}", basic_sub_1.clone() - basic_sub_2.clone()), "2");
        assert_eq!(format!("{:x}", basic_sub_2.clone() - basic_sub_1.clone()), "-2");
        assert!(bigger_sub.clone() > basic_sub_2.clone());
        assert_eq!(format!("{:x}", bigger_sub.clone() - basic_sub_2.clone()), "10000");
        assert_eq!(format!("{:x}", bigger_sub.clone() - basic_sub_1.clone()), "fffe");

        assert_eq!(format!("{:x}", basic_sub_1.clone() - -basic_sub_2.clone()), "6");
        assert_eq!(format!("{:x}", -basic_sub_1.clone() - basic_sub_2.clone()), "-6");
        assert_eq!(format!("{:x}", -basic_sub_1.clone() - -basic_sub_2.clone()), "-2");

        let mut assign_sign_1 = -basic_sub_2.deep_clone();
        let mut assign_sign_2 = -basic_sub_2.deep_clone();
        let mut assign_sign_3 = basic_sub_2.deep_clone();
        assign_sign_1 -= basic_sub_2.clone();
        assign_sign_2 -= -basic_sub_2.clone();
        assign_sign_3 -= -basic_sub_2.clone();
        assert_eq!(format!("{:x}", assign_sign_1), "-4");
        assert_eq!(format!("{:x}", assign_sign_2), "0");
        assert_eq!(format!("{:x}", assign_sign_3), "4");

        let mut assign_sign_4 = basic_sub_2.deep_clone();
        assign_sign_4 -= basic_sub_1.clone();
        assert_eq!(format!("{:x}", assign_sign_4), "-2");
    }
}