use std::{cell::RefCell, cmp::Ordering, fmt, ops::{Add, AddAssign, Neg, Sub, SubAssign}, rc::Rc};

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
        match (self.is_negative, rhs.is_negative) {
            (true, true) => return -(self.abs() + rhs.abs()),
            (true, false) => return -(self.abs() - rhs),
            (false, true) => return self - rhs.abs(),
            _ => {}
        }

        let mut output = Vec::new();

        let (smaller_num, bigger_num) = if self.inner.borrow().len() < rhs.inner.borrow().len() {
            (self.inner.borrow(), rhs.inner.borrow())
        }
        else {
            (rhs.inner.borrow(), self.inner.borrow())
        };

        let mut will_carry = false;
        for i in 0..smaller_num.len() {
            let mut byte = smaller_num[i] + bigger_num[i];
            if will_carry {
                byte += 1;
            }
        
            will_carry = (!will_carry && byte < smaller_num[i]) || (will_carry && byte <= smaller_num[i]);
            output.push(byte);
        }

        for i in smaller_num.len()..bigger_num.len() {
            output.push(bigger_num[i]);
            if will_carry {
                output[i] += 1;
            }

            will_carry = (!will_carry && output[i] < bigger_num[i]) || (will_carry && output[i] <= bigger_num[i]);
        }

        if will_carry {
            output.push(1);
        }

        Self {
            inner: Rc::new(RefCell::new(output)),
            is_negative: false
        }
    }
}

impl AddAssign for BigInt {
    fn add_assign(&mut self, rhs: Self) {
        match (self.is_negative, rhs.is_negative) {
            (true, true) => {
                self.is_negative = false;
                *self += rhs.abs();
                self.is_negative = !self.is_negative;
                return;
            },
            (true, false) => {
                self.is_negative = false;
                *self -= rhs;
                self.is_negative = !self.is_negative;
                return;
            },
            (false, true) => {
                *self -= rhs.abs();
                return;
            },
            _ => {}
        }

        let mut inner_l = self.inner.borrow_mut();
        let inner_r = rhs.inner.borrow();

        let min_length = inner_l.len().min(inner_r.len());
        let mut will_carry = false;
        for i in 0..min_length {
            let mut byte = inner_r[i] + inner_l[i];
            if will_carry {
                byte += 1;
            }
        
            will_carry = (!will_carry && byte < inner_l[i]) || (will_carry && byte <= inner_l[i]);
            inner_l[i] = byte;
        }

        for i in min_length..inner_r.len() {
            inner_l.push(inner_r[i]);
            if will_carry {
                inner_l[i] += 1;
            }

            will_carry = (!will_carry && inner_l[i] < inner_r[i]) || (will_carry && inner_l[i] <= inner_r[i]);
        }

        if will_carry {
            inner_l.push(1);
        }
    }
}

impl Sub for BigInt {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        match (self.is_negative, rhs.is_negative) {
            (true, true) => return -(self.abs() - rhs.abs()),
            (true, false) => return -(self.abs() + rhs),
            (false, true) => return self + rhs.abs(),
            (false, false) => {
                if self < rhs {
                    return -(rhs - self);
                }
            }
        }

        let inner_l = self.inner.borrow();
        let inner_r = rhs.inner.borrow();
        let mut output = Vec::new();

        let mut will_borrow = false;
        for i in 0..inner_r.len() {
            let mut byte = inner_l[i] - inner_r[i];
            if will_borrow {
                byte -= 1;
            }

            will_borrow = (!will_borrow && byte > inner_l[i]) || (will_borrow && byte >= inner_l[i]);
            output.push(byte);
        }

        for i in inner_r.len()..inner_l.len() {
            output.push(inner_l[i]);
            if will_borrow {
                output[i] -= 1;
            }

            will_borrow = (!will_borrow && output[i] > inner_l[i]) || (will_borrow && output[i] >= inner_l[i]);
        }

        let mut output = Self {
            inner: Rc::new(RefCell::new(output)), 
            is_negative: false 
        };
        output.trim();

        output
    }
}

impl SubAssign for BigInt {
    fn sub_assign(&mut self, rhs: Self) {
        match (self.is_negative, rhs.is_negative) {
            (true, true) => { //-(self.abs() - rhs.abs())
                self.is_negative = false;
                *self -= rhs.abs();
                self.is_negative = !self.is_negative;
                return;
            },
            (true, false) => { //-(self.abs() + rhs)
                self.is_negative = false;
                *self += rhs;
                self.is_negative = !self.is_negative;
                return;
            },
            (false, true) => { //self + rhs.abs()
                *self += rhs.abs();
                return;
            },
            (false, false) => {
                if *self < rhs { //-(rhs - self)
                    let mut rhs = rhs;
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
        for i in 0..inner_r.len() {
            let mut byte = inner_l[i] - inner_r[i];
            if will_borrow {
                byte -= 1;
            }

            will_borrow = (!will_borrow && byte > inner_l[i]) || (will_borrow && byte >= inner_l[i]);
            inner_l[i] = byte;
        }

        for i in inner_r.len()..inner_l.len() {
            let mut byte = inner_l[i];
            if will_borrow {
                byte -= 1;
            }

            will_borrow = (!will_borrow && byte > inner_l[i]) || (will_borrow && byte >= inner_l[i]);
            inner_l[i] = byte
        }

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