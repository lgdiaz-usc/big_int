use std::{cell::RefCell, cmp::Ordering, fmt, ops::{Add, AddAssign}, rc::Rc};

#[derive(Clone, Debug, PartialEq, Eq)]
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

    fn trim(self) {
        let mut inner = self.inner.borrow_mut();
        while inner[inner.len() - 1] == 0 && inner.len() > 1 {
            inner.pop();
        }
    }
}

/*
 *
 *  COMPARISON TRAITS
 * 
 */

impl Ord for BigInt {
    fn cmp(&self, rhs: &Self) -> Ordering {
        if self.is_negative == rhs.is_negative {
            let inner_l = self.inner.borrow();
            let inner_r = rhs.inner.borrow();
            let iter_l = inner_l.iter().rev();
            let iter_r = inner_r.iter().rev();
            let order = iter_l.cmp(iter_r);

            if self.is_negative {
                return order.reverse();
            }

            order
        }
        else {
            self.is_negative.cmp(&rhs.is_negative).reverse()
        }
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

/*
 *
 *  ARITHMETIC TRAITS
 * 
*/

impl Add for BigInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
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

        f.pad_integral(true, "0b", &output)
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

        f.pad_integral(true, "0X", &output)
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

        f.pad_integral(true, "0x", &output)
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

        assert_eq!(format!("{}", format_works), "test");
        assert_eq!(format!("{:b}", binary_test), "1111100011010");
        assert_eq!(format!("{:016b}", binary_test), "0001111100011010");
        assert_eq!(format!("{:X}", hex_test), "4A609");
        assert_eq!(format!("{:06X}", hex_test), "04A609");
        assert_eq!(format!("{:x}", hex_test), "4a609");
        assert_eq!(format!("{:06x}", hex_test), "04a609");
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

        assert!(eq_1.clone() == eq_2.clone());
        assert!(eq_1.clone() == eq_1.clone());
        assert!(eq_1.clone() != eq_3.clone());
        assert!(eq_3.clone() < eq_4.clone());
        assert!(eq_5.clone() < eq_4.clone());
    }
}