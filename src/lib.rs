use std::{array, cell::RefCell, cmp::Ordering, fmt, rc::Rc};

mod arith;
mod binary_arith;

#[derive(Clone, Debug)]
pub struct BigInt {
    inner: Rc<RefCell<Vec<Word>>>,
    is_negative: bool
}

type Word = u8;
type DoubleWord = u16;
const BITS: u32 = Word::BITS;

impl BigInt {
    pub fn new_16(input: &str) -> Self {
        const HEX_DIGIT: usize = BITS as usize / 4;

        let input_iter: Vec<u8> = input
            .chars()
            .rev()
            .map(|c| {
                if let Some(hex_digit) = c.to_digit(16) {
                    hex_digit as u8
                }
                else {
                    panic!("ERROR: Invalid Hexdigit \'{}\'", c);
                }
            })
            .collect();
        let data = input_iter
            .chunks(HEX_DIGIT)
            .map(|hex_digits| {
                let mut hex_bytes = [0; HEX_DIGIT];
                for i in 0..hex_digits.len() {
                    hex_bytes[i] = hex_digits[i];
                }

                let bytes: [u8; HEX_DIGIT / 2] = array::from_fn(|x| {
                    hex_bytes[x * 2] | (hex_bytes[x * 2 + 1] << 4)
                });

                Word::from_le_bytes(bytes)
            })
            .collect();


        /*while let Some(hex_digit_0) = input_iter.next() {
            if let Some(hex_digit_1) = input_iter.next() {
                data.push(hex_digit_0 | (hex_digit_1 << 4));
            }
            else {
                data.push(hex_digit_0);
            }
        }*/

        Self {
            inner: Rc::new(RefCell::new(data)),
            is_negative: false,
        }
    }

    pub fn new_10(input: &str) -> Self {
        let base = BigInt::new_16("A");
        let mut data = BigInt::new_16("0");

        let input_iter = input
            .chars()
            .map(|c| {
                if let Some(digit) = c.to_digit(10) {
                    digit as Word
                }
                else {
                    panic!("ERROR: Invalid digit \'{}\'", c);
                }
            });

        let big_digit = BigInt {inner: Rc::new(RefCell::new(vec![0])), is_negative: false};
        for digit in input_iter {
            big_digit.inner.borrow_mut()[0] = digit;
            data *= base.clone();
            data += big_digit.clone();
        }

        data
    }

    pub fn deep_clone(&self) -> Self {
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

    pub fn abs(&self) -> Self {
        BigInt {inner: self.inner.clone(), is_negative: false }
    }

    pub fn is_zero(&self) -> bool {
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