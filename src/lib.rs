use std::{array, cell::RefCell, cmp::Ordering, fmt, rc::Rc};

mod prim_ops;
mod self_ops;

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

    pub fn new_8(input: &str) -> Self {
        const OCTET_LIMIT: usize = BITS as usize / 3;

        let input_iter: Vec<Word> = input
            .chars()
            .map(|c| {
                if let Some(octet) = c.to_digit(8) {
                    octet as Word
                }
                else {
                    panic!("ERROR: Invalid Octet \'{}\'", c);
                }
            })
            .collect();

        let mut data = BigInt::from(0);

        input_iter
            .chunks(OCTET_LIMIT)
            .for_each(|octets| {
                let mut word = 0;
                for i in 0..octets.len() {
                    word |= octets[i] << (3*(octets.len() - 1 - i));
                }

                data <<= 3 * octets.len();
                data |= word;
            });

        data
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

    pub fn new_2(input: &str) -> Self {
        let input_iter: Vec<bool> = input
            .chars()
            .rev()
            .map(|c| {
                if let Some(bit) = c.to_digit(2) {
                    bit == 1
                }
                else {
                    panic!("ERROR: Invalid bit \'{}\'", c);
                }
            })
            .collect();

        let data = input_iter
            .chunks(BITS as usize)
            .map(|bits| {
                let mut word = 0;
                for i in 0..bits.len() {
                    if bits[i] {
                        word |= 1 << i;
                    }
                }

                word
            })
            .collect();
        
        Self {
            inner: Rc::new(RefCell::new(data)),
            is_negative: false
        }
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
        let mut self_temp = self.deep_clone();
        let mut output = String::new();

        const MAX_DIGITS: u32 = Word::MAX.ilog10();
        let max_digits = BigInt::from(10_usize.pow(MAX_DIGITS));

        while self_temp >= max_digits {
            let digits;
            (self_temp, digits) = self_ops::arith::div_with_remainder(&self_temp, &max_digits);
            let inner = digits.inner.borrow();
            output.extend(format!("{:0<width$}", inner[0], width = MAX_DIGITS as usize).chars().rev());
        }

        {
            let inner = self_temp.inner.borrow();
            output.extend(format!("{}", inner[0]).chars().rev());
        }

        output = output.chars().rev().collect();

        f.pad_integral(!self.is_negative || self.is_zero(), "0d", &output)
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
            output.extend(format!("{:0>width$b}", byte, width = BITS as usize).chars());
        }

        f.pad_integral(!self.is_negative || self.is_zero(), "0b", &output)
    }
}

impl fmt::Octal for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut self_temp = self.deep_clone();
        let mut output = String::new();

        const SHIFT_LENGTH: u32 = (BITS / 3) * 3;
        const OCTETS_MASK: Word = {
            let mut mask = 0;
            let mut i = 0;
            while i < SHIFT_LENGTH {
                mask |= 1 << i;
                i += 1;
            }
            mask
        };

        let max_octets = BigInt::from(1 << SHIFT_LENGTH);

        while self_temp >= max_octets {
            let octets = self_temp.inner.borrow()[0] & OCTETS_MASK;
            output.extend(format!("{:0<width$o}", octets, width = BITS as usize / 3).chars().rev());
            self_temp >>= SHIFT_LENGTH;
        }

        {
            let octets = self_temp.inner.borrow()[0] & OCTETS_MASK;
            output.extend(format!("{:o}", octets).chars().rev());
        }

        output = output.chars().rev().collect();

        f.pad_integral(!self.is_negative || self.is_zero(), "0o", &output)
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
            output.extend(format!("{:0>width$X}", byte, width = BITS as usize / 4).chars());
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
            output.extend(format!("{:0>width$x}", byte, width = BITS as usize / 4).chars());
        }

        f.pad_integral(!self.is_negative || self.is_zero(), "0x", &output)
    }
}