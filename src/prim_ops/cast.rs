use std::{cell::RefCell, rc::Rc};
use crate::{BigInt, Word, BITS};

pub trait SplitIntoWords {
    fn split_into_words(&self) -> Vec<Word>;
}

macro_rules! split_impl {
    ($f:ty) => {
        impl SplitIntoWords for $f {
            fn split_into_words(&self) -> Vec<Word> {
                #[allow(unused_comparisons)]
                if *self < 0 {
                    return self.abs_diff(0).split_into_words();
                }

                let num = *self;
            
                if <$f>::BITS <= BITS {
                    return vec![num as Word]
                }
            
                const BYTE_COUNT: usize = (BITS / 8) as usize;
            
                let data = num.to_le_bytes()
                    .to_vec()
                    .chunks_exact(BYTE_COUNT)
                    .map(|bytes| {
                        let mut _bytes = std::array::from_fn(|x| bytes[x]);
                        Word::from_le_bytes(_bytes)
                    })
                    .collect();
            
                #[cfg(target_endian = "big")]
                data.iter()
                    .rev()
                    .collect();
                #[cfg(not(target_endian = "big"))]
                data
            }
        }
    };
}

split_impl!{u8} split_impl! {u16} split_impl! {u32} split_impl! {u64} split_impl! {u128} split_impl! {usize}
split_impl!{i8} split_impl! {i16} split_impl! {i32} split_impl! {i64} split_impl! {i128} split_impl! {isize}

macro_rules! from_impl {
    ($f:ty) => {
        impl From<$f> for BigInt {
            fn from(value: $f) -> Self {
                #[allow(unused_comparisons)]
                let mut output = Self {
                    inner: Rc::new(RefCell::new(value.split_into_words())),
                    is_negative: value < 0
                };

                output.trim();
                output
            }
        }
    };
}

from_impl!{u8} from_impl! {u16} from_impl! {u32} from_impl! {u64} from_impl! {u128} from_impl! {usize}
from_impl!{i8} from_impl! {i16} from_impl! {i32} from_impl! {i64} from_impl! {i128} from_impl! {isize}