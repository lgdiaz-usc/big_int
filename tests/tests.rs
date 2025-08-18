#[cfg(test)]
mod tests {
    use big_int::BigInt;

    #[test]
    fn test_format() {
        let format_works = BigInt::new_16("1A");
        let binary_test = BigInt::new_16("1F1A");
        let hex_test = BigInt::new_16("4A609");
        let neg_test = -BigInt::new_16("A1");
        let neg_zero = -BigInt::new_16("0");
        let dec_test = BigInt::new_10("1229026");

        assert_eq!(format!("{}", format_works), "test");
        assert_eq!(format!("{:b}", binary_test), "1111100011010");
        assert_eq!(format!("{:016b}", binary_test), "0001111100011010");
        assert_eq!(format!("{:X}", hex_test), "4A609");
        assert_eq!(format!("{:06X}", hex_test), "04A609");
        assert_eq!(format!("{:x}", hex_test), "4a609");
        assert_eq!(format!("{:06x}", hex_test), "04a609");
        assert_eq!(format!("{:#x}", neg_test), "-0xa1");
        assert_eq!(format!("{:x}", neg_zero), "0");
        assert_eq!(format!("{:x}", dec_test), "12c0e2");
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

        assert_eq!(format!("{:x}", basic_adder.clone() + 2), "4");
        assert_eq!(format!("{:x}", 2 + basic_adder.clone()), "4");
    }

    #[test]
    fn test_comparison() {
        let eq_1 = BigInt::new_16("AA1");
        let eq_2 = BigInt::new_16("AA1");
        let eq_3 = BigInt::new_16("AA2");
        let eq_4 = BigInt::new_16("1AA1");
        let eq_5 = -BigInt::new_16("1AA1");

        let zero_1 = BigInt::new_16("0");
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

    #[test]
    fn test_multpilication() {
        let basic_multiply = BigInt::new_16("10");
        let big_multiply = BigInt::new_16("1A45");

        assert_eq!(format!("{:x}", basic_multiply.clone() * big_multiply.clone()), "1a450");
        assert_eq!(format!("{:x}", big_multiply.clone() * basic_multiply.clone()), "1a450");

        let big_multiply_1 = BigInt::new_16("16d92d9");
        let big_multiply_2 = BigInt::new_16("16c6");

        assert_eq!(format!("{:x}", big_multiply_1.clone() * big_multiply_2.clone()), "20855e39d6");
        assert_eq!(format!("{:x}", big_multiply_2.clone() * big_multiply_1.clone()), "20855e39d6");

        assert_eq!(format!("{:x}", -big_multiply_2.clone() * big_multiply_1.clone()), "-20855e39d6");
        assert_eq!(format!("{:x}", big_multiply_2.clone() * -big_multiply_1.clone()), "-20855e39d6");
        assert_eq!(format!("{:x}", -big_multiply_2.clone() * -big_multiply_1.clone()), "20855e39d6");

        let zero = BigInt::new_16("0");
        let one = BigInt::new_16("1");

        assert_eq!(format!("{:x}", big_multiply_1.clone() * zero.clone()), "0");
        assert_eq!(format!("{:x}", zero.clone() * big_multiply_1.clone()), "0");
        assert_eq!(format!("{:x}", big_multiply_1.clone() * one.clone()), "16d92d9");
        assert_eq!(format!("{:x}", one.clone() * big_multiply_1.clone()), "16d92d9");
    }

    #[test]
    fn test_division() {
        let num_1 = BigInt::new_16("f412df");
        let den_1 = BigInt::new_16("12");
        let num_2 = BigInt::new_16("228EE89B284");
        let den_2 = BigInt::new_16("23D402");

        assert_eq!(format!("{:x}", num_1.clone() / den_1.clone()), "d8f45");
        assert_eq!(format!("{:x}", num_1.clone() % den_1.clone()), "5");
        assert_eq!(format!("{:x}", num_2.clone() / den_2.clone()), "f6ed1");
        assert_eq!(format!("{:x}", num_2.clone() % den_2.clone()), "12c0e2")
    }

    #[test]
    fn test_shift() {
        let shifted_num = BigInt::new_16("5467A");
        let shift_amount_1 = 16;
        let shift_amount_2 = 12;

        assert_eq!(format!("{:x}", shifted_num.clone() << shift_amount_1), "5467a0000");
        assert_eq!(format!("{:x}", shifted_num.clone() << shift_amount_2), "5467a000");
        assert_eq!(format!("{:x}", shifted_num.clone() >> shift_amount_1), "5");
        assert_eq!(format!("{:x}", shifted_num.clone() >> shift_amount_2), "54");
        assert_eq!(format!("{:x}", shifted_num.clone() << -shift_amount_2), "54");
        assert_eq!(format!("{:x}", shifted_num.clone() >> -shift_amount_2), "5467a000");
    }

    #[test]
    fn test_cast() {
        let u_8: u8 = 0xF7;
        let u_16: u16 = 0x2348;
        let u_32: u32 = 0x84923837;
        let u_64: u64 = 0x123456789abcdef;
        let i_8: i8 = -0x12;
        let i_16: i16 = -1234;
        let i_32: i32 = 0x45348893;
        let i_64: i64 = 0x123456789abcdef;

        assert_eq!(BigInt::new_10(&u_8.to_string()), u_8.into());
        assert_eq!(BigInt::new_10(&u_16.to_string()), u_16.into());
        assert_eq!(BigInt::new_10(&u_32.to_string()), u_32.into());
        assert_eq!(BigInt::new_10(&u_64.to_string()), u_64.into());
        assert_eq!(-BigInt::new_16("12"), i_8.into());
        assert_eq!(-BigInt::new_10("1234"), i_16.into());
        assert_eq!(BigInt::new_10(&i_32.to_string()), i_32.into());
        assert_eq!(BigInt::new_10(&i_64.to_string()), i_64.into());
    }
}