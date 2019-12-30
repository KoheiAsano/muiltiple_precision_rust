mod complex;
use std::fmt;
use std::ops;
// 10digit_t.pow(9)
const KETA: usize = 3;
type DigitT = u64;
const RADIX: DigitT = 1000000000;

// KETAが最上位桁, 0が最下位桁
#[derive(Clone, Copy)]
pub struct BigInt {
    digit: [DigitT; KETA],
    plus: bool,
}

// init by 0
impl BigInt {
    fn new() -> Self {
        BigInt {
            digit: [0; KETA],
            plus: true,
        }
    }
}

// BigInt from DigitT array
impl From<[DigitT; KETA]> for BigInt {
    fn from(d: [DigitT; KETA]) -> Self {
        BigInt {
            digit: d,
            plus: true,
        }
    }
}

// BigInt from String
impl From<&str> for BigInt {
    fn from(s: &str) -> Self {
        if s.len() == 0 {
            panic!("empty string");
        }
        let mut s = s;
        let mut res = BigInt::new();
        let f = s.chars().nth(0).unwrap();
        if f == '-' {
            res.plus = false;
            s = &s[1..];
        } else if f == '+' {
            s = &s[1..];
        }
        for b in s.as_bytes().iter() {
            res = res.mul_10();
            res.digit[0] += (*b - '0' as u8) as DigitT;
        }
        res
    }
}

// BigInt from primitive less than RADIX^2
macro_rules! from_primitive {
    ($U:ty) => {
        impl From<$U> for BigInt {
            fn from(u: $U) -> Self {
                let u = u as DigitT;
                let mut d = [0; KETA];
                if u >= RADIX.pow(2) {
                    panic!("unimplement initialized by over RADIX^2")
                } else {
                    d[1] = u / RADIX;
                    d[0] = u % RADIX;
                }
                BigInt {
                    digit: d,
                    plus: true,
                }
            }
        }
    };
}
from_primitive!(DigitT);

// Display number
// (+/-)11111....
impl fmt::Display for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut res: String = String::new();
        let sign = if self.plus { '+' } else { '-' };
        let most_d: usize = self.most_d();
        for i in 0..most_d - 1 {
            res = format!(
                "{}{}",
                format!("{:0RLENGTH$}", self.digit[i], RLENGTH = 9),
                res
            );
        }
        // most significant digit should'nt be pad
        res = format!("{}{}", format!("{}", self.digit[most_d - 1]), res);
        write!(f, "{}{}", sign, res)
    }
}
// Format for Debug
// (+/-)00...1111
impl fmt::Debug for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut res: String = String::new();
        let sign = if self.plus { '+' } else { '-' };

        for i in 0..KETA {
            res = format!(
                "{}{}",
                format!("{:0RLENGTH$}", self.digit[i], RLENGTH = 9),
                res
            );
        }
        write!(f, "{}{}", sign, res)
    }
}

// array which length is over 32 can't derive PartialEq
impl PartialEq for BigInt {
    fn eq(&self, other: &Self) -> bool {
        // temporary ignore zero's sign
        let mut iszero = true;
        for i in 0..KETA {
            if self.digit[i] != other.digit[i] {
                return false;
            } else if iszero && (self.digit[i] != 0 || other.digit[i] != 0) {
                iszero = false;
            }
        }
        if iszero {
            return true;
        }
        if self.plus != other.plus {
            false
        } else {
            true
        }
    }
}

// methods
impl BigInt {
    // abs comparison >=
    fn abs_is_bigger(&self, other: BigInt) -> bool {
        for i in (0..KETA).rev() {
            if self.digit[i] > other.digit[i] {
                return true;
            } else if self.digit[i] < other.digit[i] {
                return false;
            }
        }
        true
    }
    // multiply by 10
    fn mul_10(&self) -> Self {
        let mut res = BigInt::new();
        res.plus = self.plus;
        let mut carry = 0;
        let mut tmpcarry;
        for i in 0..KETA {
            tmpcarry = (self.digit[i] * 10 + carry) / RADIX;
            res.digit[i] = (self.digit[i] * 10 + carry) % RADIX;
            carry = tmpcarry;
        }
        if carry != 0 {
            panic!("overflow! by mul10");
        }
        res
    }
    // get most significant digit position
    fn most_d(&self) -> usize {
        let mut msd = KETA;
        for i in (0..KETA).rev() {
            if self.digit[i] != 0 {
                msd = i + 1;
                break;
            }
        }
        msd
    }
}

// operations
impl std::ops::Neg for BigInt {
    type Output = BigInt;

    fn neg(self) -> Self::Output {
        BigInt {
            digit: self.digit,
            plus: !self.plus,
        }
    }
}

impl ops::Add<BigInt> for BigInt {
    type Output = BigInt;

    fn add(self, rhs: BigInt) -> BigInt {
        let mut result: BigInt = BigInt::new();

        // (+a) + (+b), (-a) + (-b) => sign*|a| + |b|
        // (-a) - (+b), (+a) - (-b) => sign*|b| - |a|

        if self.plus ^ rhs.plus == false {
            result.plus = self.plus;
            let mut carry: DigitT = 0;
            // ignore 0 prefix
            // consider carry, we need to see most_d of operands + 1
            let most_d = std::cmp::min(std::cmp::max(self.most_d(), rhs.most_d()) + 1, KETA);
            for i in 0..most_d {
                let sum: DigitT = self.digit[i] + rhs.digit[i] + carry;
                result.digit[i] = sum % RADIX;
                carry = if sum >= RADIX { 1 } else { 0 };
            }
            if carry != 0 {
                panic!("overflow!");
            }
        } else {
            if self.plus {
                result = -(-rhs - self);
            } else {
                result = rhs - (-self);
            }
        }
        result
    }
}

impl ops::Sub<BigInt> for BigInt {
    type Output = BigInt;

    fn sub(self, rhs: BigInt) -> BigInt {
        let mut lhs = self;
        let mut rhs = rhs;
        let mut borrow: DigitT = 0;
        let mut result: BigInt = BigInt::from([0; KETA]);
        // calculate sign and swap
        // (+a) - (+b), (-a) - (-b) => sign*|a| - |b|
        // (-a) - (+b), (+a) - (-b) => sign*|a| + |b|
        // left side must be bigger than rhs
        if lhs.plus ^ rhs.plus == false {
            if lhs.abs_is_bigger(rhs) {
                result.plus = lhs.plus;
            } else {
                std::mem::swap(&mut lhs, &mut rhs);
                result.plus = !lhs.plus;
            }
            println!("l={:?}", lhs);
            println!("r={:?}", rhs);
            let most_d = std::cmp::max(lhs.most_d(), rhs.most_d());
            for i in 0..most_d {
                let li = lhs.digit[i] - borrow;
                let ri = rhs.digit[i];
                if li >= ri {
                    borrow = 0;
                    result.digit[i] = li - ri;
                } else {
                    borrow = 1;
                    result.digit[i] = RADIX + li - ri;
                }
            }
            result
        } else {
            // let rhs's sign be same to lhs
            rhs.plus = lhs.plus;
            if self.abs_is_bigger(rhs) {
                result.plus = self.plus;
            } else {
                std::mem::swap(&mut lhs, &mut rhs);
                result.plus = self.plus;
            }
            result.digit = (lhs + rhs).digit;
            result
        }
    }
}

impl ops::Mul<BigInt> for BigInt {
    type Output = BigInt;

    fn mul(self, rhs: BigInt) -> BigInt {
        // Unimplement
        println!("{} * {}", self, rhs);
        self
    }
}

mod tests {
    #[allow(unused_imports)]
    use super::*;
    #[test]
    fn check_negation() {
        let a = BigInt::from("989898989898989898989898");
        let expected = BigInt::from("-989898989898989898989898");
        assert_eq!(-a, expected);
        assert_eq!(a, -expected);
    }

    #[test]
    fn check_same_sign_add() {
        println!("plus-plus addition");
        let a = BigInt::from("12354765243432432");
        let b = BigInt::from("12354765243432432");
        assert_eq!(a + b, BigInt::from("24709530486864864"));

        println!("minus-minus addition");
        let a = BigInt::from("-12354765243432432");
        let b = BigInt::from("-12354765243432432");
        assert_eq!(a + b, BigInt::from("-24709530486864864"));
    }

    #[test]
    fn check_different_sign_add() {
        println!("plus-minus addition");
        let a = BigInt::from("542378932487543");
        let b = BigInt::from("99999999999");
        assert_eq!(a + -b, BigInt::from("542278932487544"));
        assert_eq!(-b + a, BigInt::from("542278932487544"));
    }

    #[test]
    fn check_same_sign_sub() {
        println!("trivial plus-plus subtraction");
        let a = BigInt::from("1111111111111111111111");
        let b = BigInt::from(12);
        let expected = BigInt::from("1111111111111111111099");
        assert_eq!(b - a, -expected);
        assert_eq!(a - b, expected);

        println!("trivial minus-minus subtraction");
        assert_eq!(-a - -b, -expected);
        assert_eq!(-b - -a, expected);

        let a = BigInt::from("542378932487543");
        let b = BigInt::from("99999999999");
        let expected = BigInt::from("542278932487544");
        assert_eq!(b - a, -expected);
        assert_eq!(a - b, expected);

        assert_eq!(-a - -b, -expected);
        assert_eq!(-b - -a, expected);
    }

    #[test]
    fn check_different_sign_sub() {
        println!("different sign minus");
        let a = BigInt::from("1111111111111111111111");
        let b = BigInt::from(12);
        assert_eq!(BigInt::from("-1111111111111111111123"), -a - b);
        assert_eq!(BigInt::from("1111111111111111111123"), a - -b);
    }

    #[test]
    fn check_mul10() {
        // trivial
        let a = BigInt::from(1);
        assert_eq!(a.mul_10(), BigInt::from(10));
        let a = BigInt::from(10);
        assert_eq!(a.mul_10(), BigInt::from(100));
        println!("{:?}", a.digit);
        println!("{:?}", a.mul_10().digit);

        // carry
        let a = BigInt::from(10e8 as DigitT);
        assert_eq!(a.mul_10(), BigInt::from(10e9 as DigitT));
        println!("{:?}", a.digit);
        println!("{:?}", a.mul_10().digit);
        println!("{:?}", 10e8 as u64 / RADIX);
        println!("{:?}", 10e8 as u64);
        println!("{:?}", 10e1);
    }

    #[test]
    fn check_from_string() {
        // trivial
        let i = BigInt::from("10");
        assert_eq!(i, BigInt::from(10));
        // // carry
        let i = BigInt::from("1000000000");
        assert_eq!(i, BigInt::from(10e8 as DigitT));
        let i = BigInt::from("1000000000000");
        assert_eq!(i, BigInt::from(10e11 as DigitT));
        // // negative
        let i = BigInt::from("-1000000000");
        assert_eq!(i, -BigInt::from(10e8 as DigitT));
    }
}
