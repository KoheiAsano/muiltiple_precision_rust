mod complex;

use std::fmt;
use std::ops;
// 10digit_t.pow(9)
const KETA: usize = 100;
type DigitT = u64;
const RADIX: DigitT = 10000000;

// little endian
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
                format!(
                    "{:0RLENGTH$}",
                    self.digit[i],
                    RLENGTH = RADIX.to_string().len() - 1
                ),
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
                format!(
                    "{:0RLENGTH$}",
                    self.digit[i],
                    RLENGTH = RADIX.to_string().len() - 1
                ),
                res
            );
        }
        write!(f, "{}{}", sign, res)
    }
}

// array which length is over 32 can't derive PartialEq, PartialOrd
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

impl Eq for BigInt {}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for BigInt {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.plus ^ other.plus {
            if self.plus {
                return std::cmp::Ordering::Greater;
            } else {
                return std::cmp::Ordering::Less;
            }
        }
        for i in (0..KETA).rev() {
            if self.digit[i] < other.digit[i] {
                return std::cmp::Ordering::Less;
            } else if self.digit[i] > other.digit[i] {
                return std::cmp::Ordering::Greater;
            }
        }
        std::cmp::Ordering::Equal
    }
}

#[test]
fn check_cmp() {
    let a = BigInt::from("11111111111111111111111111111111111111111111111111");
    let b = BigInt::from("999");
    assert!(a > b);
    assert!(a >= b);
    let a = BigInt::from("-11111111111111111111111111111111111111111111111111");
    let b = BigInt::from("999");
    assert!(a < b);
    assert!(a <= b);
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
    // division by DigitT
    // return quotient and remainder tuple
    fn positive_division_by_d(&self, divisor: DigitT) -> (BigInt, DigitT) {
        if divisor == 0 {
            panic!("zero division when positive_division_by_d");
        }
        let mut q = BigInt::new();
        let msd = self.most_d();
        // variable for managing remainder + digit
        let mut tmpq: DigitT;
        let mut remainder: DigitT = self.digit[msd - 1];
        let mut num: DigitT = self.digit[msd - 1];
        for i in (0..msd).rev() {
            tmpq = num / divisor;
            remainder = num % divisor;
            q.digit[i] = tmpq;
            // avoid -1 access
            if i == 0 {
                break;
            }
            num = remainder * RADIX + self.digit[i - 1];
        }

        (q, remainder)
    }

    // subtarct until divisor > divided
    fn naive_positive_division(&self, divisor: BigInt) -> (BigInt, BigInt) {
        if divisor == BigInt::from(0) {
            panic!("zero division when positive_division");
        } else if !self.abs_is_bigger(divisor) {
            return (BigInt::new(), *self);
        }
        // if divisor is less than RADIX, execute d division
        if !divisor.abs_is_bigger(BigInt::from(RADIX)) {
            let (q, r): (BigInt, DigitT) = self.positive_division_by_d(divisor.digit[0]);
            return (q, BigInt::from(r));
        }
        // copy variables
        let mut rhs = *self;
        let mut qd: DigitT = 0;
        while rhs.abs_is_bigger(divisor) {
            rhs = rhs - divisor;
            qd += 1;
        }

        (BigInt::from(qd), rhs)
    }

    fn positive_division(&self, divisor: BigInt) -> (BigInt, BigInt) {
        let mut q = BigInt::new();
        let mut r = BigInt::new();
        if divisor == BigInt::from(0) {
            panic!("zero division when positive_division");
        } else if !self.abs_is_bigger(divisor) {
            return (BigInt::new(), *self);
        }
        // if divisor is less than RADIX, execute d division
        if !divisor.abs_is_bigger(BigInt::from(RADIX)) {
            let (q, r): (BigInt, DigitT) = self.positive_division_by_d(divisor.digit[0]);
            return (q, BigInt::from(r));
        }

        (q, r)
    }
}

#[test]
fn check_positive_naive_division() {
    let a = BigInt::from("33333333333333333333333333333333333333333333333333");
    let b = BigInt::from("11111111111111111111111111111111111111111111111111");
    assert_eq!(
        a.naive_positive_division(b),
        (BigInt::from(3), BigInt::from(0))
    );
    assert_eq!(b.naive_positive_division(a), (BigInt::from(0), b));
}

#[test]
fn check_positive_division_divisor_smaller_than_RADIX() {
    let a = BigInt::from("11111111111111111111111111111111111111111111111111");
    let b = BigInt::from(11);
    assert_eq!(
        (
            BigInt::from("1010101010101010101010101010101010101010101010101"),
            BigInt::from(0)
        ),
        a.positive_division(b)
    );
    let a = BigInt::from("1111111111111111111111111111111111111111111111111");
    let b = BigInt::from(11);
    assert_eq!(
        (
            BigInt::from("101010101010101010101010101010101010101010101010"),
            BigInt::from(1)
        ),
        a.positive_division(b)
    );
}

#[test]
fn check_positive_division_by_d() {
    let a = BigInt::from("999");
    let c = 7;
    assert_eq!((BigInt::from(142), 5), a.positive_division_by_d(c));

    let a = BigInt::from("11111111111111111111111111111111111111111111111111");
    let c = 11;
    assert_eq!(
        (
            BigInt::from("1010101010101010101010101010101010101010101010101"),
            0
        ),
        a.positive_division_by_d(c)
    );
    let a = BigInt::from("1111111111111111111111111111111111111111111111111");
    let c = 11;
    assert_eq!(
        (
            BigInt::from("101010101010101010101010101010101010101010101010"),
            1
        ),
        a.positive_division_by_d(c)
    );
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
        // (-a) + (+b), (+a) + (-b) => sign*|b| - |a|

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
            // subtract
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
        let mut result: BigInt = BigInt::new();
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
            let most_d = std::cmp::max(lhs.most_d(), rhs.most_d());
            for i in 0..most_d {
                // to prevent underflow, cast to signed temporarily
                let li = lhs.digit[i] as i64 - borrow as i64;
                let ri = rhs.digit[i] as i64;
                if li >= ri {
                    borrow = 0;
                    result.digit[i] = (li - ri) as u64;
                } else {
                    borrow = 1;
                    result.digit[i] = (li + RADIX as i64 - ri) as u64;
                }
            }
            result
        } else {
            // let rhs's sign be same to lhs and result
            rhs.plus = lhs.plus;
            result.plus = rhs.plus;
            result.digit = (lhs + rhs).digit;
            result
        }
    }
}

impl ops::Mul<BigInt> for BigInt {
    type Output = BigInt;

    fn mul(self, rhs: BigInt) -> BigInt {
        // check overflow
        let lhsd = self.most_d();
        let rhsd = rhs.most_d();
        let resd = lhsd + rhsd - 1;
        if resd > KETA {
            panic!("overflow by multiply {} {}", self, rhs);
        }
        let sign = !(self.plus ^ rhs.plus);
        // FFT
        let mut lhsv = self.digit.to_vec();
        lhsv.truncate(lhsd);
        let mut rhsv = rhs.digit.to_vec();
        rhsv.truncate(rhsd);

        let resv = complex::convolution(lhsv, rhsv);
        // carry calc
        let mut res = BigInt::new();
        let mut carry = 0;

        for i in 0..resd {
            res.digit[i] = (resv[i] + carry) % RADIX;
            carry = (resv[i] + carry) / RADIX;
        }
        // add carry to +1
        // if resd == KETA, carry is calculated
        if carry != 0 && resd < KETA {
            res.digit[resd] += carry;
        } else if carry != 0 && resd > KETA {
            panic!("overflow by multiply {} {}", self, rhs);
        }
        res.plus = sign;
        res
    }
}

// divmod
impl ops::Div<BigInt> for BigInt {
    type Output = BigInt;
    fn div(self, rhs: BigInt) -> BigInt {
        let lmd = self.most_d();
        let rmd = rhs.most_d();

        BigInt::new()
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

        let a = BigInt::from("9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999");
        let b = BigInt::from("1");
        assert_eq!(a + b, BigInt::from("10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"));

        println!("minus-minus addition");
        let a = BigInt::from("-5890653482749054327862489");
        let b = BigInt::from("-5234789102849789543298094821");
        assert_eq!(a + b, BigInt::from("-5240679756332538597625957310"));
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
        // failed
        println!("trivial plus-plus subtraction");
        let a = BigInt::from("1000000000000000000000000000000000");
        let b = BigInt::from(1);
        let expected = BigInt::from("999999999999999999999999999999999");
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

        let a = BigInt::from("10000000000000000000000000000000000000000");
        let b = BigInt::from("-12");
        assert_eq!(
            BigInt::from("-9999999999999999999999999999999999999988"),
            -a - b
        );
        assert_eq!(
            BigInt::from("9999999999999999999999999999999999999988"),
            a - -b
        );
    }

    #[test]
    fn check_mul10() {
        // trivial
        let a = BigInt::from(1);
        assert_eq!(a.mul_10(), BigInt::from(10));
        let a = BigInt::from(10);
        assert_eq!(a.mul_10(), BigInt::from(100));

        // carry
        let a = BigInt::from(10e8 as DigitT);
        assert_eq!(a.mul_10(), BigInt::from(10e9 as DigitT));
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

    #[test]
    fn check_mul() {
        let a = BigInt::from("32");
        let b = BigInt::from("1000000000");
        assert_eq!(BigInt::from("32000000000"), a * b);
        println!("{:?}", a * b);

        let a = BigInt::from("452378947239841");
        let b = BigInt::from("43");
        assert_eq!(BigInt::from("19452294731313163"), a * b);
        println!("{:?}", a * b);

        let a = BigInt::from("41238972198432");
        let b = BigInt::from("48231904");
        assert_eq!(BigInt::from("1989034148133441174528"), a * b);
        println!("{:?}", a * b);

        // fail by FFT in RADIX 10e8
        let a = BigInt::from("888888888888888888888888888888");
        let b = BigInt::from("999999999999999999999");
        assert_eq!(
            BigInt::from("888888888888888888887999999999111111111111111111112"),
            a * b
        );
        println!("{:?}", a * b);

        // fail by FFT in RADIX 10e8
        let a = BigInt::from("543247823184372189426374123789");
        let b = BigInt::from("5423789537982734482319");
        assert_eq!(
            BigInt::from("2946461859919292271212567654121269375800000137786691"),
            a * b
        );
        println!("{:?}", a * b);

        // fail by FFT in RADIX 10e8
        let a = BigInt::from("789423174982");
        let b = BigInt::from("423167842318");
        println!("{:?}", BigInt::from("334058501632957898488276"));
        assert_eq!(BigInt::from("334058501632957898488276"), a * b);

        //
        let a = BigInt::from("7452389175894327895723854328795743289");
        let b = BigInt::from("421367823487587526374856287563287463");
        assert_eq!(
            BigInt::from(
                "3140197006829049027326400623755143724244440804108280978168630025460085807"
            ),
            a * b
        );

        let a = BigInt::from(
        "4321897534278979840982390789375247892789573894371890539289031059831724095809483229008092",
    );
        let b = BigInt::from(
        "4321897534278979840982390789375247892789573894371890539289031059831724095809483229008092",
    );
        assert_eq!(
        BigInt::from("18678798296806725729632843531724954588411763967224168026859565546943628803082105789221693575021621123151092717582962258522556308702085309879175138442985230798847117578201480464"),
        a * b
    );
    }
}
