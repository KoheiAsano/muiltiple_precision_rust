use std::fmt;
use std::ops;
// 10u64.pow(9)
const KETA: usize = 3;
const RADIX: u64 = 1000000000;

// KETAが最上位桁, 0が最下位桁
#[derive(Clone, Copy)]
pub struct BigInt {
    digit: [u64; KETA],
    sign: char,
}

// 0で初期化
impl BigInt {
    fn new() -> Self {
        BigInt {
            digit: [0; KETA],
            sign: '+',
        }
    }
}
// u64配列から正数を作る
impl From<[u64; KETA]> for BigInt {
    fn from(d: [u64; KETA]) -> Self {
        BigInt {
            digit: d,
            sign: '+',
        }
    }
}

// 32KETA以上の場合はPartialEq がunderivable
impl PartialEq for BigInt {
    fn eq(&self, other: &Self) -> bool {
        if self.sign != other.sign {
            false
        } else {
            for i in 0..KETA {
                if self.digit[i] != other.digit[i] {
                    return false;
                }
            }
            true
        }
    }
}

impl fmt::Debug for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut res: String = String::new();

        for i in 0..KETA {
            res = format!(
                "{}{}",
                format!("{:0RLENGTH$}", self.digit[i], RLENGTH = 9),
                res
            );
        }
        write!(f, "{}{}", self.sign, res)
    }
}
//Display number
// +11111
impl fmt::Display for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut res: String = String::new();
        let most_d: usize = {
            let mut msd: usize = KETA;
            for i in (0..KETA).rev() {
                if self.digit[i] != 0 {
                    msd = i + 1;
                    break;
                }
            }
            msd
        };
        for i in 0..most_d {
            res = format!(
                "{}{}",
                format!("{:0RLENGTH$}", self.digit[i], RLENGTH = 9),
                res
            );
        }
        write!(f, "{}{}", self.sign, res)
    }
}

impl ops::Add<BigInt> for BigInt {
    type Output = BigInt;

    fn add(self, rhs: BigInt) -> BigInt {
        let result: BigInt;
        let mut resdigit: [u64; KETA] = [0; KETA];
        let mut carry: u64 = 0;
        // ignore 0 prefix
        let most_d: usize = {
            let mut msd: usize = KETA;
            for i in (0..KETA).rev() {
                if self.digit[i] != 0 || rhs.digit[i] != 0 {
                    msd = i + 1;
                    break;
                }
            }
            // carryがあるので+1
            std::cmp::min(msd + 1, KETA)
        };

        // + and +
        if self.sign == '+' && rhs.sign == '+' {
            for i in 0..most_d {
                let sum: u64 = self.digit[i] + rhs.digit[i] + carry;
                resdigit[i] = sum % RADIX;
                carry = if sum >= RADIX { 1 } else { 0 };
            }
            result = BigInt::from(resdigit);
        } else {
            panic!("unimplemented!");
        }
        if carry != 0 {
            panic!("overflow!");
        }
        println!("{} + {}", self, rhs);
        result
    }
}
#[test]
fn check_posi_posi_add() {
    println!("trivial addition");
    let a = BigInt::from([5; KETA]);
    let b = BigInt::from([5; KETA]);
    assert_eq!(a + b, BigInt::from([10; KETA]));
    println!("{}", a + b);
    println!("carry addition");
    println!("...500000000500000000 + ...500000000500000000 = ...1000000001000000000",);
    let mut a = BigInt::from([10u64.pow(9) / 2; KETA]);
    let mut b = BigInt::from([10u64.pow(9) / 2; KETA]);
    a.digit[KETA - 1] = 0;
    b.digit[KETA - 1] = 0;
    let mut expected = BigInt::from([1; KETA]);
    expected.digit[0] = 0;
    assert_eq!(a + b, expected);
    println!("{:?}", a + b);
}

impl ops::Mul<BigInt> for BigInt {
    type Output = BigInt;

    fn mul(self, rhs: BigInt) -> BigInt {
        // Unimplement
        println!("{} * {}", self, rhs);
        self
    }
}

impl BigInt {}

fn main() {
    let b0 = BigInt::new();
    println!("{}", b0);
    let b1 = BigInt::new();
    b0 + b1;
    b0 * b1;
}

mod tests {
    use super::*;
    #[test]
    fn check() {}
}
