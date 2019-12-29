use std::fmt;
use std::ops;
// 10u64.pow(9)
const KETA: usize = 100;
const RADIX: u64 = 1000000000;

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
//Display number
// +00000000
impl fmt::Display for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut res: String = String::new();
        res.push(self.sign);
        for b in self.digit.iter() {
            res = format!("{}{}", res, format!("{}", *b));
        }
        write!(f, "{}", res)
    }
}

impl ops::Add<BigInt> for BigInt {
    type Output = BigInt;

    fn add(self, rhs: BigInt) -> BigInt {
        // Unimplement
        println!("{} + {}", self, rhs);
        self
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

impl BigInt {
    fn getSign(&mut self) {}
    fn setInt(&mut self, x: u64) {}
    fn getInt(&mut self, x: u64) {}
    fn isPrime(&mut self) {}
    fn getAbs(&mut self) {}
}

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
