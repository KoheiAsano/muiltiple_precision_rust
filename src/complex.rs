use std::ops;
#[derive(Clone, Copy, Debug)]
pub struct Complex {
    re: f64,
    im: f64,
}

// constructors
#[allow(dead_code)]
impl Complex {
    pub fn new(re: f64, im: f64) -> Self {
        Complex { re: re, im: im }
    }
    pub fn zero() -> Self {
        Complex { re: 0.0, im: 0.0 }
    }
    pub fn i() -> Self {
        Complex { re: 0.0, im: 1.0 }
    }
    pub fn root(n: usize) -> Self {
        Complex {
            re: (2.0 * std::f64::consts::PI / n as f64).cos(),
            im: (2.0 * std::f64::consts::PI / n as f64).sin(),
        }
    }
}

impl PartialEq for Complex {
    fn eq(&self, other: &Complex) -> bool {
        (self.re - other.re).abs() < 10e-9 && (self.im - other.im).abs() < 10e-9
    }
}

// Operations
impl ops::Add<Complex> for Complex {
    type Output = Self;
    fn add(self, rhs: Complex) -> Self::Output {
        Complex {
            re: self.re + rhs.re,
            im: self.im + rhs.im,
        }
    }
}
impl ops::AddAssign<Complex> for Complex {
    fn add_assign(&mut self, rhs: Complex) {
        *self = *self + rhs;
    }
}

impl ops::Mul<Complex> for Complex {
    type Output = Self;
    fn mul(self, rhs: Complex) -> Self::Output {
        Complex {
            re: self.re * rhs.re - self.im * rhs.im,
            im: self.re * rhs.im + self.im * rhs.re,
        }
    }
}
impl ops::MulAssign<Complex> for Complex {
    fn mul_assign(&mut self, rhs: Complex) {
        *self = *self * rhs;
    }
}

impl ops::Div<Complex> for Complex {
    type Output = Self;
    fn div(self, rhs: Complex) -> Self::Output {
        let denomi = self.im.powf(2.0) + rhs.im.powf(2.0);
        Complex {
            re: (self.re * rhs.re + self.im * rhs.im) / denomi,
            im: (self.re * rhs.im + self.im * rhs.re) / denomi,
        }
    }
}
impl ops::DivAssign<Complex> for Complex {
    fn div_assign(&mut self, rhs: Complex) {
        *self = *self / rhs;
    }
}

// operations to primitive numbers
macro_rules! impl_ops {
    ($I:ty) => {
        impl ops::Add<$I> for Complex {
            type Output = Self;
            fn add(self, rhs: $I) -> Self::Output {
                Complex {
                    re: self.re + rhs as f64,
                    im: self.im,
                }
            }
        }
        impl ops::AddAssign<$I> for Complex {
            fn add_assign(&mut self, rhs: $I) {
                *self = *self + rhs as f64;
            }
        }

        impl ops::Mul<$I> for Complex {
            type Output = Self;
            fn mul(self, rhs: $I) -> Self::Output {
                Complex {
                    re: self.re * rhs as f64,
                    im: self.im * rhs as f64,
                }
            }
        }
        impl ops::MulAssign<$I> for Complex {
            fn mul_assign(&mut self, rhs: $I) {
                *self = *self * rhs as f64;
            }
        }

        impl ops::Div<$I> for Complex {
            type Output = Self;
            fn div(self, rhs: $I) -> Self::Output {
                Complex {
                    re: self.re / rhs as f64,
                    im: self.im / rhs as f64,
                }
            }
        }
        impl ops::DivAssign<$I> for Complex {
            fn div_assign(&mut self, rhs: $I) {
                *self = *self / rhs;
            }
        }
    };
}
impl_ops!(f64);
impl_ops!(usize);

// convert from primitives
macro_rules! impl_from {
    ($T:ty) => {
        impl From<$T> for Complex {
            fn from(n: $T) -> Self {
                Complex {
                    re: n as f64,
                    im: 0.0,
                }
            }
        }
    };
}

impl_from!(f64);
impl_from!(u64);
impl_from!(i64);

// additional operations
#[allow(dead_code)]
impl Complex {
    pub fn pow(self, mut n: usize) -> Self {
        let mut ret = Complex::new(1.0, 0.0);
        let mut base = self;
        while n > 0 {
            if n & 1 == 1 {
                ret *= base;
            }
            base *= base;
            n >>= 1;
        }
        ret
    }
    pub fn conj(self) -> Self {
        Complex {
            re: self.re,
            im: -self.im,
        }
    }
}

mod tests {
    #[allow(unused_imports)]
    use super::*;
    #[test]
    pub fn check_i() {
        let i = Complex::i();
        assert_eq!(i.pow(2).re, -1.0);
        assert_eq!(i.pow(3).re, 0.0);
        assert_eq!(i.pow(4).re, 1.0);
    }
    #[test]
    pub fn check_root() {
        let n = 11;
        let root = Complex::root(n);
        assert_eq!(root.pow(n).re, 1.0);
        // orthogonality
        for i in 0..n {
            assert_eq!(root.pow(n + i), root.pow(i));
        }
    }
    #[test]
    pub fn check_ops_with_primitives() {
        // addition
        let mut z = Complex::zero();
        assert_eq!(z + 1, Complex::new(1.0, 0.0));
        z += 1;
        assert_eq!(z, Complex::new(1.0, 0.0));
        assert_eq!(z / 4, Complex::new(0.25, 0.0));
        z /= 4;
        assert_eq!(z, Complex::new(0.25, 0.0));
        // multiplication
        let mut i = Complex::i();
        assert_eq!(i * 4, Complex::new(0.0, 4.0));
        i *= 4;
        assert_eq!(i, Complex::new(0.0, 4.0));
        // division
        let mut i = Complex::i();
        assert_eq!(i / 4, Complex::new(0.0, 0.25));
        i /= 4;
        assert_eq!(i, Complex::new(0.0, 0.25));
    }

}


fn dft(mut a: Vec<Complex>, n: usize, inv: bool) -> Vec<Complex> {
    if n == 1 {
        return a;
    }
    let mut f: Vec<Complex> = vec![];
    let mut g: Vec<Complex> = vec![];
    for i in 0..n / 2 {
        f.push(a[2 * i]);
        g.push(a[2 * i + 1]);
    }
    f = dft(f, n / 2, inv);
    g = dft(g, n / 2, inv);

    let zeta: Complex = if inv {
        Complex::root(n).conj()
    } else {
        Complex::root(n)
    };
    let mut p = Complex::new(1.0, 0.0);
    for i in 0..n {
        a[i] = f[i % (n / 2)] + p * g[i % (n / 2)];
        p *= zeta;
    }
    return a;
}

fn idft(mut a: Vec<Complex>, n: usize) -> Vec<Complex> {
    a = dft(a, n, true);
    for i in 0..n {
        a[i] /= n;
    }
    a
}

// impl_from_f64!(i64);
macro_rules! t_convolution {
    ($T:ty) => {
        pub fn convolution(a: Vec<$T>, b: Vec<$T>) -> Vec<$T>
        where
            Complex: From<$T>,
        {
            // T to Complex
            let mut a: Vec<Complex> = a.iter().map(|e| Complex::from(*e)).collect();
            let mut b: Vec<Complex> = b.iter().map(|e| Complex::from(*e)).collect();
            // length is degree + 1, result is a-deg + b-deg degree
            let d: usize = a.len() + b.len() - 1;
            let n = d.checked_next_power_of_two().unwrap();
            a.resize(n, Complex::zero());
            b.resize(n, Complex::zero());

            a = dft(a, n, false);
            b = dft(b, n, false);
            let mut f: Vec<Complex> = vec![];
            for i in 0..n {
                f.push(a[i] * b[i]);
            }
            f = idft(f, n);
            f.truncate(d);
            f.iter()
                .map(|e| {
                    if e.re > 0.0 {
                        (e.re + 0.5) as $T
                    } else {
                        (e.re - 0.5) as $T
                    }
                })
                .collect::<Vec<$T>>()
        }
    };
}

t_convolution!(u64);