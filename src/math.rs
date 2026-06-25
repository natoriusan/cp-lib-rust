#[allow(dead_code)]
pub fn factorial_mod<T: ac_library::modint::ModIntBase>(max: usize) -> (Vec<T>, Vec<T>) {
    use itertools::Itertools;

    let factorials = (0..=max).scan(T::new(1), |acc, i:usize| {
        if i != 0 {
            *acc *= T::new(i);
        }
        Some(*acc)
    }).collect_vec();
    let factorial_invs = (0..=max).rev().scan(factorials.last().unwrap().inv(), |acc, i| {
        let val = *acc;
        if i != 0 {
            *acc *= T::new(i);
        }
        Some(val)
    }).collect_vec().into_iter().rev().collect_vec();

    (factorials, factorial_invs)
}

#[allow(dead_code)]
pub const fn make_factorials<const N: usize>(modulo: usize) -> [usize; N] {
    let mut r = [1; N];
    let mut i = 1;
    while i < N {
        r[i] = (r[i-1] * i) % modulo;
        i += 1;
    }
    r
}

#[allow(dead_code)]
pub const fn make_factorial_invs<const N: usize>(modulo: usize) -> [usize; N] {
    const fn egcd(a: i64, b: i64) -> (i64, i64) {
        if b == 0 {
            (1, 0)
        } else {
            let (x, y) = egcd(b, a%b);
            (y, x-a/b*y)
        }
    }

    let mut fact = 1;
    {
        let mut i = 1;
        while i < N {
            fact = (fact*i) % modulo;
            i += 1;
        }
    }
    let inv = (egcd(fact as i64, modulo as i64).0 % modulo as i64 + modulo as i64) as usize % modulo;
    assert!((fact*inv) % modulo == 1);
    let mut r = [inv; N];
    let mut i = N-1;
    while i > 0 {
        r[i-1] = (r[i] * i) % modulo;
        i -= 1;
    }
    r
}


#[derive(Copy, Clone, Debug)]
pub struct Rational(i64, i64);

impl PartialEq for Rational {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for Rational {}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.0 * other.1).cmp(&(other.0 * self.1))
    }
}

#[allow(dead_code)]
/// (-3/2 π, 1/2 π]の偏角で順序づけられた点
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Slope {
    Finite(Rational),
    Infinity,
}

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArgPoint {
    Left(Slope),
    Right(Slope),
}

#[allow(dead_code)]
impl ArgPoint {
    pub fn new(x: i64, y: i64) -> Self {
        use Slope::*;
        use ArgPoint::*;
        if x == 0 {
            if y < 0 {
                Left(Infinity)
            } else {
                Right(Infinity)
            }
        } else if x < 0 {
            Left(Finite(Rational(y, x)))
        } else {
            Right(Finite(Rational(y, x)))
        }
    }
}
