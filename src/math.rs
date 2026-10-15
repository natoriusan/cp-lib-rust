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

pub const fn make_factorials<const N: usize>(modulo: usize) -> [usize; N] {
    let mut r = [1; N];
    let mut i = 1;
    while i < N {
        r[i] = (r[i-1] * i) % modulo;
        i += 1;
    }
    r
}

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


pub fn poly_sum(f: impl Fn(i64) -> i64, deg: usize, range: impl std::ops::RangeBounds<i64>) -> i64 {
    use std::ops::Bound::*;
    let l =
        match range.start_bound() {
            Included(&l) => l,
            Excluded(&l) => l+1,
            _ => unreachable!(),
        };
    let r =
        match range.end_bound() {
            Included(&r) => r+1,
            Excluded(&r) => r,
            _ => unreachable!(),
        };

    if l >= r {
        return 0;
    }

    let mut diff = vec![0; deg+2];
    for i in 0..deg+1 {
        diff[i+1] = diff[i] + f(l+i as i64);
    }

    let mut ret = diff[0];
    let mut c = 1;
    for i in 1..=deg+1 {
        for j in 0..deg+2-i {
            diff[j] = diff[j+1]-diff[j];
        }

        c *= r-l+1 - i as i64;
        c /= i as i64;
        ret += c * diff[0];
    }

    ret
}

pub fn poly_sum_mod<T: ac_library::modint::ModIntBase>(f: impl Fn(T) -> T, deg: usize, range: impl std::ops::RangeBounds<T>) -> T {
    use std::ops::Bound::*;
    let l =
        match range.start_bound() {
            Included(&l) => l,
            Excluded(&l) => l+T::new(1u32),
            _ => unreachable!(),
        };
    let r =
        match range.end_bound() {
            Included(&r) => r+T::new(1u32),
            Excluded(&r) => r,
            _ => unreachable!(),
        };

    let mut diff = vec![T::new(0u32); deg+2];
    for i in 0..deg+1 {
        diff[i+1] = diff[i] + f(l+T::new(i));
    }

    let mut ret = diff[0];
    let mut c = T::new(1u32);
    for i in 1..=deg+1 {
        for j in 0..deg+2-i {
            diff[j] = diff[j+1]-diff[j];
        }

        c *= r - l + T::new(1u32) - T::new(i);
        c /= T::new(i);
        ret += c * diff[0];
    }

    ret
}


pub struct DivisorLattice {
    pub n: u64,
    pub factors: std::collections::BTreeMap<u64, u32>,
}

impl DivisorLattice {
    pub fn new(n: u64) -> Self {
        let mut factors = std::collections::BTreeMap::new();
        {
            let mut n = n;
            let mut i = 2;
            while i*i <= n {
                while n.is_multiple_of(i) {
                    n /= i;
                    *factors.entry(i).or_insert(0) += 1;
                }
                i += 1;
            }
            if n > 1 {
                factors.insert(n, 1);
            }
        }

        Self {
            n,
            factors,
        }
    }

    pub fn with_spf(n: u64, spf: &[usize]) -> Self {
        let mut factors = std::collections::BTreeMap::new();
        {
            let mut n = n as usize;
            while n > 1 {
                *factors.entry(spf[n] as u64).or_insert(0) += 1;
                n /= spf[n];
            }
        }

        Self {
            n,
            factors,
        }
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.factors.values().map(|&i| i as usize+1).product()
    }

    pub fn lower_covers(&self, m: u64) -> impl Iterator<Item=u64> {
        debug_assert!(self.n.is_multiple_of(m));
        self.factors.keys().rev().filter(move |&&p| m.is_multiple_of(p)).map(move |&p| m/p)
    }

    pub fn upper_covers(&self, m: u64) -> impl Iterator<Item=u64> {
        debug_assert!(self.n.is_multiple_of(m));
        let div = self.n / m;
        self.factors.keys().filter(move |&&p| div.is_multiple_of(p)).map(move |&p| m*p)
    }

    pub fn lower_set(&self, mut m: u64) -> Vec<u64> {
        debug_assert!(self.n.is_multiple_of(m));
        let mut r = vec![];

        fn dfs(factors: &[(u64, u32)], r: &mut Vec<u64>, prod: u64, i: usize) {
            if i == factors.len() {
                r.push(prod);
                return;
            }

            let mut pow = 1;
            for _ in 0..=factors[i].1 {
                dfs(factors, r, prod*pow, i+1);
                pow = pow.wrapping_mul(factors[i].0);
            }
        }

        let mut factors = vec![];
        for &i in self.factors.keys() {
            let mut count = 0;
            while m.is_multiple_of(i) {
                m /= i;
                count += 1;
            }

            if count > 0 {
                factors.push((i, count));
            }
        }

        dfs(&factors, &mut r, 1, 0);
        r.sort_unstable();

        r
    }

    pub fn upper_set(&self, m: u64) -> Vec<u64> {
        debug_assert!(self.n.is_multiple_of(m));

        let mut r = self.lower_set(self.n/m);
        for i in &mut r {
            *i *= m;
        }

        r
    }

    pub fn euler_phi(&self, m: u64) -> u64 {
        debug_assert!(self.n.is_multiple_of(m));
        
        let mut r = m;
        for &p in self.factors.keys() {
            if m.is_multiple_of(p) {
                r -= r/p;
            }
        }
        
        r
    }
    
    pub fn mobius(&self, m: u64) -> i32 {
        debug_assert!(self.n.is_multiple_of(m));
        
        let mut r = 1;
        for &p in self.factors.keys() {
            if m.is_multiple_of(p) {
                if (m/p).is_multiple_of(p) {
                    return 0;
                }
                
                r = -r;
            }
        }
        
        r
    }
}


// .1は正でない場合cmpが正しくない場合がある
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
        (self.0 as i128 * other.1 as i128).cmp(&(other.0 as i128 * self.1 as i128))
    }
}

/// (-3/2 π, 1/2 π]の偏角で順序づけられた点
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Slope {
    Finite(Rational),
    Infinity,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArgPoint {
    Left(Slope),
    Right(Slope),
}

impl ArgPoint {
    pub fn new(x: i64, y: i64) -> Self {
        assert_ne!((x, y), (0, 0));
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
