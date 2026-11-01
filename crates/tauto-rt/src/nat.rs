//! `nat`: a natural number of any size. A value that fits in a `u64` is held
//! inline, so the small numbers that indices and sizes use cost no
//! allocation; a larger one is base-2^32 digits from the least significant,
//! with no zero digit at the top. Every value has exactly one form, so the
//! derived equality and hash agree with the number.

use std::cmp::Ordering;
use std::fmt;

use crate::Rc;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Nat(Repr);

#[derive(Clone, PartialEq, Eq, Hash)]
enum Repr {
    Small(u64),
    /// Always more than `u64::MAX`, so at least three digits.
    Big(Rc<Vec<u32>>),
}

impl Default for Nat {
    fn default() -> Nat {
        Nat::zero()
    }
}

impl Nat {
    fn of(mut digits: Vec<u32>) -> Nat {
        while digits.last() == Some(&0) {
            digits.pop();
        }
        match digits.as_slice() {
            [] => Nat::from_u64(0),
            [a] => Nat::from_u64(u64::from(*a)),
            [a, b] => Nat::from_u64(u64::from(*a) | u64::from(*b) << 32),
            _ => Nat(Repr::Big(Rc::new(digits))),
        }
    }

    /// The base-2^32 digits, for the paths that work on any size.
    fn digits(&self) -> Vec<u32> {
        match &self.0 {
            Repr::Small(0) => Vec::new(),
            Repr::Small(n) if *n >> 32 == 0 => vec![*n as u32],
            Repr::Small(n) => vec![*n as u32, (n >> 32) as u32],
            Repr::Big(d) => d.as_ref().clone(),
        }
    }

    pub fn zero() -> Nat {
        Nat(Repr::Small(0))
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.0, Repr::Small(0))
    }

    pub fn from_u64(n: u64) -> Nat {
        Nat(Repr::Small(n))
    }

    pub fn to_u64(&self) -> Option<u64> {
        match self.0 {
            Repr::Small(n) => Some(n),
            Repr::Big(_) => None,
        }
    }

    /// The number a string of decimal digits writes.
    pub fn parse(s: &str) -> Option<Nat> {
        if s.is_empty() {
            return None;
        }
        let mut n = Nat::zero();
        for c in s.chars() {
            let d = c.to_digit(10)?;
            n = n.mul_small(10).add(&Nat::from_u64(u64::from(d)));
        }
        Some(n)
    }

    pub fn add(&self, b: &Nat) -> Nat {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.0, &b.0) {
            if let Some(s) = x.checked_add(*y) {
                return Nat::from_u64(s);
            }
        }
        let (x, y) = (&self.digits(), &b.digits());
        let mut out = Vec::with_capacity(x.len().max(y.len()) + 1);
        let mut carry = 0u64;
        for i in 0..x.len().max(y.len()) {
            let s = u64::from(*x.get(i).unwrap_or(&0)) + u64::from(*y.get(i).unwrap_or(&0)) + carry;
            out.push(s as u32);
            carry = s >> 32;
        }
        out.push(carry as u32);
        Nat::of(out)
    }

    /// `self - b`, or `None` when `b` is larger.
    pub fn sub(&self, b: &Nat) -> Option<Nat> {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.0, &b.0) {
            return x.checked_sub(*y).map(Nat::from_u64);
        }
        if self < b {
            return None;
        }
        let (x, y) = (&self.digits(), &b.digits());
        let mut out = Vec::with_capacity(x.len());
        let mut borrow = 0i64;
        for i in 0..x.len() {
            let mut d = i64::from(x[i]) - i64::from(*y.get(i).unwrap_or(&0)) - borrow;
            borrow = 0;
            if d < 0 {
                d += 1 << 32;
                borrow = 1;
            }
            out.push(d as u32);
        }
        Some(Nat::of(out))
    }

    pub fn mul(&self, b: &Nat) -> Nat {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.0, &b.0) {
            if let Some(p) = x.checked_mul(*y) {
                return Nat::from_u64(p);
            }
        }
        let (x, y) = (&self.digits(), &b.digits());
        if x.is_empty() || y.is_empty() {
            return Nat::zero();
        }
        let mut out = vec![0u32; x.len() + y.len()];
        for (i, &a) in x.iter().enumerate() {
            let mut carry = 0u64;
            for (j, &c) in y.iter().enumerate() {
                let t = u64::from(a) * u64::from(c) + u64::from(out[i + j]) + carry;
                out[i + j] = t as u32;
                carry = t >> 32;
            }
            out[i + y.len()] = carry as u32;
        }
        Nat::of(out)
    }

    fn mul_small(&self, m: u32) -> Nat {
        self.mul(&Nat::from_u64(u64::from(m)))
    }

    /// The quotient and remainder of a division by `d`, which is not zero.
    fn divmod_small(&self, d: u32) -> (Nat, u32) {
        if let Repr::Small(n) = self.0 {
            return (Nat::from_u64(n / u64::from(d)), (n % u64::from(d)) as u32);
        }
        let x = self.digits();
        let mut out = vec![0u32; x.len()];
        let mut r = 0u64;
        for i in (0..x.len()).rev() {
            let t = r << 32 | u64::from(x[i]);
            out[i] = (t / u64::from(d)) as u32;
            r = t % u64::from(d);
        }
        (Nat::of(out), r as u32)
    }

    fn bits(&self) -> usize {
        match &self.0 {
            Repr::Small(n) => 64 - n.leading_zeros() as usize,
            Repr::Big(d) => 32 * (d.len() - 1) + (32 - d[d.len() - 1].leading_zeros() as usize),
        }
    }

    fn bit(&self, i: usize) -> bool {
        match &self.0 {
            Repr::Small(n) => i < 64 && n >> i & 1 == 1,
            Repr::Big(d) => d.get(i / 32).is_some_and(|d| d >> (i % 32) & 1 == 1),
        }
    }

    /// The quotient and remainder of a division by `d`; `None` when `d` is
    /// zero.
    pub fn divmod(&self, d: &Nat) -> Option<(Nat, Nat)> {
        if d.is_zero() {
            return None;
        }
        if let (Repr::Small(x), Repr::Small(y)) = (&self.0, &d.0) {
            return Some((Nat::from_u64(x / y), Nat::from_u64(x % y)));
        }
        if let Repr::Small(small) = d.0 {
            if small >> 32 == 0 {
                let (q, r) = self.divmod_small(small as u32);
                return Some((q, Nat::from_u64(u64::from(r))));
            }
        }
        if self < d {
            return Some((Nat::zero(), self.clone()));
        }
        // Long division, one bit at a time.
        let n = self.bits();
        let mut q = vec![0u32; n / 32 + 1];
        let mut r = Nat::zero();
        for i in (0..n).rev() {
            r = r.add(&r);
            if self.bit(i) {
                r = r.add(&Nat::from_u64(1));
            }
            if let Some(next) = r.sub(d) {
                r = next;
                q[i / 32] |= 1 << (i % 32);
            }
        }
        Some((Nat::of(q), r))
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, b: &Nat) -> Option<Ordering> {
        Some(self.cmp(b))
    }
}

impl Ord for Nat {
    fn cmp(&self, b: &Nat) -> Ordering {
        match (&self.0, &b.0) {
            (Repr::Small(x), Repr::Small(y)) => x.cmp(y),
            (Repr::Small(_), Repr::Big(_)) => Ordering::Less,
            (Repr::Big(_), Repr::Small(_)) => Ordering::Greater,
            (Repr::Big(x), Repr::Big(y)) => x
                .len()
                .cmp(&y.len())
                .then_with(|| x.iter().rev().cmp(y.iter().rev())),
        }
    }
}

impl fmt::Display for Nat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Repr::Small(n) = self.0 {
            return write!(f, "{n}");
        }
        // Nine decimal digits at a time.
        let mut parts = Vec::new();
        let mut n = self.clone();
        while !n.is_zero() {
            let (q, r) = n.divmod_small(1_000_000_000);
            parts.push(r);
            n = q;
        }
        let mut out = parts.pop().unwrap().to_string();
        for p in parts.iter().rev() {
            out.push_str(&format!("{p:09}"));
        }
        f.write_str(&out)
    }
}

impl fmt::Debug for Nat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::Nat;

    fn n(s: &str) -> Nat {
        Nat::parse(s).unwrap()
    }

    #[test]
    fn arithmetic_on_large_numbers() {
        let a = n("340282366920938463463374607431768211457");
        let b = n("18446744073709551629");
        assert_eq!(
            a.add(&b).to_string(),
            "340282366920938463481821351505477763086"
        );
        assert_eq!(
            a.sub(&b).unwrap().to_string(),
            "340282366920938463444927863358058659828"
        );
        assert!(b.sub(&a).is_none());
        assert_eq!(
            a.mul(&b).to_string(),
            "6277101735386680768259460193179866441144672085150730813453"
        );
        let (q, r) = a.divmod(&b).unwrap();
        assert_eq!(q.mul(&b).add(&r), a);
        assert!(r < b);
        assert_eq!(q.to_string(), "18446744073709551603");
        assert_eq!(Nat::from_u64(u64::MAX).to_string(), "18446744073709551615");
        assert_eq!(n("18446744073709551616").to_u64(), None);
        assert_eq!(n("0").to_string(), "0");
        assert!(n("7").divmod(&Nat::zero()).is_none());
        assert_eq!(n("1000000000").to_string(), "1000000000");
    }

    #[test]
    fn crossing_the_u64_boundary_keeps_one_form() {
        let max = Nat::from_u64(u64::MAX);
        let one = Nat::from_u64(1);
        let over = max.add(&one);
        assert_eq!(over, n("18446744073709551616"));
        assert_eq!(over.to_u64(), None);
        assert_eq!(over.sub(&one).unwrap(), max);
        assert_eq!(over.sub(&one).unwrap().to_u64(), Some(u64::MAX));
        assert!(max < over);
        assert_eq!(
            max.mul(&Nat::from_u64(2))
                .divmod(&Nat::from_u64(2))
                .unwrap()
                .0,
            max
        );
        let big_d = Nat::from_u64(1 << 40);
        let (q, r) = over.divmod(&big_d).unwrap();
        assert_eq!((q.to_u64(), r.to_u64()), (Some(1 << 24), Some(0)));
        assert_eq!(
            Nat::from_u64(7).divmod(&big_d).unwrap(),
            (Nat::zero(), Nat::from_u64(7))
        );
        assert_eq!(Nat::default(), Nat::zero());
    }
}
