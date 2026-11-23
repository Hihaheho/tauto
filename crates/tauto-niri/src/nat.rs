//! Natural numbers of any size, for `Nat` values past `i128`: the evaluator
//! has no bound, and niri must not stop where it does not.

use std::cmp::Ordering;

/// Little-endian base 2^32 digits, no leading zeros.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BigNat(Vec<u32>);

impl BigNat {
    pub fn of_i128(n: i128) -> Option<BigNat> {
        if n < 0 {
            return None;
        }
        let mut n = n as u128;
        let mut d = Vec::new();
        while n > 0 {
            d.push(n as u32);
            n >>= 32;
        }
        Some(BigNat(d))
    }

    pub fn to_i128(&self) -> Option<i128> {
        if self.0.len() > 3 {
            return None;
        }
        let mut n: u128 = 0;
        for d in self.0.iter().rev() {
            n = (n << 32) | u128::from(*d);
        }
        i128::try_from(n).ok()
    }

    fn trim(mut self) -> BigNat {
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
        self
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    pub fn add(&self, o: &BigNat) -> BigNat {
        let mut out = Vec::with_capacity(self.0.len().max(o.0.len()) + 1);
        let mut carry = 0u64;
        for i in 0..self.0.len().max(o.0.len()) {
            let s = u64::from(*self.0.get(i).unwrap_or(&0))
                + u64::from(*o.0.get(i).unwrap_or(&0))
                + carry;
            out.push(s as u32);
            carry = s >> 32;
        }
        out.push(carry as u32);
        BigNat(out).trim()
    }

    /// `self - o`, or `None` below zero.
    pub fn sub(&self, o: &BigNat) -> Option<BigNat> {
        if self.cmp(o) == Ordering::Less {
            return None;
        }
        let mut out = Vec::with_capacity(self.0.len());
        let mut borrow = 0i64;
        for (i, a) in self.0.iter().enumerate() {
            let mut d = i64::from(*a) - i64::from(*o.0.get(i).unwrap_or(&0)) - borrow;
            borrow = 0;
            if d < 0 {
                d += 1 << 32;
                borrow = 1;
            }
            out.push(d as u32);
        }
        Some(BigNat(out).trim())
    }

    pub fn mul(&self, o: &BigNat) -> BigNat {
        let mut out = vec![0u32; self.0.len() + o.0.len() + 1];
        for (i, a) in self.0.iter().enumerate() {
            let mut carry = 0u64;
            for (j, b) in o.0.iter().enumerate() {
                let t = u64::from(*a) * u64::from(*b) + u64::from(out[i + j]) + carry;
                out[i + j] = t as u32;
                carry = t >> 32;
            }
            let mut k = i + o.0.len();
            while carry > 0 {
                let t = u64::from(out[k]) + carry;
                out[k] = t as u32;
                carry = t >> 32;
                k += 1;
            }
        }
        BigNat(out).trim()
    }

    /// The quotient and remainder, by bits; `None` for a zero divisor.
    pub fn divmod(&self, o: &BigNat) -> Option<(BigNat, BigNat)> {
        if o.is_zero() {
            return None;
        }
        let mut q = BigNat(vec![0; self.0.len()]);
        let mut r = BigNat(Vec::new());
        for i in (0..self.0.len() * 32).rev() {
            r = r.add(&r);
            if self.0[i / 32] >> (i % 32) & 1 == 1 {
                r = r.add(&BigNat(vec![1]));
            }
            if let Some(s) = r.sub(o) {
                r = s;
                q.0[i / 32] |= 1 << (i % 32);
            }
        }
        Some((q.trim(), r))
    }

    fn divmod_small(&self, d: u32) -> (BigNat, u32) {
        let mut out = vec![0u32; self.0.len()];
        let mut rem = 0u64;
        for i in (0..self.0.len()).rev() {
            let cur = (rem << 32) | u64::from(self.0[i]);
            out[i] = (cur / u64::from(d)) as u32;
            rem = cur % u64::from(d);
        }
        (BigNat(out).trim(), rem as u32)
    }
}

impl Ord for BigNat {
    fn cmp(&self, o: &BigNat) -> Ordering {
        self.0
            .len()
            .cmp(&o.0.len())
            .then_with(|| self.0.iter().rev().cmp(o.0.iter().rev()))
    }
}

impl PartialOrd for BigNat {
    fn partial_cmp(&self, o: &BigNat) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl std::fmt::Display for BigNat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_zero() {
            return f.write_str("0");
        }
        let mut parts = Vec::new();
        let mut n = self.clone();
        while !n.is_zero() {
            let (q, r) = n.divmod_small(1_000_000_000);
            parts.push(r);
            n = q;
        }
        write!(f, "{}", parts.pop().unwrap())?;
        for p in parts.iter().rev() {
            write!(f, "{p:09}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big(s: &str) -> BigNat {
        let mut n = BigNat(Vec::new());
        for c in s.chars() {
            n = n
                .mul(&BigNat::of_i128(10).unwrap())
                .add(&BigNat::of_i128(i128::from(c.to_digit(10).unwrap())).unwrap());
        }
        n
    }

    #[test]
    fn arithmetic_past_i128() {
        let a = big("340282366920938463463374607431768211457");
        let b = big("18446744073709551629");
        assert_eq!(a.to_string(), "340282366920938463463374607431768211457");
        assert_eq!(a.add(&b).sub(&b), Some(a.clone()));
        let (q, r) = a
            .mul(&b)
            .add(&BigNat::of_i128(5).unwrap())
            .divmod(&b)
            .unwrap();
        assert_eq!((q, r.to_i128()), (a.clone(), Some(5)));
        assert_eq!(b.sub(&a), None);
        assert_eq!(a.to_i128(), None);
        assert_eq!(big("12345").to_i128(), Some(12345));
    }
}
