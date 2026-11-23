//! The numerals of the core: the natural numbers below `2^256`.
//!
//! A numeral stands for the `Nat` written with that many `Succ`s; the core
//! computes `+`, `*` and the definitions of [`super::core`]'s `NUMERIC` on
//! two numerals at once. A result past the largest numeral is left as it is
//! (`Core::past_limit`). 256 bits hold every product of two numbers below
//! `2^128`, so the bounds of the 128-bit integers and the products of their
//! values are computed.

use std::cmp::Ordering;
use std::fmt;

/// A natural number below `2^256`, in four 64-bit limbs, least significant
/// first.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Num([u64; 4]);

impl Num {
    pub const ZERO: Num = Num([0; 4]);
    pub const ONE: Num = Num([1, 0, 0, 0]);
    /// The largest numeral, `2^256 - 1`.
    pub const MAX: Num = Num([u64::MAX; 4]);

    pub const fn small(n: u64) -> Num {
        Num([n, 0, 0, 0])
    }

    pub const fn of_u128(n: u128) -> Num {
        Num([n as u64, (n >> 64) as u64, 0, 0])
    }

    /// The number as a `u128`, when it is below `2^128`.
    pub fn to_u128(self) -> Option<u128> {
        let [a, b, c, d] = self.0;
        (c == 0 && d == 0).then_some(((b as u128) << 64) | a as u128)
    }

    pub fn is_zero(self) -> bool {
        self == Num::ZERO
    }

    pub fn checked_add(self, other: Num) -> Option<Num> {
        let mut out = [0u64; 4];
        let mut carry = false;
        for (i, o) in out.iter_mut().enumerate() {
            let (s, c1) = self.0[i].overflowing_add(other.0[i]);
            let (s, c2) = s.overflowing_add(carry as u64);
            *o = s;
            carry = c1 || c2;
        }
        (!carry).then_some(Num(out))
    }

    /// `self - other`, or `None` when `other` is larger.
    pub fn checked_sub(self, other: Num) -> Option<Num> {
        let mut out = [0u64; 4];
        let mut borrow = false;
        for (i, o) in out.iter_mut().enumerate() {
            let (s, b1) = self.0[i].overflowing_sub(other.0[i]);
            let (s, b2) = s.overflowing_sub(borrow as u64);
            *o = s;
            borrow = b1 || b2;
        }
        (!borrow).then_some(Num(out))
    }

    /// `self - other`, or 0 when `other` is larger: `Nat`'s subtraction.
    pub fn saturating_sub(self, other: Num) -> Num {
        self.checked_sub(other).unwrap_or(Num::ZERO)
    }

    pub fn checked_mul(self, other: Num) -> Option<Num> {
        let mut out = [0u64; 8];
        for i in 0..4 {
            let mut carry: u128 = 0;
            for j in 0..4 {
                let cur = out[i + j] as u128 + self.0[i] as u128 * other.0[j] as u128 + carry;
                out[i + j] = cur as u64;
                carry = cur >> 64;
            }
            out[i + 4] = carry as u64;
        }
        out[4..]
            .iter()
            .all(|&l| l == 0)
            .then(|| Num([out[0], out[1], out[2], out[3]]))
    }

    fn bits(self) -> u32 {
        for i in (0..4).rev() {
            if self.0[i] != 0 {
                return 64 * i as u32 + (64 - self.0[i].leading_zeros());
            }
        }
        0
    }

    fn bit(self, i: u32) -> bool {
        (self.0[(i / 64) as usize] >> (i % 64)) & 1 == 1
    }

    fn shl1(self) -> Num {
        let mut out = [0u64; 4];
        let mut carry = 0;
        for (i, o) in out.iter_mut().enumerate() {
            *o = (self.0[i] << 1) | carry;
            carry = self.0[i] >> 63;
        }
        Num(out)
    }

    /// The quotient and remainder by a nonzero `d`, by long division one bit
    /// at a time.
    fn divrem(self, d: Num) -> Option<(Num, Num)> {
        if d.is_zero() {
            return None;
        }
        let mut q = Num::ZERO;
        let mut r = Num::ZERO;
        for i in (0..self.bits()).rev() {
            // `r < d` here, so `2r + 1 < 2d`, which is below `2^257`; the
            // top bit shifted out is kept in `over`.
            let over = r.bit(255);
            r = r.shl1();
            if self.bit(i) {
                r.0[0] |= 1;
            }
            if over || r >= d {
                r = r.wrapping_sub(d);
                q.0[(i / 64) as usize] |= 1 << (i % 64);
            }
        }
        Some((q, r))
    }

    fn wrapping_sub(self, other: Num) -> Num {
        let mut out = [0u64; 4];
        let mut borrow = false;
        for (i, o) in out.iter_mut().enumerate() {
            let (s, b1) = self.0[i].overflowing_sub(other.0[i]);
            let (s, b2) = s.overflowing_sub(borrow as u64);
            *o = s;
            borrow = b1 || b2;
        }
        Num(out)
    }

    pub fn checked_div(self, d: Num) -> Option<Num> {
        self.divrem(d).map(|(q, _)| q)
    }

    pub fn checked_rem(self, d: Num) -> Option<Num> {
        self.divrem(d).map(|(_, r)| r)
    }

    /// The number a numeral written in decimal is, when it is below `2^256`.
    pub fn parse(s: &str) -> Option<Num> {
        if s.is_empty() {
            return None;
        }
        let mut n = Num::ZERO;
        for c in s.chars() {
            let d = c.to_digit(10)?;
            n = n
                .checked_mul(Num::small(10))?
                .checked_add(Num::small(d as u64))?;
        }
        Some(n)
    }
}

impl From<u128> for Num {
    fn from(n: u128) -> Num {
        Num::of_u128(n)
    }
}

impl From<u64> for Num {
    fn from(n: u64) -> Num {
        Num::small(n)
    }
}

impl From<usize> for Num {
    fn from(n: usize) -> Num {
        Num::small(n as u64)
    }
}

impl Ord for Num {
    fn cmp(&self, other: &Num) -> Ordering {
        for i in (0..4).rev() {
            match self.0[i].cmp(&other.0[i]) {
                Ordering::Equal => {}
                o => return o,
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for Num {
    fn partial_cmp(&self, other: &Num) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// `self - other` where `other` is known not to be larger.
impl std::ops::Sub for Num {
    type Output = Num;
    fn sub(self, other: Num) -> Num {
        self.checked_sub(other)
            .expect("numeral subtraction below 0")
    }
}

impl std::ops::Add for Num {
    type Output = Num;
    fn add(self, other: Num) -> Num {
        self.checked_add(other).expect("numeral sum past 2^256")
    }
}

impl fmt::Display for Num {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(n) = self.to_u128() {
            return write!(f, "{n}");
        }
        let mut digits = Vec::new();
        let mut n = *self;
        let ten19 = Num::small(10_000_000_000_000_000_000);
        while !n.is_zero() {
            let (q, r) = n.divrem(ten19).expect("nonzero divisor");
            digits.push(r.0[0]);
            n = q;
        }
        let mut s = format!("{}", digits.pop().unwrap_or(0));
        for d in digits.iter().rev() {
            s.push_str(&format!("{d:019}"));
        }
        f.write_str(&s)
    }
}

impl fmt::Debug for Num {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::Num;

    #[test]
    fn arithmetic_agrees_with_u128_below_it_and_reaches_2_256() {
        let two128 = Num::of_u128(u128::MAX).checked_add(Num::ONE).unwrap();
        assert_eq!(
            two128.to_string(),
            "340282366920938463463374607431768211456"
        );
        let max = Num::MAX;
        assert_eq!(
            max.to_string(),
            "115792089237316195423570985008687907853269984665640564039457584007913129639935"
        );
        assert_eq!(Num::parse(&max.to_string()), Some(max));
        assert_eq!(max.checked_add(Num::ONE), None);
        let m = Num::of_u128(u128::MAX);
        let sq = m.checked_mul(m).unwrap();
        assert_eq!(sq.checked_div(m), Some(m));
        assert_eq!(sq.checked_rem(m), Some(Num::ZERO));
        assert_eq!(two128.checked_mul(two128), None);
        for (x, y) in [(17u128, 5u128), (u128::MAX, 3), (1 << 100, (1 << 64) + 7)] {
            let (a, b) = (Num::of_u128(x), Num::of_u128(y));
            assert_eq!(a.checked_div(b), Some(Num::of_u128(x / y)));
            assert_eq!(a.checked_rem(b), Some(Num::of_u128(x % y)));
            assert_eq!(a.saturating_sub(b), Num::of_u128(x.saturating_sub(y)));
            assert_eq!(a.cmp(&b), x.cmp(&y));
        }
        let big = sq.checked_add(Num::small(12345)).unwrap();
        assert_eq!(big.checked_rem(m), Some(Num::small(12345)));
    }
}
