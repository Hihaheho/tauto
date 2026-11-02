//! `Secret(A)` of `std/prelude/Secret.taut` (`docs/design/secret.md`): a
//! value whose content a program reads only through the functions here. Each
//! runs without a branch or a memory access that depends on a secret: a
//! choice is made with a mask, a comparison with the borrow or the carry of
//! a subtraction, and every mask passes through [`barrier`] so the compiler
//! cannot turn it back into a branch.

use std::hint::black_box;

/// A secret. It has no `PartialEq`, `Debug` or `Display`: the content leaves
/// only through [`expose`].
#[derive(Clone, Copy)]
pub struct Secret<T>(T);

/// A value the optimizer cannot see through: what it computes from it is
/// not specialized on what it might be.
#[inline(always)]
fn barrier(x: u64) -> u64 {
    black_box(x)
}

#[inline(always)]
fn mask(c: Secret<bool>) -> u64 {
    barrier(u64::from(c.0)).wrapping_neg()
}

#[inline(always)]
fn bool_of_bit(bit: u64) -> bool {
    barrier(bit) & 1 == 1
}

pub fn secret<T>(v: T) -> Secret<T> {
    Secret(v)
}

pub fn expose<T>(s: Secret<T>) -> T {
    s.0
}

macro_rules! words {
    ($($w:ident: $add:ident $sub:ident $mul:ident $and:ident $or:ident $xor:ident $not:ident
        $shl:ident $shr:ident $rotl:ident $rotr:ident $eq:ident $lt:ident $select:ident),* $(,)?) => {$(
        pub fn $add(a: Secret<$w>, b: Secret<$w>) -> Secret<$w> { Secret(a.0.wrapping_add(b.0)) }
        pub fn $sub(a: Secret<$w>, b: Secret<$w>) -> Secret<$w> { Secret(a.0.wrapping_sub(b.0)) }
        pub fn $mul(a: Secret<$w>, b: Secret<$w>) -> Secret<$w> { Secret(a.0.wrapping_mul(b.0)) }
        pub fn $and(a: Secret<$w>, b: Secret<$w>) -> Secret<$w> { Secret(a.0 & b.0) }
        pub fn $or(a: Secret<$w>, b: Secret<$w>) -> Secret<$w> { Secret(a.0 | b.0) }
        pub fn $xor(a: Secret<$w>, b: Secret<$w>) -> Secret<$w> { Secret(a.0 ^ b.0) }
        pub fn $not(a: Secret<$w>) -> Secret<$w> { Secret(!a.0) }
        // The amount is public: shifting by a register is a constant-time
        // instruction on the targets the backend writes for.
        pub fn $shl(a: Secret<$w>, s: u64) -> Secret<$w> {
            Secret(a.0.wrapping_shl((s % u64::from($w::BITS)) as u32))
        }
        pub fn $shr(a: Secret<$w>, s: u64) -> Secret<$w> {
            Secret(a.0.wrapping_shr((s % u64::from($w::BITS)) as u32))
        }
        pub fn $rotl(a: Secret<$w>, s: u64) -> Secret<$w> {
            Secret(a.0.rotate_left((s % u64::from($w::BITS)) as u32))
        }
        pub fn $rotr(a: Secret<$w>, s: u64) -> Secret<$w> {
            Secret(a.0.rotate_right((s % u64::from($w::BITS)) as u32))
        }
        /// The top bit of `x | -x` is set exactly when `x` is not zero.
        pub fn $eq(a: Secret<$w>, b: Secret<$w>) -> Secret<bool> {
            let x = u128::from(barrier(u64::from(a.0 ^ b.0)));
            Secret(bool_of_bit((((x | x.wrapping_neg()) >> 127) as u64) ^ 1))
        }
        /// The borrow of `a - b`, taken in a wider word.
        pub fn $lt(a: Secret<$w>, b: Secret<$w>) -> Secret<bool> {
            let d = u128::from(a.0).wrapping_sub(u128::from(b.0));
            Secret(bool_of_bit((d >> 127) as u64))
        }
        pub fn $select(c: Secret<bool>, a: Secret<$w>, b: Secret<$w>) -> Secret<$w> {
            let m = mask(c);
            Secret(((u64::from(a.0) & m) | (u64::from(b.0) & !m)) as $w)
        }
    )*};
}

words! {
    u8: ct_u8_add ct_u8_sub ct_u8_mul ct_u8_and ct_u8_or ct_u8_xor ct_u8_not
        ct_u8_shl ct_u8_shr ct_u8_rotl ct_u8_rotr ct_u8_eq ct_u8_lt ct_u8_select,
    u32: ct_u32_add ct_u32_sub ct_u32_mul ct_u32_and ct_u32_or ct_u32_xor ct_u32_not
        ct_u32_shl ct_u32_shr ct_u32_rotl ct_u32_rotr ct_u32_eq ct_u32_lt ct_u32_select,
    u64: ct_u64_add ct_u64_sub ct_u64_mul ct_u64_and ct_u64_or ct_u64_xor ct_u64_not
        ct_u64_shl ct_u64_shr ct_u64_rotl ct_u64_rotr ct_u64_eq ct_u64_lt ct_u64_select,
}

pub fn ct_u64_mul_hi(a: Secret<u64>, b: Secret<u64>) -> Secret<u64> {
    Secret(((u128::from(a.0) * u128::from(b.0)) >> 64) as u64)
}

pub fn ct_u64_of_u8(a: Secret<u8>) -> Secret<u64> {
    Secret(u64::from(a.0))
}

pub fn ct_u64_of_u32(a: Secret<u32>) -> Secret<u64> {
    Secret(u64::from(a.0))
}

pub fn ct_u32_of_u8(a: Secret<u8>) -> Secret<u32> {
    Secret(u32::from(a.0))
}

pub fn ct_u8_of_u32(a: Secret<u32>) -> Secret<u8> {
    Secret(a.0 as u8)
}

pub fn ct_u8_of_u64(a: Secret<u64>) -> Secret<u8> {
    Secret(a.0 as u8)
}

pub fn ct_u32_of_u64(a: Secret<u64>) -> Secret<u32> {
    Secret(a.0 as u32)
}

/// The length is public, as the length of every secret list is.
pub fn ct_bytes_len(s: Secret<crate::stdlib::Bytes>) -> u64 {
    s.0.len() as u64
}

/// The byte at a public index: the address depends only on `i`.
pub fn ct_bytes_get(s: Secret<crate::stdlib::Bytes>, i: u64) -> Option<Secret<u8>> {
    usize::try_from(i)
        .ok()
        .and_then(|i| s.0.get(i).copied())
        .map(Secret)
}

pub fn ct_bool_and(a: Secret<bool>, b: Secret<bool>) -> Secret<bool> {
    Secret(bool_of_bit(u64::from(a.0) & u64::from(b.0)))
}

pub fn ct_bool_or(a: Secret<bool>, b: Secret<bool>) -> Secret<bool> {
    Secret(bool_of_bit(u64::from(a.0) | u64::from(b.0)))
}

pub fn ct_bool_not(a: Secret<bool>) -> Secret<bool> {
    Secret(bool_of_bit(u64::from(a.0) ^ 1))
}

pub fn ct_bool_select(c: Secret<bool>, a: Secret<bool>, b: Secret<bool>) -> Secret<bool> {
    let m = mask(c);
    Secret(bool_of_bit((u64::from(a.0) & m) | (u64::from(b.0) & !m)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s<T>(v: T) -> Secret<T> {
        secret(v)
    }

    #[test]
    fn words_agree_with_plain_arithmetic() {
        let samples = [
            0u64,
            1,
            2,
            0x7f,
            0x80,
            0xff,
            0xffff_ffff,
            1 << 63,
            u64::MAX - 1,
            u64::MAX,
        ];
        for &a in &samples {
            for &b in &samples {
                assert_eq!(expose(ct_u64_eq(s(a), s(b))), a == b);
                assert_eq!(expose(ct_u64_lt(s(a), s(b))), a < b);
                let (a32, b32) = (a as u32, b as u32);
                assert_eq!(expose(ct_u32_eq(s(a32), s(b32))), a32 == b32);
                assert_eq!(expose(ct_u32_lt(s(a32), s(b32))), a32 < b32);
                let (a8, b8) = (a as u8, b as u8);
                assert_eq!(expose(ct_u8_lt(s(a8), s(b8))), a8 < b8);
                for c in [false, true] {
                    let want = if c { a } else { b };
                    assert_eq!(expose(ct_u64_select(s(c), s(a), s(b))), want);
                    assert_eq!(expose(ct_u8_select(s(c), s(a8), s(b8))), want as u8);
                }
                let wide = u128::from(a) * u128::from(b);
                assert_eq!(expose(ct_u64_mul_hi(s(a), s(b))), (wide >> 64) as u64);
                assert_eq!(expose(ct_u64_mul(s(a), s(b))), wide as u64);
            }
        }
    }

    #[test]
    fn bytes_one_by_one() {
        let b = s(crate::stdlib::Bytes::from(vec![7u8, 0, 255]));
        assert_eq!(ct_bytes_len(b.clone()), 3);
        assert_eq!(ct_bytes_get(b.clone(), 2).map(expose), Some(255));
        assert!(ct_bytes_get(b, 3).is_none());
    }

    #[test]
    fn booleans() {
        for a in [false, true] {
            assert_eq!(expose(ct_bool_not(s(a))), !a);
            for b in [false, true] {
                assert_eq!(expose(ct_bool_and(s(a), s(b))), a && b);
                assert_eq!(expose(ct_bool_or(s(a), s(b))), a || b);
                assert_eq!(expose(ct_bool_select(s(true), s(a), s(b))), a);
                assert_eq!(expose(ct_bool_select(s(false), s(a), s(b))), b);
            }
        }
    }
}
