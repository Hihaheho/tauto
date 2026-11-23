//! Checked integer operations; an overflow is the run-time error
//! `the number is too large`, and a division by zero is `division by zero`.

use crate::nat::Nat;
use crate::{Loc, error, messages};

macro_rules! ops {
    ($($ty:ident: $add:ident $sub:ident $mul:ident $div:ident $rem:ident $neg:ident),* $(,)?) => {$(
        pub fn $add(a: $ty, b: $ty, at: Loc) -> $ty {
            a.checked_add(b).unwrap_or_else(|| error(messages::TOO_LARGE, at))
        }
        pub fn $sub(a: $ty, b: $ty, at: Loc) -> $ty {
            a.checked_sub(b).unwrap_or_else(|| error(messages::TOO_LARGE, at))
        }
        pub fn $mul(a: $ty, b: $ty, at: Loc) -> $ty {
            a.checked_mul(b).unwrap_or_else(|| error(messages::TOO_LARGE, at))
        }
        pub fn $div(a: $ty, b: $ty, at: Loc) -> $ty {
            if b == 0 {
                error(messages::DIVISION_BY_ZERO, at);
            }
            a.checked_div(b).unwrap_or_else(|| error(messages::TOO_LARGE, at))
        }
        pub fn $rem(a: $ty, b: $ty, at: Loc) -> $ty {
            if b == 0 {
                error(messages::DIVISION_BY_ZERO, at);
            }
            a.checked_rem(b).unwrap_or_else(|| error(messages::TOO_LARGE, at))
        }
        pub fn $neg(a: $ty, at: Loc) -> $ty {
            (0 as $ty).checked_sub(a).unwrap_or_else(|| error(messages::TOO_LARGE, at))
        }
    )*};
}

ops! {
    i8: add_i8 sub_i8 mul_i8 div_i8 rem_i8 neg_i8,
    i16: add_i16 sub_i16 mul_i16 div_i16 rem_i16 neg_i16,
    u16: add_u16 sub_u16 mul_u16 div_u16 rem_u16 neg_u16,
    i32: add_i32 sub_i32 mul_i32 div_i32 rem_i32 neg_i32,
    i64: add_i64 sub_i64 mul_i64 div_i64 rem_i64 neg_i64,
    u8: add_u8 sub_u8 mul_u8 div_u8 rem_u8 neg_u8,
    u32: add_u32 sub_u32 mul_u32 div_u32 rem_u32 neg_u32,
    u64: add_u64 sub_u64 mul_u64 div_u64 rem_u64 neg_u64,
}

/// `nat`'s operations. A `nat` does not overflow; a difference below zero is
/// the run-time error of an overflow, as it is for the unsigned widths.
#[inline(always)]
pub fn add_nat(a: Nat, b: Nat, at: Loc) -> Nat {
    if let (Some(x), Some(y)) = (a.to_u64(), b.to_u64())
        && let Some(s) = x.checked_add(y)
    {
        return Nat::from_u64(s);
    }
    add_nat_big(a, b, at)
}
#[inline(never)]
fn add_nat_big(a: Nat, b: Nat, _at: Loc) -> Nat {
    a.add(&b)
}
#[inline(always)]
pub fn sub_nat(a: Nat, b: Nat, at: Loc) -> Nat {
    if let (Some(x), Some(y)) = (a.to_u64(), b.to_u64())
        && let Some(s) = x.checked_sub(y)
    {
        return Nat::from_u64(s);
    }
    sub_nat_big(a, b, at)
}
#[inline(never)]
fn sub_nat_big(a: Nat, b: Nat, at: Loc) -> Nat {
    a.sub(&b).unwrap_or_else(|| error(messages::TOO_LARGE, at))
}
#[inline]
pub fn mul_nat(a: Nat, b: Nat, _at: Loc) -> Nat {
    a.mul(&b)
}
#[inline]
pub fn div_nat(a: Nat, b: Nat, at: Loc) -> Nat {
    match a.divmod(&b) {
        Some((q, _)) => q,
        None => error(messages::DIVISION_BY_ZERO, at),
    }
}
#[inline]
pub fn rem_nat(a: Nat, b: Nat, at: Loc) -> Nat {
    match a.divmod(&b) {
        Some((_, r)) => r,
        None => error(messages::DIVISION_BY_ZERO, at),
    }
}

/// The operations of a width as `None` where the result does not exist: what
/// code that performs `overflow` checks before it performs it.
macro_rules! checked_ops {
    ($($ty:ident: $add:ident $sub:ident $mul:ident $neg:ident),* $(,)?) => {$(
        #[inline(always)]
        pub fn $add(a: $ty, b: $ty) -> Option<$ty> {
            a.checked_add(b)
        }
        #[inline(always)]
        pub fn $sub(a: $ty, b: $ty) -> Option<$ty> {
            a.checked_sub(b)
        }
        #[inline(always)]
        pub fn $mul(a: $ty, b: $ty) -> Option<$ty> {
            a.checked_mul(b)
        }
        #[inline(always)]
        pub fn $neg(a: $ty) -> Option<$ty> {
            (0 as $ty).checked_sub(a)
        }
    )*};
}

checked_ops! {
    i8: checked_add_i8 checked_sub_i8 checked_mul_i8 checked_neg_i8,
    i16: checked_add_i16 checked_sub_i16 checked_mul_i16 checked_neg_i16,
    u16: checked_add_u16 checked_sub_u16 checked_mul_u16 checked_neg_u16,
    i32: checked_add_i32 checked_sub_i32 checked_mul_i32 checked_neg_i32,
    i64: checked_add_i64 checked_sub_i64 checked_mul_i64 checked_neg_i64,
    u8: checked_add_u8 checked_sub_u8 checked_mul_u8 checked_neg_u8,
    u32: checked_add_u32 checked_sub_u32 checked_mul_u32 checked_neg_u32,
    u64: checked_add_u64 checked_sub_u64 checked_mul_u64 checked_neg_u64,
}

#[inline]
pub fn checked_add_nat(a: Nat, b: Nat) -> Option<Nat> {
    Some(a.add(&b))
}
#[inline]
pub fn checked_sub_nat(a: Nat, b: Nat) -> Option<Nat> {
    a.sub(&b)
}
#[inline]
pub fn checked_mul_nat(a: Nat, b: Nat) -> Option<Nat> {
    Some(a.mul(&b))
}
#[inline]
pub fn checked_neg_nat(a: Nat) -> Option<Nat> {
    Nat::from_u64(0).sub(&a)
}
