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
    i32: add_i32 sub_i32 mul_i32 div_i32 rem_i32 neg_i32,
    i64: add_i64 sub_i64 mul_i64 div_i64 rem_i64 neg_i64,
    u8: add_u8 sub_u8 mul_u8 div_u8 rem_u8 neg_u8,
    u32: add_u32 sub_u32 mul_u32 div_u32 rem_u32 neg_u32,
    u64: add_u64 sub_u64 mul_u64 div_u64 rem_u64 neg_u64,
}

/// `nat`'s operations. A `nat` does not overflow; a difference below zero is
/// the run-time error of an overflow, as it is for the unsigned widths.
pub fn add_nat(a: Nat, b: Nat, _at: Loc) -> Nat {
    a.add(&b)
}
pub fn sub_nat(a: Nat, b: Nat, at: Loc) -> Nat {
    a.sub(&b).unwrap_or_else(|| error(messages::TOO_LARGE, at))
}
pub fn mul_nat(a: Nat, b: Nat, _at: Loc) -> Nat {
    a.mul(&b)
}
pub fn div_nat(a: Nat, b: Nat, at: Loc) -> Nat {
    match a.divmod(&b) {
        Some((q, _)) => q,
        None => error(messages::DIVISION_BY_ZERO, at),
    }
}
pub fn rem_nat(a: Nat, b: Nat, at: Loc) -> Nat {
    match a.divmod(&b) {
        Some((_, r)) => r,
        None => error(messages::DIVISION_BY_ZERO, at),
    }
}
pub fn neg_nat(a: Nat, at: Loc) -> Nat {
    sub_nat(Nat::zero(), a, at)
}
