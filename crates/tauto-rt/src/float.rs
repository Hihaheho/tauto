//! `Float` (IEEE 754 binary64): its literals, its `/`, how it is shown, and
//! the functions of `std/prelude/Num.taut`, shared with the evaluator
//! (`crates/tauto-eval/src/eval.rs`) so that the two compute the same bits.
//! The JavaScript backend has its own copy (`crates/tauto-jsgen/src/float.js`).

use crate::{Loc, Text, error, float_math, messages};

/// The value of a literal as written (`1.5`, `2e10`): the nearest `Float`.
/// `None` for one that is not finite there (`1e400`).
pub fn parse_literal(s: &str) -> Option<f64> {
    s.parse::<f64>().ok().filter(|x| x.is_finite())
}

/// `a / b`; `None` when `b` is zero (either sign), which is a run-time
/// error rather than an infinity.
pub fn div(a: f64, b: f64) -> Option<f64> {
    (b != 0.0).then_some(a / b)
}

/// `a / b` in generated code.
pub fn float_div(a: f64, b: f64, at: Loc) -> f64 {
    div(a, b).unwrap_or_else(|| error(messages::DIVISION_BY_ZERO, at))
}

/// The digits `show` and `text_of_float` write: the shortest decimal that
/// reads back as the same `Float`, without an exponent (`0.1`, `1`,
/// `1000000`, `-0`, `NaN`, `inf`).
pub fn text_of_float(x: f64) -> Text {
    Text::from(format!("{x}"))
}

/// Whether `t` is a number as a literal writes one, with an optional `-`:
/// digits, then optionally `.` and digits, then optionally `e` or `E`, a
/// sign and digits. Nothing else (no `inf`, `NaN`, `+`, `.5` or spaces).
fn decimal_syntax(t: &str) -> bool {
    let b = t.strip_prefix('-').unwrap_or(t).as_bytes();
    let digits = |i: &mut usize| {
        let start = *i;
        while *i < b.len() && b[*i].is_ascii_digit() {
            *i += 1;
        }
        *i > start
    };
    let mut i = 0;
    if !digits(&mut i) {
        return false;
    }
    if i < b.len() && b[i] == b'.' {
        i += 1;
        if !digits(&mut i) {
            return false;
        }
    }
    if i < b.len() && (b[i] == b'e' || b[i] == b'E') {
        i += 1;
        if i < b.len() && (b[i] == b'+' || b[i] == b'-') {
            i += 1;
        }
        if !digits(&mut i) {
            return false;
        }
    }
    i == b.len()
}

/// The nearest `Float` of a number written as a literal is (with an
/// optional `-`); `None` for anything else. A number past the largest
/// `Float` reads as an infinity.
pub fn float_of_str(t: &str) -> Option<f64> {
    if decimal_syntax(t) {
        t.parse::<f64>().ok()
    } else {
        None
    }
}

pub fn float_of_text(t: Text) -> Option<f64> {
    float_of_str(&t)
}

/// The nearest `Float`, ties to even.
pub fn float_of_i64(n: i64) -> f64 {
    n as f64
}

/// The integer part, towards zero; NaN, an infinity or a part outside
/// `i64` is the run-time error of a number that does not fit.
pub fn i64_of_float_checked(x: f64) -> Option<i64> {
    let t = x.trunc();
    // -2^63 <= t < 2^63; NaN fails both comparisons.
    (t >= -9_223_372_036_854_775_808.0 && t < 9_223_372_036_854_775_808.0).then_some(t as i64)
}

pub fn i64_of_float(x: f64, at: Loc) -> i64 {
    i64_of_float_checked(x).unwrap_or_else(|| error(messages::TOO_LARGE, at))
}

/// The bits of `x`; `0x7FF8000000000000` for every NaN, whichever one the
/// platform made, so that every backend gives the same bits.
pub fn float_bits(x: f64) -> u64 {
    if x.is_nan() {
        0x7FF8_0000_0000_0000
    } else {
        x.to_bits()
    }
}

pub fn float_of_bits(b: u64) -> f64 {
    f64::from_bits(b)
}

pub fn float_is_nan(x: f64) -> bool {
    x.is_nan()
}

pub fn float_abs(x: f64) -> f64 {
    x.abs()
}

pub fn float_floor(x: f64) -> f64 {
    x.floor()
}

pub fn float_ceil(x: f64) -> f64 {
    x.ceil()
}

pub fn float_trunc(x: f64) -> f64 {
    x.trunc()
}

/// The nearest integer, halves away from zero.
pub fn float_round(x: f64) -> f64 {
    x.round()
}

pub fn float_sqrt(x: f64) -> f64 {
    x.sqrt()
}

macro_rules! computed {
    ($($name:ident => $f:ident($($a:ident),*)),* $(,)?) => {$(
        pub fn $name($($a: f64),*) -> f64 {
            float_math::$f($($a),*)
        }
    )*};
}

computed! {
    float_cbrt => cbrt(x),
    float_exp => exp(x),
    float_ln => log(x),
    float_log2 => log2(x),
    float_log10 => log10(x),
    float_pow => pow(x, y),
    float_sin => sin(x),
    float_cos => cos(x),
    float_tan => tan(x),
    float_asin => asin(x),
    float_acos => acos(x),
    float_atan => atan(x),
    float_atan2 => atan2(y, x),
    float_sinh => sinh(x),
    float_cosh => cosh(x),
    float_tanh => tanh(x),
}

// ---- `Float32` (IEEE 754 binary32) ----------------------------------------

/// `a / b` of `Float32`: `None` when `b` is a zero.
pub fn div32(a: f32, b: f32) -> Option<f32> {
    (b != 0.0).then_some(a / b)
}

/// `a / b` of `Float32` in generated code.
pub fn float32_div(a: f32, b: f32, at: Loc) -> f32 {
    div32(a, b).unwrap_or_else(|| error(messages::DIVISION_BY_ZERO, at))
}

/// The nearest `Float32`, ties to even; past the largest, an infinity.
pub fn float32_of_float(x: f64) -> f32 {
    x as f32
}

/// The same number: every `Float32` is a `Float`.
pub fn float_of_float32(x: f32) -> f64 {
    f64::from(x)
}

/// The bits of `x`; `0x7FC00000` for every NaN.
pub fn float32_bits(x: f32) -> u32 {
    if x.is_nan() { 0x7FC0_0000 } else { x.to_bits() }
}

pub fn float32_of_bits(b: u32) -> f32 {
    f32::from_bits(b)
}

pub fn float32_is_nan(x: f32) -> bool {
    x.is_nan()
}

pub fn float32_abs(x: f32) -> f32 {
    x.abs()
}

pub fn float32_floor(x: f32) -> f32 {
    x.floor()
}

pub fn float32_ceil(x: f32) -> f32 {
    x.ceil()
}

pub fn float32_trunc(x: f32) -> f32 {
    x.trunc()
}

/// The nearest integer, halves away from zero.
pub fn float32_round(x: f32) -> f32 {
    x.round()
}

pub fn float32_sqrt(x: f32) -> f32 {
    x.sqrt()
}

// The functions IEEE 754 does not round exactly: the `Float` function of the
// same number, rounded to the nearest `Float32`. Every backend computes the
// `Float` one alike, so they agree here too.
macro_rules! computed32 {
    ($($name:ident => $f:ident($($a:ident),*)),* $(,)?) => {$(
        pub fn $name($($a: f32),*) -> f32 {
            float_math::$f($(f64::from($a)),*) as f32
        }
    )*};
}

computed32! {
    float32_cbrt => cbrt(x),
    float32_exp => exp(x),
    float32_ln => log(x),
    float32_log2 => log2(x),
    float32_log10 => log10(x),
    float32_pow => pow(x, y),
    float32_sin => sin(x),
    float32_cos => cos(x),
    float32_tan => tan(x),
    float32_asin => asin(x),
    float32_acos => acos(x),
    float32_atan => atan(x),
    float32_atan2 => atan2(y, x),
    float32_sinh => sinh(x),
    float32_cosh => cosh(x),
    float32_tanh => tanh(x),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literals_and_text() {
        assert_eq!(parse_literal("1.5"), Some(1.5));
        assert_eq!(parse_literal("6.02e23"), Some(6.02e23));
        assert_eq!(parse_literal("1e400"), None);
        assert_eq!(float_of_str("-2.5E-3"), Some(-0.0025));
        assert_eq!(float_of_str("1e400"), Some(f64::INFINITY));
        for bad in [
            "", "-", ".5", "1.", "+1", "inf", "NaN", "1e", " 1", "1_0", "0x10",
        ] {
            assert_eq!(float_of_str(bad), None, "{bad:?}");
        }
        let shown: Vec<String> = [1.0, 0.1, -0.0, 1e21, 1e-7, f64::NAN, f64::NEG_INFINITY]
            .iter()
            .map(|x| text_of_float(*x).to_string())
            .collect();
        assert_eq!(
            shown,
            [
                "1",
                "0.1",
                "-0",
                "1000000000000000000000",
                "0.0000001",
                "NaN",
                "-inf"
            ]
        );
    }

    #[test]
    fn conversions() {
        assert_eq!(i64_of_float_checked(-2.9), Some(-2));
        assert_eq!(
            i64_of_float_checked(-9.223372036854775808e18),
            Some(i64::MIN)
        );
        assert_eq!(i64_of_float_checked(9.223372036854775808e18), None);
        assert_eq!(i64_of_float_checked(f64::NAN), None);
        assert_eq!(float_of_i64(i64::MAX), 9.223372036854775808e18);
        assert_eq!(div(1.0, -0.0), None);
        assert_eq!(float_round(-2.5), -3.0);
        assert_eq!(float_bits(-f64::NAN), 0x7FF8_0000_0000_0000);
        assert_eq!(
            float_bits(f64::from_bits(0x7FF0_0000_0000_0001)),
            0x7FF8_0000_0000_0000
        );
    }
}
