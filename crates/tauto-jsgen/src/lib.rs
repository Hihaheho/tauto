//! Standalone JavaScript modules from checked NIR.
use tauto_nir::*;
mod borrowed_returns;

/// The functions of `Float` and `Float32` (`std/prelude/Num.taut`): pure, and computed by
/// `pureBuiltin` (`builtins.js`) with `float.js`.
pub(crate) const FLOAT_BUILTINS: &[&str] = &[
    "Float::of_i64",
    "I64::of_float",
    "Float::of_text",
    "Text::of_float",
    "Float::bits",
    "Float::of_bits",
    "Float::is_nan",
    "Float::abs",
    "Float::floor",
    "Float::ceil",
    "Float::trunc",
    "Float::round",
    "Float::sqrt",
    "Float::cbrt",
    "Float::exp",
    "Float::ln",
    "Float::log2",
    "Float::log10",
    "Float::pow",
    "Float::sin",
    "Float::cos",
    "Float::tan",
    "Float::asin",
    "Float::acos",
    "Float::atan",
    "Float::atan2",
    "Float::sinh",
    "Float::cosh",
    "Float::tanh",
    "Float32::of_float",
    "Float::of_float32",
    "Float32::bits",
    "Float32::of_bits",
    "Float32::is_nan",
    "Float32::abs",
    "Float32::floor",
    "Float32::ceil",
    "Float32::trunc",
    "Float32::round",
    "Float32::sqrt",
    "Float32::cbrt",
    "Float32::exp",
    "Float32::ln",
    "Float32::log2",
    "Float32::log10",
    "Float32::pow",
    "Float32::sin",
    "Float32::cos",
    "Float32::tan",
    "Float32::asin",
    "Float32::acos",
    "Float32::atan",
    "Float32::atan2",
    "Float32::sinh",
    "Float32::cosh",
    "Float32::tanh",
];
mod chunks;
mod cps;
mod declarations;
mod direct;
mod shake;
mod syntax;
mod tail_calls;
pub use cps::{Modules, Options, generate, generate_modules, generate_with};
pub use declarations::{generate_declarations, generate_declarations_with};
type R<T> = Result<T, String>;
fn quote(s: &str) -> String {
    serde_json::to_string(s).unwrap()
}
fn unsupported<T>(what: impl Into<tauto_message::Message>) -> R<T> {
    Err(tauto_message::msg!("jsgen-unsupported", what = what.into()).to_string())
}
fn bounds(w: Width) -> String {
    let (min, max) = match w {
        // A `nat` has no largest value.
        Width::Nat => return "0n,Infinity".into(),
        Width::W32 => (i32::MIN as i128, i32::MAX as i128),
        Width::W64 => (i64::MIN as i128, i64::MAX as i128),
        Width::U8 => (0, u8::MAX as i128),
        Width::U32 => (0, u32::MAX as i128),
        Width::U64 => (0, u64::MAX as i128),
    };
    format!("{min}n,{max}n")
}
