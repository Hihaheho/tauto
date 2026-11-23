//! What every backend needs to know about a builtin, kept here once so
//! that no backend writes its own table.

/// The builtin that releases its owned argument: written by
/// `ownership::insert`, for a backend that drops values itself.
pub const DROP: &str = "drop";

/// The builtin that releases what is left of a `linear` value after a
/// pattern of its constructor took it apart: written by
/// `ownership::insert` where it would write `drop`, which a linear value
/// cannot end in. A backend releases it as it releases a `drop`.
pub const RELEASE_SHELL: &str = "release_shell";

/// The builtins on `Float` and its conversions.
pub const FLOAT: &[&str] = &[
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

/// Whether a call of the builtin `name` has no effect and reads nothing
/// but its arguments: it may be run again, dropped when unused, or kept in
/// a frame that is reused.
pub fn is_pure(name: &str) -> bool {
    FLOAT.contains(&name)
        || matches!(
            name,
            "concat"
                | "Text::of_i64"
                | "Text::of_u64"
                | "Text::of_nat"
                | "Text::len"
                | "Text::compare"
                | "Text::byte"
                | "Text::slice"
                | "Text::of_code_point"
                | "Text::of_utf8"
                | "words"
                | "div"
                | "mod"
                | "Array::get"
                | "Array::len"
                | "Array::set"
                | "Array::of_list"
                | "Array::to_list"
                | "Bytes::of_list"
                | "Bytes::to_list"
                | "Bytes::len"
                | "secret"
                | "expose"
                | "Region::new"
                | "Region::place"
                | "RcRegion::new"
                | "RcRegion::place"
                | "RcPlace::heap"
                | "Bytes::get"
                | "Bytes::find"
                | "Bytes::slice"
                | "Bytes::concat"
                | "Bytes::eq"
                | "Bytes::of_text"
                | "Text::of_bytes"
                | "I64::of_i8"
                | "I64::of_i16"
                | "I8::of_i64"
                | "I16::of_i64"
                | "U64::of_u16"
                | "U16::of_u64"
                | "I64::of_i32"
                | "I32::of_i64"
                | "I64::of_u64"
                | "U64::of_i64"
                | "U64::of_u32"
                | "U32::of_u64"
                | "U64::of_u8"
                | "U64::of_uhost"
                | "UHost::succ_below"
                | "UHost::pred_nz"
                | "UHost::add_within"
                | "UHost::sub"
                | "UHost::of_u64_below"
                | "U8::of_u64"
                | "Nat::of_u64"
                | "U64::of_nat"
                | "U32::and"
                | "U32::or"
                | "U32::xor"
                | "U32::shl"
                | "U32::shr"
                | "U32::rotl"
                | "U32::rotr"
                | "U64::and"
                | "U64::or"
                | "U64::xor"
                | "U64::shl"
                | "U64::shr"
                | "U64::rotl"
                | "U64::rotr"
                | "U64::wrapping_add"
                | "U64::wrapping_sub"
                | "U64::wrapping_mul"
        )
}
