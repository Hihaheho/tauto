//! Extraction: the programs of the proof language as Nib. The kernel checks the files first; what it accepted is written out
//! as Nib source with its types and proofs erased:
//!
//! * a family in `Type` becomes a `shared enum`, its parameters generics and
//!   its proof fields dropped; a family in `Prop`, a `theorem`, an `axiom`
//!   and a `def` are dropped;
//! * a function keeps its value parameters; a type parameter becomes a
//!   generic, a proof parameter is dropped, and so is the matching argument
//!   of every call;
//! * `match x: T` loses its result type; a match on a proof keeps its one
//!   arm; a match on `Nat` or `Bool` becomes a chain of `if`s.
//!
//! A few declarations of `std/` are not written out but mapped onto Nib's
//! own types and functions (`Nat` onto `nat`, `List` onto `List`, `nat_lt`
//! onto `<`, …). Each has a definition in `std/` that the proofs use. These
//! mappings are additional semantic assumptions of extraction. The kernel
//! checks the source declarations; extraction and the runtime backend are
//! responsible for preserving their behavior in executable code.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use tauto_message::{Message, msg};

use crate::check::{Checked, Role, Verdict, record_sugar};
use crate::surface::print::{in_modules_text, raw};
use crate::surface::{
    FnDecl, InductiveDecl, MatchArm, Pattern, Stmt, SurfaceTerm, TermKind, parse_program_at,
};

/// Which names are the standard library's own declarations. The tables
/// below map a declaration of `std/` (or the prelude) onto Nib by its short
/// name; a declaration of the program's own files with the same name is
/// extracted from its definition, which is what the proofs were about.
struct StdNames {
    /// What the program's own files declare.
    own: HashSet<String>,
    /// What the files of `std/` declare, as the program reads them.
    std: HashSet<String>,
    /// What the prelude declares: the library prelude and the kernel's.
    prelude: HashSet<String>,
}

impl StdNames {
    fn new(sources: &[(crate::program::SourceFile, Vec<Stmt>)]) -> Self {
        let std_root = Path::new(crate::stdlib::ROOT);
        let mut own = HashSet::new();
        let mut std = HashSet::new();
        for (file, stmts) in sources {
            // A file read by its path that is a copy of a file of `std/`, word
            // for word, declares what that file declares.
            let of_std = file.path.starts_with(std_root)
                || crate::stdlib::FILES
                    .iter()
                    .any(|(_, text)| *text == file.text);
            let set = if of_std { &mut std } else { &mut own };
            for s in stmts {
                crate::surface::qualify::declared(s, &mut |n| {
                    set.insert(n.to_string());
                });
            }
        }
        let mut prelude = crate::surface::qualify::prelude_names().clone();
        for s in crate::check::kernel_prelude()
            .map(|p| p.stmts)
            .unwrap_or_default()
        {
            crate::surface::qualify::declared(&s, &mut |n| {
                prelude.insert(n.to_string());
            });
        }
        StdNames { own, std, prelude }
    }

    fn in_std(&self, n: &str) -> bool {
        !self.own.contains(n) && self.std.contains(n)
    }

    /// Whether a call of `n`, as the checker resolved it, is written by the
    /// mapping of the `std/` function it names. The name decides, not the
    /// spelling: the prelude's `Text::len`, a builtin of Nib, is never
    /// written by a mapping.
    fn written_by_mapping(&self, n: &str) -> bool {
        self.in_std(n) && mapped_fn(crate::surface::qualify::short(n)).is_some()
    }

    /// The short name of `n` when `n` names a declaration of the standard
    /// library: one of `std/`, or the prelude's when no file of the program
    /// declares it.
    fn of<'n>(&self, n: &'n str) -> Option<&'n str> {
        use crate::surface::qualify::{PRELUDE_MODULE, SEPARATOR, short};
        if self.own.contains(n) {
            return None;
        }
        if self.std.contains(n) {
            return Some(short(n));
        }
        // The constructor a struct's record syntax gives it (`Pair::Mk`).
        if let Some((family, _)) = n.rsplit_once("::") {
            return self.of(family).map(|_| short(n));
        }
        let bare = n
            .strip_prefix(PRELUDE_MODULE)
            .and_then(|rest| rest.strip_prefix(SEPARATOR))
            .unwrap_or(n);
        self.prelude.contains(bare).then_some(bare)
    }
}

/// The Nib type a family of `std/` is extracted to.
fn mapped_type(name: &str) -> Option<&'static str> {
    Some(match name {
        "Nat" => "nat",
        "Bool" => "Bool",
        "Unit" => "Unit",
        "List" => "List",
        "Option" => "Option",
        "Pair" => "Pair",
        "Text" => "Text",
        "Array" => "Array",
        "Bytes" => "Bytes",
        "Stack" => "Vec",
        "Ordering" => "Ordering",
        "Never" => "Never",
        "U8" => "u8",
        "U32" => "u32",
        "U64" => "u64",
        "I32" => "i32",
        "I64" => "i64",
        "Float" => "Float",
        "Float32" => "Float32",
        "Secret" => "Secret",
        _ => return None,
    })
}

/// A class that programs and proofs both read from the prelude
/// (`std/prelude/Ord.taut`): a file does not declare it, an instance of it
/// for a type that extraction maps onto a builtin of Nib is not written
/// either (Nib's `std` has that instance), and its methods take their
/// arguments by borrow.
fn mapped_class(name: &str) -> bool {
    name == "Ord"
}

/// The heads mapped onto builtins of Nib whose instances of a mapped class
/// Nib's `std` declares (`std/prelude/Classes.taut`).
fn std_instance_head(name: &str) -> bool {
    matches!(name, "Nat" | "Bool" | "Text")
}

/// The constructor of an instance's head: `List` of `List(A)`.
fn head_name(head: &SurfaceTerm) -> &str {
    match &*head.kind {
        TermKind::Var(n) => n,
        TermKind::App { function, .. } => match &*function.kind {
            TermKind::Var(n) => n,
            _ => "",
        },
        _ => "",
    }
}

/// The functions of `std/` extracted to an expression of Nib: `$0`, `$1`,
/// … are the value arguments, each evaluated once (they are bound first
/// when used more than once).
fn mapped_fn(name: &str) -> Option<&'static str> {
    Some(match name {
        "Nat::lt" => "$0 < $1",
        "Nat::le" => "$0 <= $1",
        "Nat::eq" => "$0 == $1",
        "Nat::pred" => "extract_nat_sub($0, 1)",
        "Nat::add" => "$0 + $1",
        "Nat::sub" => "extract_nat_sub($0, $1)",
        "Nat::mul" => "$0 * $1",
        "Nat::div_nz" => "extract_nat_div($0, $1)",
        "Nat::rem_nz" => "extract_nat_mod($0, $1)",
        "Nat::divmod" => "extract_nat_divmod($0, $1, $2, $3)",
        "Bool::and" => "$0 && $1",
        "Bool::or" => "$0 || $1",
        "not" => "not($0)",
        "Bool::eq" => "$0 == $1",
        "Text::bytes" => "extract_text_bytes($0)",
        "Text::len" => "Nat::of_u64(Text::len($0))",
        "Text::byte" => "extract_text_byte($0, $1)",
        "Text::slice" => "Text::slice($0, U64::of_nat($1), U64::of_nat($2))",
        // The builtin by its full name: inside `module Text`, `concat` would
        // be the extracted `Text::concat` itself.
        "Text::concat" => "std::prelude::concat($0, $1)",
        "Text::concat_all" => "extract_text_concat_all($0)",
        "Text::ordering" => "extract_ordering(Text::compare($0, $1))",
        "Text::eq" => "$0 == $1",
        "Text::of_nat" => "Text::of_nat($0)",
        "Text::of_code_point" => "extract_text_of_code_point($0)",
        "Text::utf8_of_code_point" => "extract_text_utf8_of_code_point($0)",
        "Text::of_utf8" => "extract_text_of_utf8($0)",
        "Array::of_list" => "Array::of_list($0)",
        "Array::to_list" => "Array::to_list($0)",
        "Array::get" => "Array::get($0, U64::of_nat($1))",
        "Array::len" => "Nat::of_u64(Array::len($0))",
        "Bytes::of_list" => "Bytes::of_list($0)",
        "Bytes::to_list" => "Bytes::to_list($0)",
        "Bytes::len" => "Nat::of_u64(Bytes::len($0))",
        "Bytes::get" => "Bytes::get($0, U64::of_nat($1))",
        "Bytes::slice" => "Bytes::slice($0, U64::of_nat($1), U64::of_nat($2))",
        "Bytes::concat" => "Bytes::concat($0, $1)",
        "Bytes::eq" => "Bytes::eq($0, $1)",
        "Bytes::of_text" => "Bytes::of_text($0)",
        "Text::of_bytes" => "Text::of_bytes($0)",
        "Stack::new" => "Vec::new()",
        "Stack::push" => "Vec::push($0, $1)",
        "Stack::pop" => "Vec::pop($0)",
        "Stack::len" => "Nat::of_u64(Vec::len($0))",
        "Stack::is_empty" => "(Vec::len($0) == 0)",
        // Nib's `Never` is below every type.
        "Never::elim" => "$0",
        "U8::val" => "Nat::of_u64(U64::of_u8($0))",
        "U8::of_decided" => "extract_u8_of_decided($0, $1)",
        "U8::of_nat_checked" => "extract_u8_of_nat($0)",
        "U8::add" => "$0 + $1",
        "U8::sub" => "$0 - $1",
        "U8::mul" => "$0 * $1",
        "U8::checked_add" => "extract_u8_checked_add($0, $1)",
        "U8::checked_sub" => "extract_u8_checked_sub($0, $1)",
        "U8::checked_mul" => "extract_u8_checked_mul($0, $1)",
        "U8::lt" => "$0 < $1",
        "U8::le" => "$0 <= $1",
        "U8::eq" => "$0 == $1",
        "U8::wrapping_add" => "extract_u8_wrap(extract_u8_nat($0) + extract_u8_nat($1))",
        "U8::wrapping_sub" => {
            "extract_u8_wrap(extract_u8_nat($0) + extract_u8_modulus() - extract_u8_nat($1))"
        }
        "U8::wrapping_mul" => "extract_u8_wrap(extract_u8_nat($0) * extract_u8_nat($1))",
        "U32::val" => "Nat::of_u64(U64::of_u32($0))",
        "U32::of_decided" => "extract_u32_of_decided($0, $1)",
        "U32::of_nat_checked" => "extract_u32_of_nat($0)",
        "U32::add" => "$0 + $1",
        "U32::sub" => "$0 - $1",
        "U32::mul" => "$0 * $1",
        "U32::checked_add" => "extract_u32_checked_add($0, $1)",
        "U32::checked_sub" => "extract_u32_checked_sub($0, $1)",
        "U32::checked_mul" => "extract_u32_checked_mul($0, $1)",
        "U32::lt" => "$0 < $1",
        "U32::le" => "$0 <= $1",
        "U32::eq" => "$0 == $1",
        "U32::wrapping_add" => "extract_u32_wrap(extract_u32_nat($0) + extract_u32_nat($1))",
        "U32::wrapping_sub" => {
            "extract_u32_wrap(extract_u32_nat($0) + extract_u32_modulus() - extract_u32_nat($1))"
        }
        "U32::wrapping_mul" => "extract_u32_wrap(extract_u32_nat($0) * extract_u32_nat($1))",
        "U64::val" => "Nat::of_u64($0)",
        "U64::of_decided" => "extract_u64_of_decided($0, $1)",
        "U64::of_nat_checked" => "extract_u64_of_nat($0)",
        "U64::add" => "$0 + $1",
        "U64::sub" => "$0 - $1",
        "U64::mul" => "$0 * $1",
        "U64::checked_add" => "extract_u64_checked_add($0, $1)",
        "U64::checked_sub" => "extract_u64_checked_sub($0, $1)",
        "U64::checked_mul" => "extract_u64_checked_mul($0, $1)",
        "U64::lt" => "$0 < $1",
        "U64::le" => "$0 <= $1",
        "U64::eq" => "$0 == $1",
        "U64::wrapping_add" => "extract_u64_wrap(extract_u64_nat($0) + extract_u64_nat($1))",
        "U64::wrapping_sub" => {
            "extract_u64_wrap(extract_u64_nat($0) + extract_u64_modulus() - extract_u64_nat($1))"
        }
        "U64::wrapping_mul" => "extract_u64_wrap(extract_u64_nat($0) * extract_u64_nat($1))",
        "U32::and" => "U32::and($0, $1)",
        "U32::or" => "U32::or($0, $1)",
        "U32::xor" => "U32::xor($0, $1)",
        "U32::shl" => "U32::shl($0, U64::of_nat(extract_nat_mod($1, 32)))",
        "U32::shr" => "U32::shr($0, U64::of_nat(extract_nat_mod($1, 32)))",
        "U32::rotl" => "U32::rotl($0, U64::of_nat(extract_nat_mod($1, 32)))",
        "U32::rotr" => "U32::rotr($0, U64::of_nat(extract_nat_mod($1, 32)))",
        "U64::and" => "U64::and($0, $1)",
        "U64::or" => "U64::or($0, $1)",
        "U64::xor" => "U64::xor($0, $1)",
        "U64::shl" => "U64::shl($0, U64::of_nat(extract_nat_mod($1, 64)))",
        "U64::shr" => "U64::shr($0, U64::of_nat(extract_nat_mod($1, 64)))",
        "U64::rotl" => "U64::rotl($0, U64::of_nat(extract_nat_mod($1, 64)))",
        "U64::rotr" => "U64::rotr($0, U64::of_nat(extract_nat_mod($1, 64)))",
        // The secret words run in constant time (`docs/design/secret.md`).
        "Ct::u8_add" => "Ct::u8_add($0, $1)",
        "Ct::u8_sub" => "Ct::u8_sub($0, $1)",
        "Ct::u8_mul" => "Ct::u8_mul($0, $1)",
        "Ct::u8_and" => "Ct::u8_and($0, $1)",
        "Ct::u8_or" => "Ct::u8_or($0, $1)",
        "Ct::u8_xor" => "Ct::u8_xor($0, $1)",
        "Ct::u8_eq" => "Ct::u8_eq($0, $1)",
        "Ct::u8_lt" => "Ct::u8_lt($0, $1)",
        "Ct::u8_not" => "Ct::u8_not($0)",
        "Ct::u8_shl" => "Ct::u8_shl($0, U64::of_nat(extract_nat_mod($1, 8)))",
        "Ct::u8_shr" => "Ct::u8_shr($0, U64::of_nat(extract_nat_mod($1, 8)))",
        "Ct::u8_rotl" => "Ct::u8_rotl($0, U64::of_nat(extract_nat_mod($1, 8)))",
        "Ct::u8_rotr" => "Ct::u8_rotr($0, U64::of_nat(extract_nat_mod($1, 8)))",
        "Ct::u8_select" => "Ct::u8_select($0, $1, $2)",
        "Ct::u32_add" => "Ct::u32_add($0, $1)",
        "Ct::u32_sub" => "Ct::u32_sub($0, $1)",
        "Ct::u32_mul" => "Ct::u32_mul($0, $1)",
        "Ct::u32_and" => "Ct::u32_and($0, $1)",
        "Ct::u32_or" => "Ct::u32_or($0, $1)",
        "Ct::u32_xor" => "Ct::u32_xor($0, $1)",
        "Ct::u32_eq" => "Ct::u32_eq($0, $1)",
        "Ct::u32_lt" => "Ct::u32_lt($0, $1)",
        "Ct::u32_not" => "Ct::u32_not($0)",
        "Ct::u32_shl" => "Ct::u32_shl($0, U64::of_nat(extract_nat_mod($1, 32)))",
        "Ct::u32_shr" => "Ct::u32_shr($0, U64::of_nat(extract_nat_mod($1, 32)))",
        "Ct::u32_rotl" => "Ct::u32_rotl($0, U64::of_nat(extract_nat_mod($1, 32)))",
        "Ct::u32_rotr" => "Ct::u32_rotr($0, U64::of_nat(extract_nat_mod($1, 32)))",
        "Ct::u32_select" => "Ct::u32_select($0, $1, $2)",
        "Ct::u64_add" => "Ct::u64_add($0, $1)",
        "Ct::u64_sub" => "Ct::u64_sub($0, $1)",
        "Ct::u64_mul" => "Ct::u64_mul($0, $1)",
        "Ct::u64_and" => "Ct::u64_and($0, $1)",
        "Ct::u64_or" => "Ct::u64_or($0, $1)",
        "Ct::u64_xor" => "Ct::u64_xor($0, $1)",
        "Ct::u64_eq" => "Ct::u64_eq($0, $1)",
        "Ct::u64_lt" => "Ct::u64_lt($0, $1)",
        "Ct::u64_not" => "Ct::u64_not($0)",
        "Ct::u64_shl" => "Ct::u64_shl($0, U64::of_nat(extract_nat_mod($1, 64)))",
        "Ct::u64_shr" => "Ct::u64_shr($0, U64::of_nat(extract_nat_mod($1, 64)))",
        "Ct::u64_rotl" => "Ct::u64_rotl($0, U64::of_nat(extract_nat_mod($1, 64)))",
        "Ct::u64_rotr" => "Ct::u64_rotr($0, U64::of_nat(extract_nat_mod($1, 64)))",
        "Ct::u64_select" => "Ct::u64_select($0, $1, $2)",
        "Ct::u64_mul_hi" => "Ct::u64_mul_hi($0, $1)",
        "Ct::u64_of_u8" => "Ct::u64_of_u8($0)",
        "Ct::u64_of_u32" => "Ct::u64_of_u32($0)",
        "Ct::u32_of_u8" => "Ct::u32_of_u8($0)",
        "Ct::u8_of_u32" => "Ct::u8_of_u32($0)",
        "Ct::u8_of_u64" => "Ct::u8_of_u64($0)",
        "Ct::u32_of_u64" => "Ct::u32_of_u64($0)",
        "Ct::bytes_len" => "Nat::of_u64(Ct::bytes_len($0))",
        "Ct::bytes_get" => "Ct::bytes_get($0, U64::of_nat($1))",
        "Ct::bool_and" => "Ct::bool_and($0, $1)",
        "Ct::bool_or" => "Ct::bool_or($0, $1)",
        "Ct::bool_not" => "Ct::bool_not($0)",
        "Ct::bool_select" => "Ct::bool_select($0, $1, $2)",
        "expose" => "expose($0)",
        "I32::val" => "extract_i32_int($0)",
        "I32::of_decided" => "extract_i32_of_decided($0, $1)",
        "I32::of_int" => "extract_i32_of_int($0)",
        "I32::add" => "$0 + $1",
        "I32::sub" => "$0 - $1",
        "I32::mul" => "$0 * $1",
        "I32::checked_add" => {
            "extract_i32_of_int(Int::add(extract_i32_int($0), extract_i32_int($1)))"
        }
        "I32::checked_sub" => {
            "extract_i32_of_int(Int::sub(extract_i32_int($0), extract_i32_int($1)))"
        }
        "I32::checked_mul" => {
            "extract_i32_of_int(Int::mul(extract_i32_int($0), extract_i32_int($1)))"
        }
        "I32::lt" => "$0 < $1",
        "I32::le" => "$0 <= $1",
        "I32::eq" => "$0 == $1",
        "I64::val" => "extract_i64_int($0)",
        "I64::of_decided" => "extract_i64_of_decided($0, $1)",
        "I64::of_int" => "extract_i64_of_int($0)",
        "I64::add" => "$0 + $1",
        "I64::sub" => "$0 - $1",
        "I64::mul" => "$0 * $1",
        "I64::checked_add" => {
            "extract_i64_of_int(Int::add(extract_i64_int($0), extract_i64_int($1)))"
        }
        "I64::checked_sub" => {
            "extract_i64_of_int(Int::sub(extract_i64_int($0), extract_i64_int($1)))"
        }
        "I64::checked_mul" => {
            "extract_i64_of_int(Int::mul(extract_i64_int($0), extract_i64_int($1)))"
        }
        "I64::lt" => "$0 < $1",
        "I64::le" => "$0 <= $1",
        "I64::eq" => "$0 == $1",
        "Float::raw" => "Nat::of_u64(Float::bits($0))",
        "Float::of_raw" => "Float::of_bits(U64::of_nat(extract_nat_mod($0, 18446744073709551616)))",
        "Float::bits" => "Float::bits($0)",
        "Float::of_bits" => "Float::of_bits($0)",
        "Float::add" => "$0 + $1",
        "Float::sub" => "$0 - $1",
        "Float::mul" => "$0 * $1",
        "Float::neg" => "-$0",
        "Float::div" => "$0 / $1",
        "Float::checked_div" => "extract_float_checked_div($0, $1)",
        "Float::is_zero" => "$0 == 0.0",
        "Float::is_infinite" => "extract_float_is_infinite($0)",
        "Float::eq" => "$0 == $1",
        "Float::lt" => "$0 < $1",
        "Float::le" => "$0 <= $1",
        "Float::of_i64" => "Float::of_i64($0)",
        "I64::of_float_checked" => "extract_i64_of_float_checked($0)",
        "Float::is_nan" => "Float::is_nan($0)",
        "Float::abs" => "Float::abs($0)",
        "Float::sqrt" => "Float::sqrt($0)",
        "Float::trunc" => "Float::trunc($0)",
        "Float::floor" => "Float::floor($0)",
        "Float::ceil" => "Float::ceil($0)",
        "Float::round" => "Float::round($0)",
        "Float::cbrt" => "Float::cbrt($0)",
        "Float::exp" => "Float::exp($0)",
        "Float::ln" => "Float::ln($0)",
        "Float::log2" => "Float::log2($0)",
        "Float::log10" => "Float::log10($0)",
        "Float::pow" => "Float::pow($0, $1)",
        "Float::sin" => "Float::sin($0)",
        "Float::cos" => "Float::cos($0)",
        "Float::tan" => "Float::tan($0)",
        "Float::asin" => "Float::asin($0)",
        "Float::acos" => "Float::acos($0)",
        "Float::atan" => "Float::atan($0)",
        "Float::atan2" => "Float::atan2($0, $1)",
        "Float::sinh" => "Float::sinh($0)",
        "Float::cosh" => "Float::cosh($0)",
        "Float::tanh" => "Float::tanh($0)",
        "Text::of_float" => "Text::of_float($0)",
        "Float::of_text" => "Float::of_text($0)",
        "Float32::raw" => "Nat::of_u64(U64::of_u32(Float32::bits($0)))",
        "Float32::of_raw" => {
            "Float32::of_bits(U32::of_u64(U64::of_nat(extract_nat_mod($0, 4294967296))))"
        }
        "Float32::bits" => "Float32::bits($0)",
        "Float32::of_bits" => "Float32::of_bits($0)",
        "Float32::of_float" => "Float32::of_float($0)",
        "Float::of_float32" => "Float::of_float32($0)",
        "Float32::add" => "$0 + $1",
        "Float32::sub" => "$0 - $1",
        "Float32::mul" => "$0 * $1",
        "Float32::neg" => "-$0",
        "Float32::div" => "$0 / $1",
        "Float32::checked_div" => "extract_float32_checked_div($0, $1)",
        "Float32::is_zero" => "$0 == Float32::of_float(0.0)",
        "Float32::is_infinite" => "extract_float32_is_infinite($0)",
        "Float32::eq" => "$0 == $1",
        "Float32::lt" => "$0 < $1",
        "Float32::le" => "$0 <= $1",
        "Float32::is_nan" => "Float32::is_nan($0)",
        "Float32::abs" => "Float32::abs($0)",
        "Float32::sqrt" => "Float32::sqrt($0)",
        "Float32::trunc" => "Float32::trunc($0)",
        "Float32::floor" => "Float32::floor($0)",
        "Float32::ceil" => "Float32::ceil($0)",
        "Float32::round" => "Float32::round($0)",
        "Float32::cbrt" => "Float32::cbrt($0)",
        "Float32::exp" => "Float32::exp($0)",
        "Float32::ln" => "Float32::ln($0)",
        "Float32::log2" => "Float32::log2($0)",
        "Float32::log10" => "Float32::log10($0)",
        "Float32::sin" => "Float32::sin($0)",
        "Float32::cos" => "Float32::cos($0)",
        "Float32::tan" => "Float32::tan($0)",
        "Float32::asin" => "Float32::asin($0)",
        "Float32::acos" => "Float32::acos($0)",
        "Float32::atan" => "Float32::atan($0)",
        "Float32::sinh" => "Float32::sinh($0)",
        "Float32::cosh" => "Float32::cosh($0)",
        "Float32::tanh" => "Float32::tanh($0)",
        "Float32::pow" => "Float32::pow($0, $1)",
        "Float32::atan2" => "Float32::atan2($0, $1)",
        // A value of `Quot` is a value of its representation.
        "Quot::mk" => "$0",
        "Quot::lift" => "$0($1)",
        _ => return None,
    })
}

/// The mapped functions whose names Nib's builtins already have: they get
/// no function of their own (a Nib program calls the builtin).
fn builtin_name(name: &str) -> bool {
    matches!(
        name,
        "Text::len"
            | "Text::byte"
            | "Text::slice"
            | "Text::of_code_point"
            | "Text::of_utf8"
            | "Array::of_list"
            | "Array::to_list"
            | "Array::get"
            | "Array::len"
            | "Bytes::of_list"
            | "Bytes::to_list"
            | "Bytes::len"
            | "Bytes::get"
            | "Bytes::slice"
            | "Bytes::concat"
            | "Bytes::eq"
            | "Bytes::of_text"
            | "Text::of_bytes"
            | "Float::bits"
            | "Float::of_bits"
            | "Float::of_i64"
            | "Float::is_nan"
            | "Float::abs"
            | "Float::sqrt"
            | "Float::trunc"
            | "Float::floor"
            | "Float::ceil"
            | "Float::round"
            | "Float::cbrt"
            | "Float::exp"
            | "Float::ln"
            | "Float::log2"
            | "Float::log10"
            | "Float::pow"
            | "Float::sin"
            | "Float::cos"
            | "Float::tan"
            | "Float::asin"
            | "Float::acos"
            | "Float::atan"
            | "Float::atan2"
            | "Float::sinh"
            | "Float::cosh"
            | "Float::tanh"
            | "Text::of_float"
            | "Float::of_text"
            | "Float32::bits"
            | "Float32::of_bits"
            | "Float32::of_float"
            | "Float::of_float32"
    )
}

/// The mapped functions that are written out at each call, with the places
/// they borrow (`&mut s`) as the arguments: they get no function of their own.
fn inline_only(name: &str) -> bool {
    matches!(
        name,
        "Stack::new" | "Stack::push" | "Stack::pop" | "Stack::len" | "Stack::is_empty"
    )
}

/// What every extracted program starts with: the helpers the tables use.
const HELPERS: &str = "\
// Extracted by tauto: do not edit.\n\nfn extract_nat_sub(a: nat, b: nat): nat {\n  if a < b { 0 } else { a - b }\n}\n\nfn extract_float_checked_div(a: Float, b: Float): Option(Float) {\n  if b == 0.0 { None } else { Some(a / b) }\n}\n\nfn extract_float_is_infinite(x: Float): Bool {\n  Float::abs(x) > 1.7976931348623157e308\n}\n\nfn extract_float32_checked_div(a: Float32, b: Float32): Option(Float32) {\n  if b == Float32::of_float(0.0) { None } else { Some(a / b) }\n}\n\nfn extract_float32_is_infinite(x: Float32): Bool {\n  Float::abs(Float::of_float32(x)) > 1.7976931348623157e308\n}\n\nfn extract_i64_of_float_checked(x: Float): Option(i64) {\n  let t := Float::trunc(x)\n  if t >= -9223372036854775808.0 && t < 9223372036854775808.0 { Some(I64::of_float(t)) } else { None }\n}\n\nfn extract_nat_div(a: nat, b: nat): nat {\n  if b == 0 { 0 } else { div(a, b) }\n}\n\nfn extract_nat_mod(a: nat, b: nat): nat {\n  if b == 0 { a } else { mod(a, b) }\n}\n\nfn extract_nat_divmod(a: nat, b: nat, q: nat, r: nat): Pair(nat, nat) {\n  if b == 0 || r >= b {\n    Pair { fst: q, snd: r + a }\n  } else {\n    Pair { fst: q + div(r + a, b), snd: mod(r + a, b) }\n  }\n}\n\n// Never called: it stands for a match on a proof with no arms. Its\n// recursion is written as `Div`, so the program is also a Tauto program.\nfn extract_unreachable<A: Shared>(): A ! {Div} {\n  extract_unreachable()\n}\n";

/// The helpers of the `Text` functions, written when `std/Text.taut` is
/// in the program.
const TEXT_HELPERS: &str = "\nfn extract_text_byte(t: Text, i: nat): Option(nat) {\n  match Text::byte(t, U64::of_nat(i)) {\n    Some(b) => Some(Nat::of_u64(U64::of_u8(b)))\n    None => None\n  }\n}\n\nfn extract_text_bytes_from(t: Text, i: u64, acc: List(nat)): List(nat) {\n  if i == 0 {\n    acc\n  } else {\n    match Text::byte(t, i - 1) {\n      Some(b) => extract_text_bytes_from(t, i - 1, Cons(Nat::of_u64(U64::of_u8(b)), acc))\n      None => acc\n    }\n  }\n}\n\nfn extract_text_bytes(t: Text): List(nat) {\n  extract_text_bytes_from(t, Text::len(t), Nil)\n}\n\nfn extract_text_push_all(&mut b: Buf, parts: List(Text)): () {\n  match parts {\n    Nil => ()\n    Cons(part, rest) => {\n      Buf::push(&mut b, &part)\n      extract_text_push_all(&mut b, rest)\n    }\n  }\n}\n\nfn extract_text_concat_all(parts: List(Text)): Text {\n  var b := Buf::new()\n  extract_text_push_all(&mut b, parts)\n  Text::of(b)\n}\n\nfn extract_ordering(c: i64): Ordering {\n  if c < 0 { Less } else if c == 0 { Equal } else { Greater }\n}\n\nfn extract_text_of_code_point(c: nat): Option(Text) {\n  if c > 1114111 {\n    None\n  } else {\n    Text::of_code_point(U32::of_u64(U64::of_nat(c)))\n  }\n}\n\nfn extract_text_utf8_of_code_point(c: nat): Text {\n  match extract_text_of_code_point(c) {\n    Some(t) => t\n    None => \"\"\n  }\n}\n\nfn extract_bytes_of(bs: List(nat)): Option(List(u8)) {\n  match bs {\n    Nil => Some(Nil)\n    Cons(b, rest) => if b > 255 {\n      None\n    } else {\n      match extract_bytes_of(rest) {\n        Some(r) => Some(Cons(U8::of_u64(U64::of_nat(b)), r))\n        None => None\n      }\n    }\n  }\n}\n\nfn extract_text_of_utf8(bs: List(nat)): Option(Text) {\n  match extract_bytes_of(bs) {\n    Some(r) => Text::of_utf8(r)\n    None => None\n  }\n}\n\n// `Text::Mk(bs)`. A `Text` at run time is well-formed UTF-8, so other bytes\n// have no value to stand for, and the program stops rather than go on\n// with a wrong one. It stops through a conversion that does not fit (Nib\n// has no other way to stop without an effect), so a function value that\n// builds a text stays pure.\nfn extract_text_of_bytes(bs: List(nat)): Text {\n  match extract_text_of_utf8(bs) {\n    Some(t) => t\n    None => Text::of_u64(U64::of_u8(U8::of_u64(256)))\n  }\n}\n";

/// `std/SInt.taut`'s widths: the Nib type and the module whose `fits` the
/// helpers call. Extraction keeps those same `fits`, so the name called and
/// the name kept come from this one table.
const SINT_WIDTHS: [(&str, &str); 2] = [("i32", "I32"), ("i64", "I64")];

/// The helpers of `std/SInt.taut`'s mapped functions, written when it is in
/// the program: a width's value as an `Int` and back. The range is
/// `std/SInt.taut`'s own `I32::fits` / `I64::fits`, extracted with it, so
/// the program decides the range by the same definition the proofs use.
fn sint_helpers() -> String {
    let mut out = String::new();
    for ((ty, module), (to_i64, of_i64)) in SINT_WIDTHS
        .into_iter()
        .zip([("I64::of_i32", "I32::of_i64"), ("", "")])
    {
        let _ = write!(
            out,
            "\nfn extract_{ty}_int(x: {ty}): Int {{\n  let y: i64 := {to_i64}(x)\n  if y >= 0 {{ IntOfNat(Nat::of_u64(U64::of_i64(y))) }} else {{ IntNegSucc(Nat::of_u64(U64::of_i64(-(y + 1)))) }}\n}}\n\nfn extract_{ty}_of_fitting(v: Int): {ty} {{\n  match v {{\n    IntOfNat(n) => {of_i64}(I64::of_u64(U64::of_nat(n)))\n    IntNegSucc(n) => {of_i64}(-I64::of_u64(U64::of_nat(n)) - 1)\n  }}\n}}\n\nfn extract_{ty}_of_decided(v: Int, o: Bool): Option({ty}) {{\n  if o {{ Some(extract_{ty}_of_fitting(v)) }} else {{ None }}\n}}\n\nfn extract_{ty}_of_int(v: Int): Option({ty}) {{\n  if {module}::fits(v) {{ Some(extract_{ty}_of_fitting(v)) }} else {{ None }}\n}}\n"
        );
    }
    out
}

/// The helpers of `std/UInt.taut`'s mapped functions, written when it is in
/// the program. The `u64` ones keep every value they compute at most
/// `2^63` (`h` is `2^63 - 1`), since Nib's literals stop at `i64`'s maximum.
fn uint_helpers() -> String {
    let mut out = String::new();
    for (ty, max, of_nat) in [
        ("u8", "255", "U8::of_u64"),
        ("u32", "4294967295", "U32::of_u64"),
    ] {
        let _ = write!(
            out,
            "\nfn extract_{ty}_of_decided(n: nat, o: Bool): Option({ty}) {{\n  if o {{ Some({of_nat}(U64::of_nat(n))) }} else {{ None }}\n}}\n\nfn extract_{ty}_of_nat(n: nat): Option({ty}) {{\n  if n <= {max} {{ Some({of_nat}(U64::of_nat(n))) }} else {{ None }}\n}}\n\nfn extract_{ty}_checked_add(a: {ty}, b: {ty}): Option({ty}) {{\n  if a <= {max} - b {{ Some(a + b) }} else {{ None }}\n}}\n\nfn extract_{ty}_checked_sub(a: {ty}, b: {ty}): Option({ty}) {{\n  if b <= a {{ Some(a - b) }} else {{ None }}\n}}\n\nfn extract_{ty}_checked_mul(a: {ty}, b: {ty}): Option({ty}) {{\n  if b == 0 || a <= div({max}, b) {{ Some(a * b) }} else {{ None }}\n}}\n"
        );
    }
    // `2^w`, and a width's value as a `nat` and back modulo `2^w`. Nib's
    // literals stop at `i64`'s maximum, so `2^64` is computed.
    for (ty, modulus, to_u64, of_u64) in [
        ("u8", "256", "U64::of_u8", "U8::of_u64"),
        ("u32", "4294967296", "U64::of_u32", "U32::of_u64"),
        ("u64", "(Nat::of_u64(9223372036854775807) + 1) * 2", "", ""),
    ] {
        let _ = write!(
            out,
            "\nfn extract_{ty}_modulus(): nat {{\n  {modulus}\n}}\n\nfn extract_{ty}_nat(x: {ty}): nat {{\n  Nat::of_u64({to_u64}(x))\n}}\n\nfn extract_{ty}_wrap(n: nat): {ty} {{\n  {of_u64}(U64::of_nat(mod(n, extract_{ty}_modulus())))\n}}\n"
        );
    }
    out.push_str(
        "\nfn extract_u64_of_decided(n: nat, o: Bool): Option(u64) {\n  if o { Some(U64::of_nat(n)) } else { None }\n}\n\nfn extract_u64_of_nat(n: nat): Option(u64) {\n  if n <= 9223372036854775807 * 2 + 1 { Some(U64::of_nat(n)) } else { None }\n}\n\n// `a + b` fits when half of it, rounded down, is at most `2^63 - 1`.\nfn extract_u64_checked_add(a: u64, b: u64): Option(u64) {\n  let h: u64 := 9223372036854775807\n  let odd := if mod(a, 2) == 1 && mod(b, 2) == 1 { 1 } else { 0 }\n  if div(a, 2) + div(b, 2) + odd <= h { Some(a + b) } else { None }\n}\n\nfn extract_u64_checked_sub(a: u64, b: u64): Option(u64) {\n  if b <= a { Some(a - b) } else { None }\n}\n\n// `a * b` fits when `a` is at most `(2^64 - 1) div b`, which is\n// `2 (h div b) + (2 (h mod b) + 1) div b` for `2 <= b <= h`.\nfn extract_u64_checked_mul(a: u64, b: u64): Option(u64) {\n  let h: u64 := 9223372036854775807\n  if a <= 1 || b <= 1 {\n    Some(a * b)\n  } else if b > h {\n    None\n  } else if a <= 2 * div(h, b) + div(2 * mod(h, b) + 1, b) {\n    Some(a * b)\n  } else {\n    None\n  }\n}\n",
    );
    out
}

/// The path the extracted declarations are read from when the program runs.
/// It is a file of no tote: its names are the ones the check resolved, so
/// another file's declaration of a prelude name never takes one over.
pub(crate) const EXTRACTED_PATH: &str = "extracted.taut";

/// Display markers around extracted Nib. Text markers carry no checking evidence.
pub const EXTRACTED_BEGIN: &str = "// tauto:extracted\n";
pub const EXTRACTED_END: &str = "// tauto:extracted-end\n";

/// Checks the files and extracts what they define, in the order checked.
/// Fails on rejected declarations, axiom dependencies, unsupported forms or
/// incomplete declarations. Unproved instance laws and proofs incomplete only
/// because they use those laws are erased and do not prevent extraction.
pub fn extract_files(roots: &[PathBuf]) -> Result<String, String> {
    let input = crate::read::check_files_for_extraction(roots, true, false)?;
    extract_checked(&input, false, roots).map(|(text, _, _)| text)
}

pub(crate) struct Extracted {
    pub texts: Vec<(PathBuf, String)>,
    pub total: HashSet<String>,
    /// For each file read again to run, whether each declaration its macros
    /// made, in order, runs as written. The text keeps the macro calls, so
    /// they make their declarations again; one the kernel read is in
    /// `extracted.taut` already and is left out.
    pub generated: HashMap<PathBuf, Vec<bool>>,
    /// The files each file read again imports, for what its names mean
    /// (`qualify::files`); every one reaches `extracted.taut`.
    pub imports: HashMap<PathBuf, Vec<PathBuf>>,
    /// The directories of the files that were checked, whether or not a
    /// file of theirs is read again to run: where the tables of a syntax
    /// they declare are, which an extracted `syn_parse` reads at run time.
    pub syntax_dirs: Vec<PathBuf>,
}

/// Whether `s` is a declaration a macro made: its span is one of an
/// expansion's, which no file's text has.
pub(crate) fn macro_made(s: &Stmt) -> bool {
    let span = match s {
        Stmt::Fn(f) => f.span,
        Stmt::Effect(e) => e.span,
        Stmt::Theorem(t) | Stmt::Def(t) => t.span,
        Stmt::Inductive(i) => i.span,
        Stmt::Class(c) => c.span,
        Stmt::Instance(i) => i.span,
        Stmt::Mutual { span, .. } => *span,
        _ => return false,
    };
    (crate::macros::EXPANSION_BASE..crate::surface::PRELUDE_BASE).contains(&span.start)
}

pub(crate) fn extract_tote(roots: &[PathBuf]) -> Result<Extracted, String> {
    let input = crate::read::check_files_for_extraction(roots, true, true)?;
    let (text, mut runtime, total) = extract_checked(&input, true, roots)?;
    if text
        != format!(
            "{EXTRACTED_BEGIN}{}\n{EXTRACTED_END}",
            crate::fmt::format(HELPERS).unwrap_or(HELPERS.into())
        )
    {
        runtime.insert(0, (PathBuf::from(EXTRACTED_PATH), text));
    }
    let generated = input
        .sources
        .iter()
        .filter(|(file, _)| runtime.iter().any(|(p, _)| *p == file.path))
        .map(|(file, stmts)| {
            let made = stmts.iter().filter(|s| macro_made(s));
            // A `mutual` block is kept whole, as its text would be.
            let runs = made
                .map(|s| matches!(s, Stmt::Mutual { .. }) || executable(s, &input.checked.runtime));
            (file.path.clone(), runs.collect())
        })
        .collect();
    let extracted = PathBuf::from("extracted.taut");
    // A file left out (one with nothing to run) is passed through: a file
    // importing it reaches what it imports, as it did when it was checked.
    let canon = |p: &PathBuf| std::fs::canonicalize(p).unwrap_or_else(|_| p.clone());
    let kept: HashSet<PathBuf> = runtime.iter().map(|(p, _)| canon(p)).collect();
    let imported: HashMap<PathBuf, &Vec<PathBuf>> =
        input.imports.iter().map(|(p, v)| (canon(p), v)).collect();
    let mut imports: HashMap<PathBuf, Vec<PathBuf>> = HashMap::new();
    for (path, direct) in &input.imports {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        let mut todo: Vec<&PathBuf> = direct.iter().rev().collect();
        while let Some(t) = todo.pop() {
            let c = canon(t);
            if !seen.insert(c.clone()) {
                continue;
            }
            if kept.contains(&c) {
                out.push(t.clone());
            } else if let Some(next) = imported.get(&c) {
                todo.extend(next.iter().rev());
            }
        }
        imports.insert(path.clone(), out);
    }
    for (path, _) in &runtime {
        if *path != extracted {
            imports
                .entry(path.clone())
                .or_default()
                .push(extracted.clone());
        }
    }
    let mut syntax_dirs: Vec<PathBuf> = Vec::new();
    for (file, _) in &input.sources {
        if let Some(dir) = file.path.parent()
            && !syntax_dirs.iter().any(|d| d == dir)
        {
            syntax_dirs.push(dir.to_path_buf());
        }
    }
    Ok(Extracted {
        texts: runtime,
        total,
        generated,
        imports,
        syntax_dirs,
    })
}

/// An axiom of `std/Float.taut` that extraction maps onto a builtin of Nib
/// (`Float::exp`, `Text::of_float`, …): a function the proofs know nothing of,
/// trusted as the mapped functions are. `Quot::sound` is a proof and is
/// erased: a quotient is extracted as its representation, which a program
/// reads only through `Quot_lift`, giving related values the same result.
fn mapped_axiom(name: &str) -> bool {
    // The axiom is named under the module of its type (`Float::exp`,
    // `Text::of_float`), after the module of its file if any.
    name == crate::check::QUOT_SOUND
        || ["Float::", "Float32::", "Text::"].iter().any(|m| {
            let f = match name.rfind(&format!("::{m}")) {
                Some(i) => &name[i + 2..],
                None => name,
            };
            f.starts_with(m) && mapped_fn(f).is_some()
        })
}

/// The declarations of the proof language in `prefix` that the kernel
/// accepts without axioms, extracted as Nib source, for a macro to call
/// while the program is read: a macro's function is executable code, and the
/// files before it are not extracted yet. What the kernel does not accept,
/// or does not read (executable code), is left out, with what depends on it.
pub(crate) fn executable_prefix(prefix: &[Stmt]) -> Result<String, String> {
    use crate::surface::qualify::{SEPARATOR, declared};
    // The files before keep their modules (`module Nat { … }`) until the
    // whole program is read; the kernel takes their functions by full name.
    let flat = crate::surface::modules::resolve_with(
        prefix.to_vec(),
        &crate::surface::effect_sets::Sets::new(),
        crate::program::prelude_module_names(),
    )
    .0;
    let prefix = flat.as_slice();
    let mut kernel = crate::check::Kernel::new();
    let prelude_names = crate::check::declare_prelude(&mut kernel)?;
    let path = PathBuf::from("macro library");
    let mut kept = Vec::new();
    let mut out = Vec::new();
    for s in prefix {
        let entries = kernel.declare_program(&crate::surface::Program {
            stmts: vec![s.clone()],
            errors: Vec::new(),
        });
        let accepted = !entries.is_empty()
            && entries
                .iter()
                .all(|e| matches!(&e.verdict, Verdict::Checked { axioms } if axioms.is_empty()));
        let proof_language = matches!(
            s,
            Stmt::Inductive(_)
                | Stmt::Fn(_)
                | Stmt::Theorem(_)
                | Stmt::Def(_)
                | Stmt::Class(_)
                | Stmt::Instance(_)
                | Stmt::Mutual { .. }
        );
        // A function of `std/` that extraction maps onto Nib (`Bool.or` is
        // `||`), or that Nib's prelude has (`Nat.max`), is not written: the
        // name would be declared twice.
        let mapped = matches!(
            s,
            Stmt::Fn(f) if (mapped_fn(&f.name).is_some() || nib_prelude_fn(&f.name))
                && std_declared().contains(&f.name)
        );
        if accepted && proof_language && !mapped {
            kept.push(s.clone());
        }
        out.extend(entries.into_iter().map(|entry| crate::check::FileEntry {
            file: path.clone(),
            entry,
        }));
    }
    let checked = crate::check::checked_entries(kernel, vec![path.clone()], out, prelude_names);
    // A name of `std/` is qualified by its module (`std::Nat::add`).
    let std_prefix = format!("std{SEPARATOR}");
    let mut own = HashSet::new();
    let mut std = HashSet::new();
    for s in prefix {
        declared(s, &mut |n| {
            if n.starts_with(&std_prefix) || std_declared().contains(n) {
                std.insert(n.to_string());
            } else {
                own.insert(n.to_string());
            }
        });
    }
    let mut std_names = StdNames::new(&[]);
    std_names.own = own;
    std_names.std = std;
    let mut ex = Extractor {
        checked: &checked,
        generated: HashSet::new(),
        out: String::from(HELPERS),
        fresh: 0,
        mixed: false,
        needed: HashSet::new(),
        runtime: Vec::new(),
        total: HashSet::new(),
        thunks: HashSet::new(),
        std: &std_names,
        written: HashSet::new(),
        pending: Vec::new(),
        unused: HashSet::new(),
        aliases: type_aliases(&checked, &kept),
        proof_takers: HashSet::new(),
        refined_takers: HashSet::new(),
    };
    if checked.families.contains_key("Text") {
        ex.out.push_str(TEXT_HELPERS);
    }
    if checked.families.contains_key("U64") {
        ex.out.push_str(&uint_helpers());
    }
    if checked.families.contains_key("I64") {
        ex.out.push_str(&sint_helpers());
    }
    let file = crate::program::SourceFile {
        path,
        base: 0,
        text: String::new(),
    };
    // One declaration extraction cannot write is left out, with what calls it,
    // which the checker of executable code then leaves out.
    for s in &kept {
        let (out, fresh) = (ex.out.len(), ex.fresh);
        if ex.file(&file, std::slice::from_ref(s)).is_err() {
            ex.out.truncate(out);
            ex.fresh = fresh;
        }
    }
    Ok(legal_names(&ex.out).0)
}

/// The full names the files of `std/` declare (`Bool.or`), which the files
/// before a macro hold as they are written, without `std.` before them.
fn std_declared() -> &'static HashSet<String> {
    static NAMES: std::sync::OnceLock<HashSet<String>> = std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        let mut names = HashSet::new();
        for (_, text) in crate::stdlib::FILES {
            let Ok(p) = crate::surface::parse_program_unresolved_at(text, 0) else {
                continue;
            };
            let (stmts, _) = crate::surface::modules::resolve_with(
                p.stmts,
                &crate::surface::effect_sets::Sets::new(),
                crate::program::prelude_module_names(),
            );
            for s in &stmts {
                crate::surface::qualify::declared(s, &mut |n| {
                    names.insert(n.to_string());
                });
            }
        }
        names
    })
}

fn extract_checked(
    input: &crate::read::ExtractionInput,
    mixed: bool,
    roots: &[PathBuf],
) -> Result<(String, Vec<(PathBuf, String)>, HashSet<String>), String> {
    let checked = &input.checked;
    let mut problems = Vec::new();
    let unproved = unproved_laws(&checked);
    let generated = generated_nib_names(input);
    let unused = if mixed {
        HashSet::new()
    } else {
        unused_imported(input, roots)
    };
    for e in &checked.entries {
        match &e.entry.verdict {
            // What `inductive_syntax!` makes for Nib (the tree `<syntax>.parse` reads, the reader and
            // `<syntax>.<Type>.to_i`) is written out as Nib, not extracted.
            Verdict::Skipped(_) if generated.contains(&e.entry.name) => {}
            // A function with effects the kernel does not read runs as written.
            // One the kernel read and rejected is an error like any other.
            Verdict::Skipped(_) if mixed && checked.runtime.contains(&e.entry.name) => {}
            // An imported function nothing extracted reaches, such as one a
            // macro runs while the program is read, is not written out.
            Verdict::Skipped(_) if unused.contains(&e.entry.name) => {}
            // A law an instance does not prove leaves its record of laws
            // incomplete, and the proofs that use it; they are erased, and
            // the program still runs.
            Verdict::Incomplete { .. } if !mixed && unproved.contains(&e.entry.name) => {}
            Verdict::Checked { axioms } if !axioms.iter().all(|a| mapped_axiom(a)) => problems
                .push(format!(
                    "{}: {}",
                    e.file.display(),
                    msg!(
                        "tauto-extract-uses-axioms",
                        name = &e.entry.name,
                        axioms = axioms.join(", ")
                    )
                )),
            Verdict::Failed(d) => {
                // `file:line:col:`, as a type error from the run says where it is.
                let place = d
                    .span
                    .and_then(|sp| {
                        let text = std::fs::read_to_string(&e.file).ok()?;
                        let (l, c) = crate::report::line_col(&text, sp.start as usize);
                        Some(format!("{}:{l}:{c}", e.file.display()))
                    })
                    .unwrap_or_else(|| e.file.display().to_string());
                problems.push(format!("{place}: {}: {}", e.entry.name, d.message))
            }
            Verdict::Incomplete { .. } => problems.push(format!(
                "{}: {}",
                e.file.display(),
                msg!("tauto-extract-incomplete", name = &e.entry.name)
            )),
            Verdict::Skipped(why) => problems.push(format!(
                "{}: {}",
                e.file.display(),
                msg!(
                    "tauto-extract-skipped",
                    name = &e.entry.name,
                    why = why.as_str()
                )
            )),
            Verdict::Checked { .. } => {}
        }
    }
    if !problems.is_empty() {
        return Err(problems.join("\n"));
    }
    let std = StdNames::new(&input.sources);
    let mut ex = Extractor {
        checked: &checked,
        generated: generated.clone(),
        out: String::from(HELPERS),
        fresh: 0,
        mixed,
        needed: if mixed {
            reachable(input, roots)?
        } else {
            HashSet::new()
        },
        runtime: Vec::new(),
        total: HashSet::new(),
        thunks: HashSet::new(),
        std: &std,
        written: HashSet::new(),
        pending: Vec::new(),
        unused,
        aliases: type_aliases(checked, input.sources.iter().flat_map(|(_, s)| s)),
        proof_takers: HashSet::new(),
        refined_takers: HashSet::new(),
    };
    if checked.families.contains_key("Text") {
        ex.out.push_str(TEXT_HELPERS);
    }
    if checked.families.contains_key("U64") {
        ex.out.push_str(&uint_helpers());
    }
    if checked.families.contains_key("I64") {
        ex.out.push_str(&sint_helpers());
    }
    for (file, stmts) in &input.sources {
        ex.file(file, stmts)?;
    }
    if mixed {
        ex.kernel_functions()?;
        ex.runtime_files()?;
    }
    let (out, renamed) = legal_names(&ex.out);
    let total = ex
        .total
        .into_iter()
        .map(|n| renamed.get(&n).cloned().unwrap_or(n))
        .collect();
    // Laid out as `tauto fmt` would, for whoever reads `tauto extract`.
    let text = crate::fmt::format(&out).unwrap_or(out);
    Ok((
        format!("{EXTRACTED_BEGIN}{text}\n{EXTRACTED_END}"),
        ex.runtime,
        total,
    ))
}

/// `text` with each name a macro expansion made hygienic (`x#3`, `x#r3`),
/// which no source can spell, written as a name that can be read back
/// (`x_3`, or another number when that is taken), and those renamings.
/// Each such name is unique, so a fresh name for each keeps what refers to what.
/// A local as an expression. A name spelled like a reserved word is written `r#name`. A name that
/// is a keyword only by what follows it (`if label {`) is written in parentheses, which the
/// keyword never is followed by.
fn local_name(n: &str) -> String {
    const CONTEXTUAL: &[&str] = &["as", "syntax"];
    if crate::surface::print::RESERVED.contains(&n) {
        raw(n)
    } else if CONTEXTUAL.contains(&n) {
        format!("({n})")
    } else {
        n.to_string()
    }
}

/// `A::b::c` written as a chain of fields over a name.
fn dotted(t: &crate::surface::SurfaceTerm) -> Option<String> {
    match &*t.kind {
        TermKind::Var(n) => Some(n.clone()),
        TermKind::Field { base, name } => Some(format!("{}::{name}", dotted(base)?)),
        _ => None,
    }
}

/// `decl` in the module `module`, each segment of a path `a.b` opening one
/// module inside the one before it, as Nib has no dotted module names.
fn in_modules(module: Option<&str>, decl: &str) -> String {
    let Some(module) = module else {
        return decl.to_string();
    };
    let segments: Vec<&str> = module.split("::").collect();
    let mut out = String::new();
    for (depth, m) in segments.iter().enumerate() {
        let _ = writeln!(out, "{}module {m} {{", "  ".repeat(depth));
    }
    let indent = "  ".repeat(segments.len());
    for line in decl.lines() {
        let _ = writeln!(out, "{indent}{line}");
    }
    for depth in (0..segments.len()).rev() {
        let _ = write!(out, "{}}}", "  ".repeat(depth));
        if depth > 0 {
            out.push('\n');
        }
    }
    out
}

fn legal_names(text: &str) -> (String, HashMap<String, String>) {
    let ident = |c: char| c.is_alphanumeric() || c == '_';
    let mut words: Vec<(bool, &str)> = Vec::new();
    let mut rest = text;
    while let Some(c) = rest.chars().next() {
        let len = if c == '"' {
            let mut escaped = false;
            rest[1..]
                .char_indices()
                .find(|&(_, c)| {
                    let end = c == '"' && !escaped;
                    escaped = c == '\\' && !escaped;
                    end
                })
                .map_or(rest.len(), |(i, _)| i + 2)
        } else if rest.starts_with("//") {
            rest.find('\n').unwrap_or(rest.len())
        } else if ident(c) {
            let mut end = rest.find(|c| !ident(c)).unwrap_or(rest.len());
            if let Some(after) = rest[end..].strip_prefix('#') {
                let digits = after.strip_prefix('r').unwrap_or(after);
                let n = digits
                    .find(|c: char| !c.is_ascii_digit())
                    .unwrap_or(digits.len());
                if n > 0 {
                    end = rest.len() - digits.len() + n;
                    words.push((true, &rest[..end]));
                    rest = &rest[end..];
                    continue;
                }
            }
            end
        } else {
            c.len_utf8()
        };
        words.push((false, &rest[..len]));
        rest = &rest[len..];
    }
    let mut taken: HashSet<String> = words
        .iter()
        .filter(|(h, w)| !h && w.starts_with(ident))
        .map(|(_, w)| w.to_string())
        .collect();
    let mut renamed: HashMap<String, String> = HashMap::new();
    let mut out = String::with_capacity(text.len());
    for (hygienic, w) in words {
        if !hygienic {
            out.push_str(w);
            continue;
        }
        if !renamed.contains_key(w) {
            let plain = &w[..w.find('#').unwrap_or(w.len())];
            let name = (1..)
                .map(|k| format!("{plain}_{k}"))
                .find(|n| !taken.contains(n))
                .unwrap_or_default();
            taken.insert(name.clone());
            renamed.insert(w.to_string(), name);
        }
        out.push_str(&renamed[w]);
    }
    (out, renamed)
}

/// The declarations that are incomplete only for laws that were not written:
/// those with such holes, and what uses only those.
fn unproved_laws(checked: &Checked) -> HashSet<String> {
    let mut out: HashSet<String> = HashSet::new();
    loop {
        let before = out.len();
        for e in &checked.entries {
            if let Verdict::Incomplete { holes, uses } = &e.entry.verdict
                && holes.iter().all(|h| h.name.starts_with("law:"))
                && uses.iter().all(|u| out.contains(u))
            {
                out.insert(e.entry.name.clone());
            }
        }
        if out.len() == before {
            return out;
        }
    }
}

/// A `def` as the function it is when executable code calls it: its
/// generics stay generics, its other parameters and its type become the
/// function's, and its body is checked as the function's would be. Its
/// signature in the kernel (`Checked::signatures`) covers the generics and
/// the parameters alike, as a function's does.
fn def_as_fn(t: &crate::surface::TheoremDecl) -> Option<FnDecl> {
    let body = t.body.clone()?;
    let (generics, params) = t.params.split_at(t.implicit.min(t.params.len()));
    Some(FnDecl {
        budget: None,
        vis: Default::default(),
        name: t.name.clone(),
        generics: Vec::new(),
        rows: Vec::new(),
        bounds: Vec::new(),
        bound_spans: Vec::new(),
        params: generics
            .iter()
            .chain(params)
            .map(|(n, _)| n.clone())
            .collect(),
        borrows: vec![None; t.params.len()],
        param_types: t.params.iter().map(|(_, ty)| Some(ty.clone())).collect(),
        result: Some(t.ty.clone()),
        effects: None,
        where_: Vec::new(),
        span: t.span,
        opaque: false,
        decreasing_by: None,
        generates: None,
        body,
    })
}

fn executable(s: &Stmt, runtime: &HashSet<String>) -> bool {
    match s {
        Stmt::Fn(f) => runtime.contains(&f.name),
        Stmt::Effect(e) => runtime.contains(&e.name),
        // An `inductive enum` the kernel reads is extracted with the
        // functions over it, which name its constructors.
        Stmt::Enum(d) => runtime.contains(&d.name),
        Stmt::Inductive(_)
        | Stmt::Theorem(_)
        | Stmt::Def(_)
        | Stmt::Import { .. }
        | Stmt::Class(_)
        | Stmt::Instance(_)
        | Stmt::Mutual { .. } => false,
        _ => true,
    }
}

/// What the executable code needs to know of the constructors of the
/// proofs: the struct a constructor builds, if it builds one, and whether a
/// name is a constructor.
struct Ctors<'a> {
    struct_of: &'a dyn Fn(&str) -> Option<String>,
    is_ctor: &'a dyn Fn(&str) -> bool,
    /// The path of a variant that kept its short name inside a type written
    /// out in modules ([`Extractor::qualified_ctor`]).
    qualified: &'a dyn Fn(&str) -> Option<String>,
}

fn runtime_source(
    text: &str,
    base: u32,
    stmts: &[Stmt],
    runtime: &HashSet<String>,
    std: &StdNames,
    written: &HashSet<String>,
    ctors: Ctors,
) -> String {
    let Ctors {
        struct_of,
        is_ctor,
        qualified,
    } = ctors;
    fn range(span: tauto_parol::Span, base: u32) -> std::ops::Range<usize> {
        span.start.saturating_sub(base) as usize..span.end.saturating_sub(base) as usize
    }
    fn blank(bytes: &mut [u8], span: tauto_parol::Span, base: u32) {
        let Some(bytes) = bytes.get_mut(range(span, base)) else {
            return;
        };
        for b in bytes {
            if *b != b'\n' && *b != b'\r' {
                *b = b' ';
            }
        }
    }
    fn erase(
        bytes: &mut [u8],
        original: &[u8],
        base: u32,
        stmts: &[Stmt],
        runtime: &HashSet<String>,
    ) {
        for s in stmts {
            if executable(s, runtime) {
                continue;
            }
            let span = match s {
                Stmt::Fn(f) => f.span,
                // An effect the proofs read is declared once, where it is
                // extracted, so that the code that runs handles that effect.
                Stmt::Effect(e) => e.span,
                Stmt::Theorem(t) | Stmt::Def(t) => t.span,
                Stmt::Inductive(i) => i.span,
                Stmt::Enum(d) => d.span,
                // An import is kept: what the file's names mean when it runs
                // is what its imports made them mean when it was checked.
                Stmt::Import { .. } => continue,
                Stmt::Class(c) => c.span,
                Stmt::Instance(i) => i.span,
                Stmt::Mutual { items, span } => {
                    blank(bytes, *span, base);
                    for item in items {
                        if let Stmt::Fn(f) = item
                            && runtime.contains(&f.name)
                        {
                            let r = range(f.span, base);
                            if let (Some(to), Some(from)) =
                                (bytes.get_mut(r.clone()), original.get(r))
                            {
                                to.copy_from_slice(from);
                            }
                        }
                    }
                    continue;
                }
                _ => continue,
            };
            blank(bytes, span, base);
        }
    }
    let mut bytes = text.as_bytes().to_vec();
    // An import is kept: the file is read again to run with the imports it
    // was checked with, so that its names mean what they meant then. A
    // macro call that makes statements is erased: what it made is in the
    // expanded statements, and calling it again would declare it twice.
    if let Ok(written) = crate::surface::parse_program_unresolved_at(text, base) {
        for stmt in &written.stmts {
            match stmt {
                Stmt::Called { span, .. } => blank(&mut bytes, *span, base),
                Stmt::Attributed { stmt, span, .. } => {
                    // The declaration an attribute is given stays as written
                    // when the macro kept it; the attribute is erased.
                    blank(&mut bytes, *span, base);
                    if let Some(d) = stmt_span(stmt) {
                        blank(
                            &mut bytes,
                            tauto_parol::Span::new(span.start, d.start),
                            base,
                        );
                        if !stmts.iter().any(|s| stmt_span(s) == Some(d)) {
                            blank(&mut bytes, d, base);
                        }
                    }
                }
                _ => {}
            }
        }
    }
    erase(&mut bytes, text.as_bytes(), base, stmts, runtime);
    // An `include_text!` that is kept is written as the literal it was read
    // as: the source is read again without the file it was in. The literal
    // has no line break, so the lines after it stay where they were.
    let mut included: Vec<(tauto_parol::Span, String)> = Vec::new();
    let mut kept: Vec<Stmt> = Vec::new();
    for s in stmts {
        match s {
            Stmt::Mutual { items, .. } => kept.extend(
                items
                    .iter()
                    .filter(|i| matches!(i, Stmt::Fn(f) if runtime.contains(&f.name)))
                    .cloned(),
            ),
            s if executable(s, runtime) => kept.push(s.clone()),
            _ => {}
        }
    }
    // What a macro made has no text of its own here: it is printed after
    // the written source, so that the lines before it stay where they were.
    let (made, mut kept): (Vec<Stmt>, Vec<Stmt>) = kept.into_iter().partition(made_by_macro);
    for s in &mut kept {
        crate::surface::walk::stmt(s, &mut |t| {
            if let TermKind::Text(value) = &*t.kind
                && text
                    .get(range(t.span, base))
                    .is_some_and(|w| w.starts_with(crate::program::include::NAME))
            {
                included.push((t.span, crate::surface::print::quoted(value)));
            }
        });
    }
    // The families and constructors of `std/` that extraction maps onto Nib
    // are written as Nib writes them in the executable code too (`Succ(n)`
    // as `(n + 1)`, `Nat` as `nat`), so that it can call what was extracted.
    for s in &mut kept {
        crate::surface::walk::stmt(s, &mut |t| match &*t.kind {
            TermKind::Var(n) if !runtime.contains(n) && std.of(n).is_some() => {
                let mapped = match std.of(n).unwrap_or(n) {
                    m @ ("Zero" | "true" | "false" | "Star") => mapped_ctor(m, &[]),
                    m @ ("Nat" | "Bool" | "Unit" | "Stack") => mapped_type(m).map(str::to_string),
                    _ => None,
                };
                if let Some(m) = mapped {
                    included.push((t.span, m));
                }
            }
            // A constructor without arguments is a value of Nib, not a
            // function: `hi()` as `hi`, as extraction writes it.
            TermKind::App {
                function,
                arguments,
            } if arguments.is_empty()
                && matches!(&*function.kind, TermKind::Var(n) if !runtime.contains(n) && std.of(n).is_none() && is_ctor(n) && struct_of(n).is_none()) =>
            {
                included.push((
                    tauto_parol::Span::new(function.span.end, t.span.end),
                    String::new(),
                ));
            }
            // A function of `std/` that is written out at each call
            // (`stack_len(&s)`) has no function to call: the call is written
            // as the proofs' calls are. Only the text around the arguments is
            // replaced, so that what is rewritten inside them stays apart.
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(n) if !runtime.contains(n) && (std.of(n).is_some_and(inline_only) || std.written_by_mapping(n))) =>
            {
                let TermKind::Var(n) = &*function.kind else {
                    unreachable!()
                };
                if let Some(template) = std.of(n).and_then(mapped_fn) {
                    // The template between its holes, which come in order.
                    let mut pieces = Vec::new();
                    let mut rest = template;
                    for k in 0..arguments.len() {
                        let hole = format!("${k}");
                        let Some((before, after)) = rest.split_once(hole.as_str()) else {
                            return;
                        };
                        pieces.push(before);
                        rest = after;
                    }
                    let mut start = t.span.start;
                    // Each argument is put in parentheses, as `fill` puts it.
                    for (k, (piece, a)) in pieces.iter().zip(arguments).enumerate() {
                        let close = if k == 0 { "" } else { ")" };
                        included.push((
                            tauto_parol::Span::new(start, a.span.start),
                            format!("{close}{piece}("),
                        ));
                        start = a.span.end;
                    }
                    let close = if arguments.is_empty() { "" } else { ")" };
                    included.push((
                        tauto_parol::Span::new(start, t.span.end),
                        format!("{close}{rest}"),
                    ));
                }
            }
            TermKind::App {
                function,
                arguments,
            } if arguments.len() == 1
                && matches!(&*function.kind, TermKind::Var(n) if std.of(n) == Some("Succ") && !runtime.contains(n)) =>
            {
                let x = arguments[0].span;
                included.push((tauto_parol::Span::new(t.span.start, x.start), "(".into()));
                included.push((tauto_parol::Span::new(x.end, t.span.end), " + 1)".into()));
            }
            _ => {}
        });
    }
    // A function of `std/` the proofs read is extracted by its full name
    // (`std::Text::Text::len`), and the executable code is read again
    // without its imports. A call is written by the full name it was
    // resolved to, so that it means the function the proofs checked, not a
    // builtin of the prelude that has the same short name. So is a family or
    // a constructor the proofs declare: renamed to its full name because
    // another file has its name, it is extracted by that name, and read
    // again the short name would mean the other file's declaration.
    for s in &mut kept {
        crate::surface::walk::stmt(s, &mut |t| {
            if let TermKind::Var(n) = &*t.kind
                && n.contains(crate::surface::qualify::SEPARATOR)
                && written.contains(n)
                && !runtime.contains(n)
                && text.get(range(t.span, base)).is_some_and(|w| w != n)
            {
                included.push((t.span, n.clone()));
            }
        });
    }
    // A variant that kept its short name is declared inside the modules of
    // its type when that type was renamed to its full name (a program's
    // `Pending` against the prelude's), and read again the short name finds
    // no variant: it is written by the path of its type.
    for s in &mut kept {
        crate::surface::walk::stmt(s, &mut |t| {
            if let TermKind::Var(n) = &*t.kind
                && !runtime.contains(n)
                && let Some(q) = qualified(n)
                && text.get(range(t.span, base)).is_some_and(|w| w == n)
            {
                included.push((t.span, q));
            }
        });
    }
    // The one constructor of a family extracted as a struct is matched as
    // Nib matches a struct by position: `usage(a, b)` as `Usage(a, b)`.
    for s in &mut kept {
        crate::surface::walk::stmt(s, &mut |t| {
            let TermKind::Match {
                scrutinee,
                result,
                arms,
                ..
            } = &*t.kind
            else {
                return;
            };
            // A match on `Nat` with a `Succ` pattern is written as the
            // chain of tests extraction writes for it, since a `nat` of Nib
            // has no constructors to match: the arms in order, the last one
            // taken when the others are not, as the kernel checked them to
            // cover every value.
            if let Some(chain) = nat_chain(arms, std, runtime, t.span.start) {
                let (first, rest) = chain.split_first().expect("a chain has an arm");
                // The line breaks of what is replaced stay, so that the lines
                // after it stay where they were.
                let lines = |span: tauto_parol::Span| {
                    let n = text
                        .get(range(span, base))
                        .map_or(0, |w| w.matches('\n').count());
                    "\n".repeat(n)
                };
                let mut push = |(span, s): (tauto_parol::Span, String)| {
                    let s = s + &lines(span);
                    included.push((span, s));
                };
                push((
                    tauto_parol::Span::new(t.span.start, scrutinee.span.start),
                    format!("{{ let {} := ", nat_subject(t.span.start)),
                ));
                push((
                    tauto_parol::Span::new(scrutinee.span.end, arms[0].body.span.start),
                    format!("; {first}"),
                ));
                for (k, open) in rest.iter().enumerate() {
                    push((
                        tauto_parol::Span::new(arms[k].body.span.end, arms[k + 1].body.span.start),
                        format!(" }} {open}"),
                    ));
                }
                let last = arms[arms.len() - 1].body.span.end;
                push((tauto_parol::Span::new(last, t.span.end), " } }".into()));
                return;
            }
            let mut start = scrutinee.span.end;
            if let Some(r) = result {
                start = start.max(r.span.end);
            }
            for arm in arms {
                let end = arm.body.span.start;
                let mut names = Vec::new();
                pattern_ctors(&arm.pattern, &mut names);
                // A constructor is written in the pattern by its short name,
                // and read again by the name it is extracted as: its family's
                // when matched as a struct, else its full name when it was
                // renamed to one.
                let mut renamed: Vec<(&str, String)> = names
                    .into_iter()
                    .filter_map(|n| {
                        let word = crate::surface::qualify::short(n);
                        match struct_of(n) {
                            Some(s) => Some((word, s)),
                            None if word != n && written.contains(n) && !runtime.contains(n) => {
                                Some((word, n.to_string()))
                            }
                            None if !runtime.contains(n) => qualified(n).map(|q| (word, q)),
                            None => None,
                        }
                    })
                    .collect();
                // A nullary constructor that extraction maps onto a Nib
                // literal is matched as that literal: `Zero` as `0`, not
                // as a name that binds whatever the value is. One renamed to
                // its full name is matched by that name, as above.
                let mut binds = Vec::new();
                pattern_binds(&arm.pattern, &mut binds);
                renamed.extend(binds.into_iter().filter_map(|n| {
                    if runtime.contains(n) {
                        return None;
                    }
                    let word = crate::surface::qualify::short(n);
                    if word != n && written.contains(n) {
                        return Some((word, n.to_string()));
                    }
                    if let Some(q) = qualified(n) {
                        return Some((word, q));
                    }
                    match std.of(n)? {
                        m @ ("Zero" | "true" | "false") => mapped_ctor(m, &[]).map(|l| (n, l)),
                        _ => None,
                    }
                }));
                if !renamed.is_empty() {
                    let skipped: Vec<tauto_parol::Span> =
                        arm.guard.iter().chain(&arm.goal).map(|g| g.span).collect();
                    for (at, word) in words(text, base, start, end) {
                        if skipped.iter().any(|g| g.start <= at && at < g.end) {
                            continue;
                        }
                        if let Some((_, s)) = renamed.iter().find(|(n, _)| *n == word) {
                            let span = tauto_parol::Span::new(at, at + word.len() as u32);
                            included.push((span, s.clone()));
                        }
                    }
                }
                start = arm.body.span.end;
            }
        });
    }
    included.sort_by_key(|(span, _)| std::cmp::Reverse(span.start));
    for (span, literal) in included {
        bytes.splice(range(span, base), literal.into_bytes());
    }
    let mut out = String::from_utf8(bytes).expect("erasing source preserves UTF-8");
    if !made.is_empty() {
        out.push('\n');
        // A name a hygienic macro renamed (`x#1`) is written as Nib names one.
        out.push_str(&legal_names(&crate::surface::print::print_stmts(&made)).0);
    }
    out
}

/// Whether a macro made `s`: it was not written, so it has no place in the
/// written text.
fn made_by_macro(s: &Stmt) -> bool {
    let at = match s {
        Stmt::Expr(t) | Stmt::Return(Some(t)) => t.span,
        Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
            value.span
        }
        Stmt::While { condition, .. } => condition.span,
        s => match stmt_span(s) {
            Some(span) => span,
            None => return false,
        },
    };
    at.start >= crate::macros::EXPANSION_BASE
}

/// Where a declaration is written; `None` for a statement that is not one.
fn stmt_span(s: &Stmt) -> Option<tauto_parol::Span> {
    Some(match s {
        Stmt::Fn(f) => f.span,
        Stmt::Effect(e) => e.span,
        Stmt::Theorem(t) | Stmt::Def(t) => t.span,
        Stmt::Inductive(i) => i.span,
        Stmt::Class(c) => c.span,
        Stmt::Instance(i) => i.span,
        Stmt::Struct(d) | Stmt::Enum(d) => d.span,
        Stmt::Mutual { span, .. }
        | Stmt::Module { span, .. }
        | Stmt::Extern { span, .. }
        | Stmt::Import { span, .. }
        | Stmt::Called { span, .. }
        | Stmt::Attributed { span, .. } => *span,
        _ => return None,
    })
}

/// The name the subject of a match on `Nat` is bound to, by where the
/// match starts.
fn nat_subject(at: u32) -> String {
    format!("extract_nat_{at}")
}

/// A match on `Nat` that names `Succ`, as what opens each arm of its chain
/// of tests (`if s >= 1 { let k = (s - 1); `, then `else if …`, and `else {`
/// for the last arm); `None` when no arm names `Succ` or an arm cannot be
/// written so (a guard, a goal, a pattern that is not on `Nat`).
fn nat_chain(
    arms: &[MatchArm],
    std: &StdNames,
    runtime: &HashSet<String>,
    at: u32,
) -> Option<Vec<String>> {
    fn succ_in(p: &Pattern, std: &StdNames, runtime: &HashSet<String>) -> bool {
        matches!(p, Pattern::Ctor { name, .. } if !runtime.contains(name) && std.of(name) == Some("Succ"))
    }
    fn test(
        p: &Pattern,
        at: &str,
        std: &StdNames,
        runtime: &HashSet<String>,
        tests: &mut Vec<String>,
        binds: &mut Vec<String>,
    ) -> Option<()> {
        fn short<'n>(n: &'n str, std: &StdNames, runtime: &HashSet<String>) -> Option<&'n str> {
            if runtime.contains(n) { None } else { std.of(n) }
        }
        let mapped = |n| short(n, std, runtime);
        match p {
            Pattern::Wild => {}
            Pattern::Bind(n) if mapped(n) == Some("Zero") => tests.push(format!("{at} == 0")),
            Pattern::Bind(n) if mapped(n).is_none() => {
                binds.push(format!("let {} := {at};", raw(n)))
            }
            Pattern::Int(k) => tests.push(format!("{at} == {k}")),
            Pattern::Ctor { name, args } => match (mapped(name)?, args.as_slice()) {
                ("Zero", []) => tests.push(format!("{at} == 0")),
                ("Succ", [q]) => {
                    tests.push(format!("{at} >= 1"));
                    test(q, &format!("({at} - 1)"), std, runtime, tests, binds)?;
                }
                _ => return None,
            },
            _ => return None,
        }
        Some(())
    }
    if !arms.iter().any(|a| succ_in(&a.pattern, std, runtime)) {
        return None;
    }
    let subject = nat_subject(at);
    let n = arms.len();
    let mut out = Vec::new();
    for (k, arm) in arms.iter().enumerate() {
        if arm.guard.is_some() || arm.goal.is_some() {
            return None;
        }
        let mut tests = Vec::new();
        let mut binds = Vec::new();
        test(&arm.pattern, &subject, std, runtime, &mut tests, &mut binds)?;
        let binds = binds.iter().map(|b| format!("{b} ")).collect::<String>();
        let open = if k + 1 == n {
            if k == 0 {
                "{ ".to_string()
            } else {
                "else { ".to_string()
            }
        } else {
            let test = if tests.is_empty() {
                "true".to_string()
            } else {
                tests.join(" && ")
            };
            if k == 0 {
                format!("if {test} {{ ")
            } else {
                format!("else if {test} {{ ")
            }
        };
        out.push(format!("{open}{binds}"));
    }
    Some(out)
}

/// The constructors a pattern names.
fn pattern_ctors<'p>(p: &'p Pattern, out: &mut Vec<&'p str>) {
    match p {
        Pattern::Ctor { name, args } => {
            out.push(name);
            for a in args {
                pattern_ctors(a, out);
            }
        }
        Pattern::Record { fields, .. } => {
            for (_, f) in fields {
                pattern_ctors(f, out);
            }
        }
        Pattern::Tuple(items) => items.iter().for_each(|q| pattern_ctors(q, out)),
        _ => {}
    }
}

/// The names a pattern binds, a nullary constructor among them.
fn pattern_binds<'p>(p: &'p Pattern, out: &mut Vec<&'p str>) {
    match p {
        Pattern::Bind(name) => out.push(name),
        Pattern::Ctor { args, .. } => {
            for a in args {
                pattern_binds(a, out);
            }
        }
        Pattern::Record { fields, .. } => {
            for (_, f) in fields {
                pattern_binds(f, out);
            }
        }
        Pattern::Tuple(items) => items.iter().for_each(|q| pattern_binds(q, out)),
        _ => {}
    }
}

/// The identifiers written between `start` and `end`, with where each
/// starts; a name after `.` or `::` is a field or a path, not a word.
fn words(text: &str, base: u32, start: u32, end: u32) -> Vec<(u32, &str)> {
    let from = start.saturating_sub(base) as usize;
    let to = (end.saturating_sub(base) as usize).min(text.len());
    let bytes = text.as_bytes();
    let word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut out = Vec::new();
    let mut i = from;
    while i < to {
        if word(bytes[i]) && (i == 0 || !word(bytes[i - 1])) {
            let mut j = i;
            while j < to && word(bytes[j]) {
                j += 1;
            }
            let after_path = i > 0 && matches!(bytes[i - 1], b'.' | b':');
            if !after_path && !bytes[i].is_ascii_digit() {
                out.push((i as u32 + base, &text[i..j]));
            }
            i = j;
        } else {
            i += 1;
        }
    }
    out
}

// Proof-only helper functions are checked but need no executable representation.
fn reachable(
    input: &crate::read::ExtractionInput,
    roots: &[PathBuf],
) -> Result<HashSet<String>, String> {
    let checked = &input.checked;
    let exports: HashSet<_> = roots
        .iter()
        .map(|p| p.canonicalize().unwrap_or_else(|_| p.clone()))
        .collect();
    let mut needed = HashSet::new();
    let mut candidates = HashSet::new();
    let mut unsupported = HashSet::new();
    let mut dependencies = std::collections::HashMap::<String, HashSet<String>>::new();
    let std_names = StdNames::new(&input.sources);
    let aliases = type_aliases(checked, input.sources.iter().flat_map(|(_, s)| s));
    fn references(s: &Stmt) -> HashSet<String> {
        let mut refs = HashSet::new();
        let mut s = s.clone();
        crate::surface::walk::stmt(&mut s, &mut |t| match &*t.kind {
            TermKind::Var(n) => {
                refs.insert(n.clone());
            }
            TermKind::Field { .. } => {
                if let Some(n) = dotted(t) {
                    refs.insert(n);
                }
            }
            _ => {}
        });
        refs
    }
    fn flatten(stmts: Vec<Stmt>, out: &mut Vec<Stmt>) {
        for s in stmts {
            if let Stmt::Mutual { items, .. } = s {
                flatten(items, out);
            } else {
                out.push(s);
            }
        }
    }
    for (file, source_stmts) in &input.sources {
        let path = &file.path;
        let mut stmts = Vec::new();
        flatten(source_stmts.clone(), &mut stmts);
        let mut normalized = Vec::new();
        for s in stmts {
            if executable(&s, &checked.runtime) {
                normalized.push(s);
            } else {
                flatten(vec![record_sugar(&checked.records, &s)], &mut normalized);
            }
        }
        for s in normalized {
            if executable(&s, &checked.runtime) || matches!(s, Stmt::Instance(_)) {
                needed.extend(references(&s));
            } else if let Some((f, def)) = match s {
                Stmt::Fn(f) => Some((f, false)),
                Stmt::Def(t) => def_as_fn(&t).map(|f| (f, true)),
                _ => None,
            } {
                let mut probe = Extractor {
                    checked,
                    generated: HashSet::new(),
                    out: String::new(),
                    fresh: 0,
                    mixed: false,
                    needed: HashSet::new(),
                    runtime: Vec::new(),
                    total: HashSet::new(),
                    thunks: HashSet::new(),
                    std: &std_names,
                    written: HashSet::new(),
                    pending: Vec::new(),
                    unused: HashSet::new(),
                    aliases: aliases.clone(),
                    proof_takers: HashSet::new(),
                    refined_takers: HashSet::new(),
                };
                if probe.function(path, &f).is_err() {
                    unsupported.insert(f.name.clone());
                    continue;
                }
                // Follow the erased executable body, not its proof arguments or
                // termination certificates. Mapped primitives have no dependencies.
                let (written, renamed) = legal_names(&probe.out);
                let back: HashMap<&String, &String> =
                    renamed.iter().map(|(from, to)| (to, from)).collect();
                let mut refs = HashSet::new();
                // What extraction wrote not parsing is a fault of extraction,
                // named with the function it came from.
                let parsed = parse_program_at(&written, 0).map_err(|e| {
                    format!(
                        "{}: extracting `{}` wrote code that does not parse ({e}):\n{}",
                        path.display(),
                        f.name,
                        written.trim()
                    )
                })?;
                for stmt in parsed.stmts {
                    refs.extend(
                        references(&stmt)
                            .into_iter()
                            .map(|r| back.get(&r).map_or(r, |from| (*from).clone())),
                    );
                }
                // A `def` is written out only when executable code reaches it.
                if !def
                    && exports.contains(&crate::program::canonical_path(path))
                    && !probe.out.is_empty()
                {
                    candidates.insert(f.name.clone());
                }
                dependencies.insert(f.name, refs);
            }
        }
    }
    loop {
        let before = unsupported.len();
        for (name, refs) in &dependencies {
            if refs.iter().any(|r| unsupported.contains(r)) {
                unsupported.insert(name.clone());
            }
        }
        if before == unsupported.len() {
            break;
        }
    }
    // Export the tote's functions that have an executable representation. A
    // proof model without one is kept only if runtime code explicitly uses it;
    // normal extraction then reports the error instead of silently dropping it.
    needed.extend(candidates.difference(&unsupported).cloned());
    // The helpers of `std/SInt.taut` call its range checks.
    if checked.families.contains_key("I64") {
        needed.extend(SINT_WIDTHS.map(|(_, module)| format!("{module}::fits")));
    }
    loop {
        let before = needed.len();
        for (name, refs) in &dependencies {
            if needed.contains(name) {
                needed.extend(refs.iter().cloned());
            }
        }
        if before == needed.len() {
            return Ok(needed);
        }
    }
}

/// The functions declared in imported files that are not reached from the
/// files named on the command line. Everything in the named files is
/// extracted, and an error there is still reported.
fn unused_imported(input: &crate::read::ExtractionInput, roots: &[PathBuf]) -> HashSet<String> {
    let named: HashSet<_> = roots
        .iter()
        .map(|p| p.canonicalize().unwrap_or_else(|_| p.clone()))
        .collect();
    fn flatten(stmts: &[Stmt], out: &mut Vec<Stmt>) {
        for s in stmts {
            if let Stmt::Mutual { items, .. } = s {
                flatten(items, out);
            } else {
                out.push(s.clone());
            }
        }
    }
    fn references(s: &Stmt, refs: &mut HashSet<String>) {
        let mut s = s.clone();
        crate::surface::walk::stmt(&mut s, &mut |t| match &*t.kind {
            TermKind::Var(n) => {
                refs.insert(n.clone());
            }
            TermKind::Field { .. } => {
                if let Some(n) = dotted(t) {
                    refs.insert(n);
                }
            }
            _ => {}
        });
    }
    let mut imported = std::collections::HashMap::<String, Stmt>::new();
    let mut needed = HashSet::new();
    for (file, stmts) in &input.sources {
        let mut flat = Vec::new();
        flatten(stmts, &mut flat);
        let is_named = named.contains(&crate::program::canonical_path(&file.path));
        for s in flat {
            match &s {
                Stmt::Fn(f) if !is_named => {
                    imported.insert(f.name.clone(), s.clone());
                }
                // Proofs are erased; what they mention is not run.
                Stmt::Theorem(_) | Stmt::Def(_) | Stmt::Import { .. } => {}
                // An instance is reached through its class, not by name.
                _ => references(&s, &mut needed),
            }
        }
    }
    let mut queue: Vec<String> = needed.iter().cloned().collect();
    while let Some(name) = queue.pop() {
        if let Some(s) = imported.get(&name) {
            let mut refs = HashSet::new();
            references(s, &mut refs);
            for r in refs {
                if needed.insert(r.clone()) {
                    queue.push(r);
                }
            }
        }
    }
    imported
        .into_keys()
        .filter(|n| !needed.contains(n))
        .collect()
}

struct Extractor<'a> {
    checked: &'a Checked,
    /// The names `inductive_syntax!` declarations make for Nib.
    generated: HashSet<String>,
    out: String,
    fresh: usize,
    mixed: bool,
    needed: HashSet<String>,
    runtime: Vec<(PathBuf, String)>,
    total: HashSet<String>,
    /// The functions written with effects and no parameters: such a name
    /// without `()` is the function, passed as a value.
    thunks: HashSet<String>,
    std: &'a StdNames,
    /// The functions written out, by the names they are written with.
    written: HashSet<String>,
    /// The files whose executable source is still to be written.
    pending: Vec<(crate::program::SourceFile, Vec<Stmt>)>,
    /// Functions of imported files that nothing in the named files uses;
    /// they are not extracted, so that an import does not make the
    /// extraction depend on what it does not use.
    unused: HashSet<String>,
    /// The functions that return a type, by name: a type naming one is
    /// read as its body, as the checker reads it, since Nib has no aliases.
    aliases: HashMap<String, FnDecl>,
    /// The functions written out that take a proof among the parameters a
    /// call writes (not the laws a `where` adds).
    proof_takers: HashSet<String>,
    /// The functions and constructors written out that take a refined
    /// value ([`Extractor::refined`]) among the parameters a call writes.
    refined_takers: HashSet<String>,
}

/// The functions among `stmts` that return a type and take only types,
/// which a type written for Nib unfolds.
fn type_aliases<'s>(
    checked: &Checked,
    stmts: impl IntoIterator<Item = &'s Stmt>,
) -> HashMap<String, FnDecl> {
    fn walk(checked: &Checked, s: &Stmt, out: &mut HashMap<String, FnDecl>) {
        match s {
            Stmt::Mutual { items, .. } => items.iter().for_each(|s| walk(checked, s, out)),
            Stmt::Fn(f) if f.generics.is_empty() => {
                if checked.signatures.get(&f.name).is_some_and(|sig| {
                    sig.result == Role::Type && sig.params.iter().all(|r| *r == Role::Type)
                }) {
                    out.insert(f.name.clone(), f.clone());
                }
            }
            _ => {}
        }
    }
    let mut out = HashMap::new();
    for s in stmts {
        walk(checked, s, &mut out);
    }
    out
}

type Locals = HashSet<String>;

fn fail<X>(file: &Path, what: Message) -> Result<X, String> {
    Err(format!("{}: {what}", file.display()))
}

impl Extractor<'_> {
    fn file(
        &mut self,
        file: &crate::program::SourceFile,
        source_stmts: &[Stmt],
    ) -> Result<(), String> {
        let path = &file.path;
        let mut stmts = Vec::new();
        let mut runtime = Vec::new();
        let mut flattened = Vec::new();
        fn flatten(stmts: &[Stmt], out: &mut Vec<Stmt>) {
            for s in stmts {
                if let Stmt::Mutual { items, .. } = s {
                    flatten(items, out);
                } else {
                    out.push(s.clone());
                }
            }
        }
        flatten(source_stmts, &mut flattened);
        for s in &flattened {
            let made = match s {
                Stmt::Fn(f) => Some(&f.name),
                Stmt::Struct(d) | Stmt::Enum(d) => Some(&d.name),
                _ => None,
            };
            if made.is_some_and(|n| self.generated.contains(n)) {
                self.out
                    .push_str(&crate::surface::print::print_stmts(std::slice::from_ref(s)));
                continue;
            }
            if self.mixed && executable(s, &self.checked.runtime) {
                runtime.push(s.clone());
                continue;
            }
            match record_sugar(&self.checked.records, s) {
                Stmt::Mutual { items, .. } => stmts.extend(items),
                s => stmts.push(s),
            }
        }
        for s in &stmts {
            match s {
                Stmt::Inductive(i) => self.inductive(path, i)?,
                Stmt::Enum(d) => {
                    self.inductive(path, &tauto_kernel::check::program_family(d, false))?
                }
                Stmt::Fn(f) => self.function(path, f)?,
                Stmt::Effect(e) => self.effect(path, e)?,
                Stmt::Class(c) if self.std.of(&c.name).is_some_and(mapped_class) => {}
                Stmt::Class(c) if self.checked.classes.contains(&c.name) => self.class(path, c)?,
                Stmt::Instance(i)
                    if self.std.of(&i.class).is_some_and(mapped_class)
                        && self
                            .std
                            .of(head_name(&i.head))
                            .is_some_and(std_instance_head) => {}
                Stmt::Instance(i) if self.checked.classes.contains(&i.class) => {
                    self.instance(path, i)?
                }
                Stmt::Def(t) if self.mixed && self.needed.contains(&t.name) => {
                    if let Some(f) = def_as_fn(t) {
                        self.function(path, &f)?;
                    }
                }
                Stmt::Theorem(_) | Stmt::Def(_) | Stmt::Import { .. } => {}
                Stmt::Let { name, .. } => {
                    return fail(
                        path,
                        msg!("tauto-extract-a-constant-is-not-extracted", name = name),
                    );
                }
                _ => {
                    return fail(path, msg!("tauto-extract-only-declarations-of-the-proof"));
                }
            }
        }
        if !runtime.is_empty() {
            // Written once every file is extracted, when what each name is
            // extracted as is known.
            self.pending.push((file.clone(), source_stmts.to_vec()));
        }
        Ok(())
    }

    /// The executable source of each file that has some, kept verbatim,
    /// including its original positions and kinds: reprinting it would lose
    /// source locations and can change native syntax.
    fn runtime_files(&mut self) -> Result<(), String> {
        let mut problems = Vec::new();
        for (file, stmts) in &self.pending {
            self.proofs_given(file, stmts, &mut problems);
        }
        if !problems.is_empty() {
            return Err(problems.join("\n"));
        }
        for (file, stmts) in std::mem::take(&mut self.pending) {
            let source = runtime_source(
                &file.text,
                file.base,
                &stmts,
                &self.checked.runtime,
                &self.std,
                &self.written,
                Ctors {
                    struct_of: &|c| self.struct_fields(c).map(|(family, _)| family),
                    is_ctor: &|c| self.is_ctor(c),
                    qualified: &|c| self.qualified_ctor(c),
                },
            );
            self.runtime.push((file.path, source));
        }
        Ok(())
    }

    /// Executable code that the kernel does not check cannot give a proof:
    /// extraction erases the proof arguments of the functions it calls and
    /// the proof fields of the values it builds. So it may not call a
    /// declaration that takes a proof, a constructor with a proof field
    /// among them, nor write such a constructor's record. A value built by
    /// a function the kernel checked, and so with its proof, may be passed
    /// on and read.
    fn proofs_given(
        &self,
        file: &crate::program::SourceFile,
        stmts: &[Stmt],
        problems: &mut Vec<String>,
    ) {
        let runtime = &self.checked.runtime;
        let refined_takers = &self.refined_takers;
        // A function by the parameters a call writes; a constructor by its
        // fields, after the family's parameters.
        let takes_proof = |n: &str| {
            !runtime.contains(n)
                && (self.proof_takers.contains(n)
                    // A family mapped onto a type of Nib (`U64` onto `u64`)
                    // is not built by its constructor there; its name is
                    // Nib's own type.
                    || self.checked.families.iter().any(|(name, fam)| {
                        fam.ctors.iter().any(|c| c == n)
                            && self.mapped_type(name).is_none()
                            && self.checked.signatures.get(n).is_some_and(|sig| {
                                sig.params
                                    .get(fam.params..)
                                    .is_some_and(|fields| fields.contains(&Role::Proof))
                            })
                    }))
        };
        let mut kept: Vec<Stmt> = Vec::new();
        for s in stmts {
            match s {
                Stmt::Mutual { items, .. } => kept.extend(
                    items
                        .iter()
                        .filter(|i| matches!(i, Stmt::Fn(f) if runtime.contains(&f.name)))
                        .cloned(),
                ),
                s if executable(s, runtime) => kept.push(s.clone()),
                _ => {}
            }
        }
        for s in &mut kept {
            crate::surface::walk::stmt(s, &mut |t| {
                let (name, what) = match &*t.kind {
                    TermKind::Var(n) if takes_proof(n) => {
                        (n.clone(), "tauto-extract-unchecked-takes-proof")
                    }
                    TermKind::Var(n) if !runtime.contains(n) && refined_takers.contains(n) => {
                        (n.clone(), "tauto-extract-unchecked-takes-refined")
                    }
                    TermKind::Record { name, .. }
                        if !runtime.contains(name) && refined_takers.contains(name) =>
                    {
                        (name.clone(), "tauto-extract-unchecked-refined-field")
                    }
                    TermKind::Record { name, .. }
                        if !runtime.contains(name)
                            && self
                                .checked
                                .records
                                .get(name)
                                .is_some_and(|(ctor, _)| takes_proof(ctor)) =>
                    {
                        (name.clone(), "tauto-extract-unchecked-proof-field")
                    }
                    _ => return,
                };
                let at = (t.span.start.saturating_sub(file.base)) as usize;
                let (l, c) = crate::report::line_col(&file.text, at);
                let short = crate::surface::qualify::short(&name);
                problems.push(format!(
                    "{}:{l}:{c}: {}",
                    file.path.display(),
                    msg!(what, name = short.to_string()),
                ));
            });
        }
    }

    /// The functions of the kernel's prelude that executable code calls
    /// (`nat_lt`, `nat_sub`, …). No file declares them, so no file writes
    /// them out; each is written as the proofs' calls to it are, by its
    /// mapping, and only when the program has no declaration of its own.
    fn kernel_functions(&mut self) -> Result<(), String> {
        let prelude = crate::check::kernel_prelude()?;
        let path = Path::new("prelude");
        for s in &prelude.stmts {
            if let Stmt::Fn(f) = s
                && self.needed.contains(&f.name)
                && !nib_prelude_fn(&f.name)
                && self.std.of(&f.name).is_some_and(|n| mapped_fn(n).is_some())
            {
                self.function(path, f)?;
            }
        }
        Ok(())
    }

    fn inductive(&mut self, path: &Path, i: &InductiveDecl) -> Result<(), String> {
        let Some(fam) = self.checked.families.get(&i.name) else {
            return fail(path, msg!("tauto-extract-did-not-check", name = &i.name));
        };
        if fam.prop || fam.predicate || self.mapped_type(&i.name).is_some() {
            return Ok(());
        }
        if fam.indices > 0 {
            return fail(
                path,
                msg!("tauto-extract-has-indices-a-family-of", name = &i.name),
            );
        }
        // Executable code names the family and its constructors by what
        // they are extracted as, as it names the functions.
        self.written.insert(i.name.clone());
        self.written
            .extend(i.constructors.iter().map(|c| c.name.clone()));
        let kept = self.kept_params(&i.name);
        let generics: Vec<&str> = i
            .params
            .iter()
            .zip(&kept)
            .filter(|(_, k)| **k)
            .map(|((n, _), _)| n.as_str())
            .collect();
        let mut locals: Locals = generics.iter().map(|g| g.to_string()).collect();
        if let [c] = i.constructors.as_slice()
            && let Some((_, names)) = self.struct_fields(&c.name)
        {
            // One constructor with fields: a struct, so that Nib reads
            // `x.f` and writes `T { f: e }` as the proofs do.
            let sig = &self.checked.signatures[&c.name];
            let mut fields = Vec::new();
            for (k, (n, t)) in c.params.iter().enumerate() {
                if sig.params[fam.params + k] == Role::Value {
                    if self.refined(t) {
                        self.refined_takers.insert(c.name.clone());
                        self.refined_takers.insert(i.name.clone());
                    }
                    fields.push(format!("{}: {}", raw(n), self.ty(path, t, &locals)?));
                }
                locals.insert(n.clone());
            }
            debug_assert_eq!(fields.len(), names.len());
            let decl = format!(
                "shared struct {}{} {{ {} }}",
                i.name.rsplit("::").next().unwrap_or(&i.name),
                type_params(&generics),
                fields.join(", ")
            );
            let _ = writeln!(self.out, "\n{}", in_modules_text(&i.name, &decl));
            // Programs call the constructor by the name the proofs give it.
            // A struct is built only by its fields, so the name becomes a
            // function that builds them.
            if c.name != i.name {
                let values: Vec<String> = names
                    .iter()
                    .map(|n| format!("{}: {}", raw(n), raw(n)))
                    .collect();
                let result = if generics.is_empty() {
                    i.name.clone()
                } else {
                    format!("{}({})", i.name, generics.join(", "))
                };
                let short = crate::surface::qualify::short(&c.name);
                let ctor = short.rsplit("::").next().unwrap_or(short);
                // A record expression names its struct without a path, which
                // the modules around it find.
                let decl = format!(
                    "fn {ctor}{}({}): {result} {{\n  {} {{ {} }}\n}}",
                    angle(&generics),
                    fields.join(", "),
                    i.name.rsplit("::").next().unwrap_or(&i.name),
                    values.join(", ")
                );
                let _ = writeln!(self.out, "\n{}", in_modules_text(short, &decl));
            }
            return Ok(());
        }
        let mut decl = format!(
            "shared enum {}{} {{\n",
            i.name.rsplit("::").next().unwrap_or(&i.name),
            type_params(&generics)
        );
        for c in &i.constructors {
            let sig = &self.checked.signatures[&c.name];
            let mut fields = Vec::new();
            for (k, (n, t)) in c.params.iter().enumerate() {
                let role = sig.params[fam.params + k];
                if role == Role::Value {
                    if self.refined(t) {
                        self.refined_takers.insert(c.name.clone());
                    }
                    fields.push(self.ty(path, t, &locals)?);
                }
                locals.insert(n.clone());
            }
            // A variant is declared by its own name: one another type's
            // variant shares has its full name (`m::Bytecode::CBranch`), which
            // names this one.
            let name = c.name.rsplit("::").next().unwrap_or(&c.name);
            if fields.is_empty() {
                let _ = writeln!(decl, "  {name}");
            } else {
                let _ = writeln!(decl, "  {name}({})", fields.join(", "));
            }
        }
        decl.push('}');
        let _ = writeln!(self.out, "\n{}", in_modules_text(&i.name, &decl));
        Ok(())
    }

    /// Which parameters of the family `n` its extracted type keeps: the
    /// types. A parameter that is a predicate (`P: (A) -> Prop`) or a value
    /// (`p: (A) -> Bool`) is used only by the proofs in the fields, since a
    /// family of data has no indices and its value fields' types are data,
    /// so the extracted family does not take it.
    fn kept_params(&self, n: &str) -> Vec<bool> {
        let Some(fam) = self.checked.families.get(n) else {
            return Vec::new();
        };
        match fam
            .ctors
            .first()
            .and_then(|c| self.checked.signatures.get(c))
        {
            Some(sig) => sig.params[..fam.params]
                .iter()
                .map(|r| *r == Role::Type)
                .collect(),
            None => vec![true; fam.params],
        }
    }

    /// Whether the type `t` names a family whose extracted type leaves out a
    /// parameter (`Refined(Nat, Pos)`, `List(Refined(Nat, Pos))`): Nib reads
    /// `Refined(Nat, Pos)` and `Refined(Nat, Even)` as the same type.
    fn refined(&self, t: &SurfaceTerm) -> bool {
        let mut found = false;
        let mut t = t.clone();
        crate::surface::walk::term(&mut t, &mut |u| {
            if let TermKind::Var(n) = &*u.kind
                && self.mapped_type(n).is_none()
                && self
                    .checked
                    .families
                    .get(n)
                    .is_some_and(|f| !f.prop && !f.predicate)
                && self.kept_params(n).contains(&false)
            {
                found = true;
            }
        });
        found
    }

    /// For the one constructor of a family of data with fields: the family
    /// and the names of its value fields (it is extracted as a struct).
    fn struct_fields(&self, ctor: &str) -> Option<(String, Vec<String>)> {
        let (family, (_, names)) = self.checked.records.iter().find(|(_, (c, _))| c == ctor)?;
        let fam = self.checked.families.get(family)?;
        if fam.prop || fam.indices > 0 || self.mapped_type(family).is_some() {
            return None;
        }
        let sig = self.checked.signatures.get(ctor)?;
        let values: Vec<String> = names
            .iter()
            .zip(sig.params.get(fam.params..)?)
            .filter(|(_, r)| **r == Role::Value)
            .map(|(n, _)| n.clone())
            .collect();
        (!values.is_empty()).then(|| (family.clone(), values))
    }

    fn function(&mut self, path: &Path, f: &FnDecl) -> Result<(), String> {
        if (self.mixed && !self.needed.contains(&f.name)) || self.unused.contains(&f.name) {
            return Ok(());
        }
        let mut stripped = f.clone();
        crate::surface::walk::strip_recursion_proofs(&mut stripped);
        let f = &stripped;
        let Some(sig) = self.checked.signatures.get(&f.name).cloned() else {
            return fail(path, msg!("tauto-extract-did-not-check", name = &f.name));
        };
        let std = self.std.of(&f.name);
        if sig.result != Role::Value
            || std.is_some_and(builtin_name)
            || std.is_some_and(inline_only)
        {
            return Ok(());
        }
        let mut generics: Vec<String> = f.generics.clone();
        let mut params = Vec::new();
        let mut locals: Locals = f.generics.iter().cloned().collect();
        // The records of a `where` come after the generics in the kernel's
        // signature; the extracted function has the `where` itself.
        // A row variable is read as two parameters (`check/effects.rs`), in
        // place of its generic.
        let records = self.records_of(&f.where_);
        let row_var = f.effects.iter().flatten().any(|e| {
            e.strip_prefix('|')
                .is_some_and(|v| f.generics.iter().any(|g| g == v))
        });
        let n_generics = f.generics.len() + records + usize::from(row_var);
        for (k, (n, t)) in f.params.iter().zip(&f.param_types).enumerate() {
            let Some(t) = t else {
                return fail(
                    path,
                    msg!("tauto-extract-parameter-has-no-type", name = &f.name, n = n),
                );
            };
            let lent = match f.borrows.get(k) {
                Some(Some(true)) => "&mut ",
                Some(Some(false)) => "&",
                _ => "",
            };
            match sig.params[n_generics + k] {
                Role::Type => generics.push(n.clone()),
                Role::Proof => {
                    self.proof_takers.insert(f.name.clone());
                }
                Role::Value => {
                    if self.refined(t) {
                        self.refined_takers.insert(f.name.clone());
                    }
                    params.push(format!("{lent}{}: {}", raw(n), self.ty(path, t, &locals)?))
                }
            }
            locals.insert(n.clone());
        }
        let Some(result) = &f.result else {
            return fail(
                path,
                msg!("tauto-extract-has-no-result-type", name = &f.name),
            );
        };
        let result = self.ty(path, result, &locals)?;
        let body = match std.and_then(mapped_fn) {
            // A function a Nib program may call by its name.
            Some(template) => {
                let names: Vec<String> = f
                    .params
                    .iter()
                    .enumerate()
                    .filter(|(k, _)| sig.params[n_generics + k] == Role::Value)
                    .map(|(_, n)| n.clone())
                    .collect();
                fill(template, &names)
            }
            None => self.expr(path, &f.body, &locals, 1)?,
        };
        // A row variable is written `!e` again, as the source declares it,
        // and is not a type with a bound.
        let generics: Vec<String> = generics
            .into_iter()
            .enumerate()
            .map(|(k, g)| match f.rows.get(k) {
                Some(true) => format!("!{g}"),
                _ => g,
            })
            .collect();
        let generics: Vec<&str> = generics.iter().map(String::as_str).collect();
        let wheres = self.where_clause(path, &f.where_, &locals)?;
        let row = match f.effects.as_deref() {
            Some(row) if !row.is_empty() => format!(" ! {}", row_text(row)),
            _ => String::new(),
        };
        // `M::f` is written as `f` in `module M`, which the program opens again for each.
        let (module, short) = match f.name.rsplit_once("::") {
            Some((m, s)) => (Some(m), s),
            None => (None, f.name.as_str()),
        };
        let decl = format!(
            "fn {}{}({}): {result}{row}{wheres} {{\n  {body}\n}}",
            raw(short),
            angle(&generics),
            params.join(", ")
        );
        let _ = writeln!(self.out, "\n{}", in_modules(module, &decl));
        self.written.insert(f.name.clone());
        if row.is_empty() {
            self.total.insert(f.name.clone());
        } else if params.is_empty() {
            self.thunks.insert(f.name.clone());
        }
        Ok(())
    }

    /// `effect e(P, …): R`, its types mapped as the functions' are.
    fn effect(&mut self, path: &Path, e: &crate::surface::EffectDecl) -> Result<(), String> {
        let locals = Locals::new();
        let mut params = Vec::new();
        for (i, p) in e.params.iter().enumerate() {
            let Some(p) = p else {
                return fail(
                    path,
                    msg!("tauto-extract-a-parameter-has-no-type", name = &e.name),
                );
            };
            // Nib reads a parameter only with its name, so the written one
            // is kept and one is made up where none was written.
            let name = match e.param_names.get(i) {
                Some(n) if !n.is_empty() => n.clone(),
                _ => format!("p{i}"),
            };
            params.push(format!("{}: {}", raw(&name), self.ty(path, p, &locals)?));
        }
        let result = match &e.result {
            Some(r) => self.ty(path, r, &locals)?,
            None => "Unit".into(),
        };
        let resume = e
            .resume
            .as_ref()
            .map(|r| match r.as_str() {
                "direct" => " direct".to_string(),
                r => format!(" resume {r}"),
            })
            .unwrap_or_default();
        let _ = writeln!(
            self.out,
            "\neffect {}({}): {result}{resume}",
            raw(&e.name),
            params.join(", ")
        );
        Ok(())
    }

    /// How many constraints of a `where` are records of the proof language.
    fn records_of(&self, wheres: &[crate::surface::Constraint]) -> usize {
        if wheres
            .iter()
            .all(|c| self.checked.classes.contains(&c.class))
        {
            wheres.len()
        } else {
            0
        }
    }

    fn where_clause(
        &self,
        path: &Path,
        wheres: &[crate::surface::Constraint],
        locals: &Locals,
    ) -> Result<String, String> {
        if wheres.is_empty() {
            return Ok(String::new());
        }
        let mut parts = Vec::new();
        for c in wheres {
            parts.push(format!("{}({})", c.class, self.ty(path, &c.ty, locals)?));
        }
        Ok(format!(" where {}", parts.join(", ")))
    }

    /// `class C(A: Type) { fn m(…): R }`: the methods, without the laws.
    fn class(&mut self, path: &Path, c: &crate::surface::ClassDecl) -> Result<(), String> {
        let locals: Locals = std::iter::once(c.param.clone()).collect();
        let bound = c.bound.as_deref().unwrap_or("Type");
        let mut text = format!("\nclass {}({}: {bound}) {{\n", c.name, c.param);
        for m in &c.methods {
            let mut params = Vec::new();
            for (k, (n, t)) in m.params.iter().zip(&m.param_types).enumerate() {
                let Some(t) = t else {
                    return fail(
                        path,
                        msg!(
                            "tauto-extract-member-parameter-has-no-type",
                            class = &c.name,
                            member = &m.name,
                            n = n
                        ),
                    );
                };
                let lent = match m.borrows.get(k) {
                    Some(Some(true)) => "&mut ",
                    Some(Some(false)) => "&",
                    _ => "",
                };
                params.push(format!("{lent}{}: {}", raw(n), self.ty(path, t, &locals)?));
            }
            let result = match &m.result {
                Some(r) => self.ty(path, r, &locals)?,
                None => "Unit".into(),
            };
            let _ = writeln!(
                text,
                "  fn {}({}): {result}",
                raw(&m.name),
                params.join(", ")
            );
        }
        text.push_str("}\n");
        self.out.push_str(&text);
        Ok(())
    }

    /// `instance<G> C(H) where … { fn m(…): R { … } }`: the methods, with
    /// the types and the proofs erased like a function's.
    fn instance(&mut self, path: &Path, i: &crate::surface::InstanceDecl) -> Result<(), String> {
        let records = self.records_of(&i.where_);
        let n_generics = i.generics.len() + records;
        let locals: Locals = i.generics.iter().cloned().collect();
        let head = self.ty(path, &i.head, &locals)?;
        let wheres = self.where_clause(path, &i.where_, &locals)?;
        let generics: Vec<&str> = i.generics.iter().map(String::as_str).collect();
        let mut text = format!(
            "\ninstance{} {}({head}){wheres} {{\n",
            angle(&generics),
            i.class
        );
        let head_name = head_name(&i.head);
        for m in &i.methods {
            let kernel_name = format!("{}::{}@{head_name}", i.class, m.name);
            let Some(sig) = self.checked.signatures.get(&kernel_name).cloned() else {
                return fail(
                    path,
                    msg!("tauto-extract-did-not-check", name = kernel_name),
                );
            };
            let mut params = Vec::new();
            let mut inner = locals.clone();
            for (k, (n, t)) in m.params.iter().zip(&m.param_types).enumerate() {
                let Some(t) = t else {
                    return fail(
                        path,
                        msg!(
                            "tauto-extract-member-parameter-has-no-type",
                            class = &i.class,
                            member = &m.name,
                            n = n
                        ),
                    );
                };
                let lent = match m.borrows.get(k) {
                    Some(Some(true)) => "&mut ",
                    Some(Some(false)) => "&",
                    _ if self.std.of(&i.class).is_some_and(mapped_class) => "&",
                    _ => "",
                };
                if sig.params[n_generics + k] == Role::Value {
                    params.push(format!("{lent}{}: {}", raw(n), self.ty(path, t, &inner)?));
                }
                inner.insert(n.clone());
            }
            let Some(result) = &m.result else {
                return fail(
                    path,
                    msg!(
                        "tauto-extract-member-has-no-result-type",
                        class = &i.class,
                        member = &m.name
                    ),
                );
            };
            let result = self.ty(path, result, &inner)?;
            let body = self.expr(path, &m.body, &inner, 2)?;
            let _ = writeln!(
                text,
                "  fn {}({}): {result} {{\n    {body}\n  }}",
                raw(&m.name),
                params.join(", ")
            );
        }
        text.push_str("}\n");
        self.out.push_str(&text);
        Ok(())
    }

    // ---- types ------------------------------------------------------------

    fn ty(&self, path: &Path, t: &SurfaceTerm, locals: &Locals) -> Result<String, String> {
        self.ty_in(path, t, locals, &HashMap::new())
    }

    /// `t` as a Nib type, with the parameters of the aliases being unfolded
    /// (`env`) read as the types they were given.
    fn ty_in(
        &self,
        path: &Path,
        t: &SurfaceTerm,
        locals: &Locals,
        env: &HashMap<String, String>,
    ) -> Result<String, String> {
        if is_unit(t) {
            return Ok("Unit".into());
        }
        match &*t.kind {
            TermKind::Var(n) if env.contains_key(n) => Ok(env[n].clone()),
            TermKind::Var(n) if locals.contains(n) => Ok(n.clone()),
            TermKind::Var(n) if self.aliases.contains_key(n) => self.unfold(path, n, Vec::new()),
            TermKind::Var(n) => self.type_name(path, n).map(|s| s.to_string()),
            TermKind::App {
                function,
                arguments,
            } => {
                let TermKind::Var(n) = &*function.kind else {
                    return fail(
                        path,
                        msg!("tauto-extract-a-type-is-not-extracted", ty = show(t)),
                    );
                };
                // A quotient is its representation: a program reads a value
                // of it only through `Quot_lift`, which respects the relation.
                if self.std.of(n) == Some("Quot")
                    && let [a, _] = &arguments[..]
                {
                    return self.ty_in(path, a, locals, env);
                }
                if !env.contains_key(n) && !locals.contains(n) && self.aliases.contains_key(n) {
                    let args = arguments
                        .iter()
                        .map(|a| self.ty_in(path, a, locals, env))
                        .collect::<Result<Vec<_>, _>>()?;
                    return self.unfold(path, n, args);
                }
                // `Prod(A, B)`: the elaborated form of a product, Nib's `A × B`.
                if crate::surface::qualify::short(n) == "Prod" && arguments.len() == 2 {
                    let members = arguments
                        .iter()
                        .map(|a| self.ty_in(path, a, locals, env).map(|m| format!("({m})")))
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(members.join(" × "));
                }
                let head = self.type_name(path, n)?;
                let kept = if self.mapped_type(n).is_some() {
                    Vec::new()
                } else {
                    self.kept_params(n)
                };
                let args = arguments
                    .iter()
                    .enumerate()
                    .filter(|(k, _)| kept.get(*k).copied().unwrap_or(true))
                    .map(|(_, a)| self.ty_in(path, a, locals, env))
                    .collect::<Result<Vec<_>, _>>()?;
                if args.is_empty() {
                    return Ok(head.to_string());
                }
                Ok(format!("{head}({})", args.join(", ")))
            }
            TermKind::Pi {
                params,
                result,
                effects,
            } => {
                let mut inner = locals.clone();
                let mut env = env.clone();
                let mut doms = Vec::new();
                for (n, d) in params {
                    doms.push(self.ty_in(path, d, &inner, &env)?);
                    if let Some(n) = n {
                        env.remove(n);
                        inner.insert(n.clone());
                    }
                }
                let row = match effects.as_deref() {
                    Some(row) if !row.is_empty() => format!(" ! {}", row_text(row)),
                    _ => String::new(),
                };
                Ok(format!(
                    "({}) -> {}{row}",
                    doms.join(", "),
                    self.ty_in(path, result, &inner, &env)?
                ))
            }
            // A borrowed parameter's type, as a class method's is (`&K`).
            TermKind::Borrow { mutable, term } => Ok(format!(
                "{}{}",
                if *mutable { "&mut " } else { "&" },
                self.ty_in(path, term, locals, env)?
            )),
            // `@a T`: Nib's own label, a mark of the type.
            TermKind::Tagged { tag, term } => {
                Ok(format!("@{} {}", raw(tag), self.ty_in(path, term, locals, env)?))
            }
            // `A × B`: Nib's own product, its members as one set (`A × Unit` is `A`).
            TermKind::Product(items) => {
                let members = crate::surface::qualify::product_type_members(items)
                    .iter()
                    .map(|m| self.ty_in(path, m, locals, env).map(|m| format!("({m})")))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(match members.len() {
                    0 => "Unit".into(),
                    _ => members.join(" × "),
                })
            }
            _ => fail(
                path,
                msg!("tauto-extract-a-type-is-not-extracted", ty = show(t)),
            ),
        }
    }

    /// The alias `n` given `args`, as the type its body names.
    fn unfold(&self, path: &Path, n: &str, args: Vec<String>) -> Result<String, String> {
        let f = &self.aliases[n];
        if f.params.len() != args.len() {
            return fail(
                path,
                msg!(
                    "tauto-extract-is-given-types-for-parameters",
                    n = n,
                    count = args.len(),
                    params = f.params.len()
                ),
            );
        }
        let mut body = &f.body;
        while let TermKind::Block(stmts) = &*body.kind {
            match stmts.as_slice() {
                [Stmt::Expr(e)] => body = e,
                _ => return fail(path, msg!("tauto-extract-a-type-alias-s-body", n = n)),
            }
        }
        let env = f.params.iter().cloned().zip(args).collect();
        self.ty_in(path, body, &Locals::new(), &env)
    }

    /// The builtin of Nib a family of the standard library is mapped onto.
    fn mapped_type(&self, n: &str) -> Option<&'static str> {
        self.std.of(n).and_then(mapped_type)
    }

    fn type_name<'s>(&self, path: &Path, n: &'s str) -> Result<&'s str, String> {
        if let Some(m) = self.mapped_type(n) {
            return Ok(m);
        }
        // A field of an `inductive enum` names Nib's
        // own type (`u64`), which the kernel reads as its family (`U64`).
        let bare = crate::surface::qualify::short(n);
        if tauto_surface::inductive_data::proof_type(bare).is_some()
            && (n == bare || self.std.of(n).is_some())
        {
            return Ok(bare);
        }
        match self.checked.families.get(n) {
            Some(f) if !f.prop && !f.predicate => Ok(n),
            _ => fail(path, msg!("tauto-extract-is-not-a-type-of", n = n)),
        }
    }

    // ---- terms ------------------------------------------------------------

    fn fresh(&mut self, base: &str) -> String {
        self.fresh += 1;
        format!("{base}_x{}", self.fresh)
    }

    /// `t` as a Nib expression, `depth` levels of indentation in.
    fn expr(
        &mut self,
        path: &Path,
        t: &SurfaceTerm,
        locals: &Locals,
        depth: usize,
    ) -> Result<String, String> {
        if is_unit(t) {
            return Ok("#()".into());
        }
        match &*t.kind {
            TermKind::Nat(n) => Ok(n.clone()),
            TermKind::Bool(b) => Ok(b.to_string()),
            TermKind::Float(x) => Ok(x.clone()),
            TermKind::Text(s) => Ok(text_literal(s)),
            // A place lent to a call: `&mut x`, `&mut x.f`.
            TermKind::Borrow { mutable, term } => {
                let place = match &*term.kind {
                    TermKind::Var(x) => raw(x),
                    TermKind::Field { base, name } => match &*base.kind {
                        TermKind::Var(x) => format!("{}.{}", raw(x), raw(name)),
                        _ => {
                            return fail(
                                path,
                                msg!("tauto-extract-is-not-extracted", ty = show(t)),
                            );
                        }
                    },
                    _ => self.expr(path, term, locals, depth)?,
                };
                Ok(format!("{}{place}", if *mutable { "&mut " } else { "&" }))
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                let c = self.expr(path, condition, locals, depth)?;
                let a = self.expr(path, then, locals, depth + 1)?;
                let mut out = format!("if {c} {}", braces(&[a], depth));
                if let Some(b) = otherwise {
                    let b = self.expr(path, b, locals, depth + 1)?;
                    out.push_str(&format!(" else {}", braces(&[b], depth)));
                }
                Ok(out)
            }
            TermKind::Var(n) if locals.contains(n) || self.thunks.contains(n) => Ok(local_name(n)),
            TermKind::Var(n) => self.global(path, n, &[], locals, depth),
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                // `Cons(a, Cons(b, Nil))` is written back as `[a, b]`, which
                // the parser reads as the same terms: a long list nested as
                // calls would be deeper than any source is allowed to be.
                TermKind::Var(n) if n == "Cons" && !locals.contains(n) => {
                    match list_items(t, locals) {
                        Some(items) => {
                            let items = items
                                .into_iter()
                                .map(|a| self.expr(path, a, locals, depth))
                                .collect::<Result<Vec<_>, _>>()?;
                            Ok(format!("[{}]", items.join(", ")))
                        }
                        None => self.global(path, n, arguments, locals, depth),
                    }
                }
                TermKind::Var(n) if !locals.contains(n) => {
                    self.global(path, n, arguments, locals, depth)
                }
                // `C::m(…)`: a method of a class.
                TermKind::Field { base, name } if matches!(&*base.kind, TermKind::Var(c) if !locals.contains(c) && self.checked.classes.contains(c)) =>
                {
                    let TermKind::Var(c) = &*base.kind else {
                        unreachable!()
                    };
                    // A mapped class's methods borrow their arguments; one
                    // written already lent (`Ord::compare(&a, &b)`) is lent once.
                    let args = arguments
                        .iter()
                        .map(|a| {
                            let lent = self.std.of(c).is_some_and(mapped_class)
                                && !matches!(&*a.kind, TermKind::Borrow { .. });
                            self.expr(path, a, locals, depth)
                                .map(|a| if lent { format!("&{a}") } else { a })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(format!("{c}::{}({})", raw(name), args.join(", ")))
                }
                // `match x: (P, …) -> R { … }(h, …)`: the parameters of the
                // result that are propositions are erased in the arms and in
                // the arguments alike, as the checker typed them.
                TermKind::Match {
                    scrutinee,
                    result: Some(motive),
                    arms,
                    ..
                } if matches!(&*motive.kind, TermKind::Pi { params, .. }
                    if params.iter().any(|(_, t)| self.is_prop(t))) =>
                {
                    let TermKind::Pi { params, .. } = &*motive.kind else {
                        unreachable!()
                    };
                    let erased: Vec<bool> = params.iter().map(|(_, t)| self.is_prop(t)).collect();
                    if arguments.len() != erased.len() {
                        return fail(path, msg!("tauto-extract-a-match-whose-result-takes"));
                    }
                    let mut stripped = Vec::new();
                    for arm in arms {
                        let TermKind::Lam {
                            params: names,
                            body,
                            types,
                        } = &*arm.body.kind
                        else {
                            return fail(path, msg!("tauto-extract-arm-is-lambda"));
                        };
                        if names.len() != erased.len() {
                            return fail(path, msg!("tauto-extract-arm-binds-parameters"));
                        }
                        let keep = |k: &usize| !erased[*k];
                        let mut arm = arm.clone();
                        arm.body = if erased.iter().all(|e| *e) {
                            (**body).clone()
                        } else {
                            arm.body.with_kind(
                                TermKind::Lam {
                                    params: (0..names.len())
                                        .filter(keep)
                                        .map(|k| names[k].clone())
                                        .collect(),
                                    body: body.clone(),
                                    types: if types.is_empty() {
                                        Vec::new()
                                    } else {
                                        (0..types.len())
                                            .filter(keep)
                                            .map(|k| types[k].clone())
                                            .collect()
                                    },
                                },
                                arm.body.span,
                            )
                        };
                        stripped.push(arm);
                    }
                    let f = self.matching(path, scrutinee, &stripped, locals, depth)?;
                    let args = arguments
                        .iter()
                        .zip(&erased)
                        .filter(|(_, e)| !**e)
                        .map(|(a, _)| self.expr(path, a, locals, depth))
                        .collect::<Result<Vec<_>, _>>()?;
                    if args.is_empty() {
                        Ok(f)
                    } else {
                        Ok(format!("({f})({})", args.join(", ")))
                    }
                }
                _ => {
                    let f = self.expr(path, function, locals, depth)?;
                    let args = arguments
                        .iter()
                        .map(|a| self.expr(path, a, locals, depth))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(format!("({f})({})", args.join(", ")))
                }
            },
            TermKind::Lam {
                params, body, types,
            } => {
                // A written parameter type is kept: Nib reads a lambda's
                // parameters before the arguments that would tell them.
                let mut shown = Vec::new();
                for (k, p) in params.iter().enumerate() {
                    match types.get(k).and_then(|t| t.as_ref()) {
                        Some(t) => match self.ty_in(path, t, locals, &HashMap::new()) {
                            Ok(t) => shown.push(format!("{p}: {t}")),
                            Err(_) => shown.push(p.clone()),
                        },
                        None => shown.push(p.clone()),
                    }
                }
                let mut inner = locals.clone();
                inner.extend(params.iter().cloned());
                let body = self.expr(path, body, &inner, depth)?;
                Ok(format!("({}) => {body}", shown.join(", ")))
            }
            TermKind::Match {
                scrutinee, arms, ..
            } => self.matching(path, scrutinee, arms, locals, depth),
            TermKind::Block(stmts) => self.block(path, stmts, locals, depth),
            TermKind::Field { base, name } => self.field(path, base, name, locals, depth),
            TermKind::Perform { effect, args } => {
                let args = args
                    .iter()
                    .map(|a| self.expr(path, a, locals, depth))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("perform {}({})", raw(effect), args.join(", ")))
            }
            TermKind::Handle { body, handlers } => self.handle(path, body, handlers, locals, depth),
            // `@a e`: Nib's own label, which leaves the value as it is.
            TermKind::Tagged { tag, term } => {
                Ok(format!("@{} ({})", raw(tag), self.expr(path, term, locals, depth)?))
            }
            // `#(a, b)`: Nib's own product, its members told apart by their types; the
            // std's `Pair` is written as the record it is.
            TermKind::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|a| self.expr(path, a, locals, depth))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("#({})", items.join(", ")))
            }
            // `(e: T)`: Nib takes the members `T` names out of a product, as the proof does.
            TermKind::Ascribe { term, ty } => Ok(format!(
                "({}: {})",
                self.expr(path, term, locals, depth)?,
                self.ty(path, ty, locals)?
            )),
            _ => fail(path, msg!("tauto-extract-is-not-extracted", ty = show(t))),
        }
    }

    /// `handle { body } with { … }`: arms whose patterns are names.
    fn handle(
        &mut self,
        path: &Path,
        body: &SurfaceTerm,
        handlers: &[crate::surface::Handler],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, String> {
        use crate::surface::Handler;
        fn name(path: &Path, p: &Pattern) -> Result<String, String> {
            match p {
                Pattern::Bind(n) => Ok(n.clone()),
                Pattern::Wild => Ok("_".into()),
                _ => fail(path, msg!("tauto-extract-a-handler-arm-s-pattern")),
            }
        }
        let b = self.expr(path, body, locals, depth + 1)?;
        let pad = "  ".repeat(depth + 1);
        let mut arms = Vec::new();
        for h in handlers {
            let mut inner = locals.clone();
            match h {
                Handler::Return { pattern, body } => {
                    let x = name(path, pattern)?;
                    inner.insert(x.clone());
                    let e = self.expr(path, body, &inner, depth + 1)?;
                    arms.push(format!("{pad}return {} => {e}", raw(&x)));
                }
                Handler::Operation {
                    effect,
                    patterns,
                    cont,
                    guard,
                    body,
                    ..
                } => {
                    if guard.is_some() {
                        return fail(path, msg!("tauto-extract-a-guard-on-a-handler"));
                    }
                    let xs = patterns
                        .iter()
                        .map(|p| name(path, p))
                        .collect::<Result<Vec<_>, _>>()?;
                    inner.extend(xs.iter().cloned());
                    let k = cont.clone().unwrap_or_else(|| "_".into());
                    inner.insert(k.clone());
                    let e = self.expr(path, body, &inner, depth + 1)?;
                    let xs: Vec<String> = xs.iter().map(|x| raw(x)).collect();
                    arms.push(format!(
                        "{pad}{}({}), {} => {e}",
                        raw(effect),
                        xs.join(", "),
                        raw(&k)
                    ));
                }
            }
        }
        let end = "  ".repeat(depth);
        Ok(format!(
            "handle {} with {{\n{}\n{end}}}",
            braces(&[b], depth),
            arms.join("\n")
        ))
    }

    /// `x.f`: Nib's own field for a mapped record (`Pair`), else a match on
    /// the one constructor of the family that has the field.
    fn field(
        &mut self,
        path: &Path,
        base: &SurfaceTerm,
        name: &str,
        locals: &Locals,
        depth: usize,
    ) -> Result<String, String> {
        let owners: Vec<(String, (String, Vec<String>))> = self
            .checked
            .records
            .iter()
            .filter(|(family, (_, fs))| {
                !self.checked.props.contains(*family) && fs.iter().any(|f| f == name)
            })
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        // A struct's field Nib reads itself, by the type it infers, so
        // records that share a field name are told apart there.
        if !owners.is_empty()
            && owners.iter().all(|(family, (ctor, _))| {
                self.mapped_type(family).is_some() || self.struct_fields(ctor).is_some()
            })
        {
            let b = self.expr(path, base, locals, depth)?;
            return Ok(format!("({b}).{}", raw(name)));
        }
        let [(_, (ctor, fields))] = owners.as_slice() else {
            return fail(path, msg!("tauto-extract-is-a-field-of-no", name = name));
        };
        let var = format!("extract_{name}");
        let arm = MatchArm {
            goal: None,
            pattern: Pattern::Ctor {
                name: ctor.clone(),
                args: fields
                    .iter()
                    .map(|f| match f == name {
                        true => Pattern::Bind(var.clone()),
                        false => Pattern::Wild,
                    })
                    .collect(),
            },
            guard: None,
            body: SurfaceTerm::new(TermKind::Var(var), base.span),
        };
        self.matching(path, base, &[arm], locals, depth)
    }

    fn block(
        &mut self,
        path: &Path,
        stmts: &[Stmt],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, String> {
        // A block that ends with a statement is `()`.
        let (last, lets) = match stmts.split_last() {
            Some((Stmt::Expr(last), lets)) => (Some(last), lets),
            _ => (None, stmts),
        };
        let mut inner = locals.clone();
        let mut lines = Vec::new();
        for s in lets {
            match s {
                Stmt::Let {
                    name, ty, value, ..
                } => {
                    if !ty.as_ref().is_some_and(|ty| self.is_prop(ty)) {
                        let v = self.expr(path, value, &inner, depth + 1)?;
                        // The type written can be what fixes a generic of
                        // the value (`let x: Box(Nat) = empty()`).
                        match ty.as_ref().map(|ty| self.ty(path, ty, &inner)) {
                            Some(Ok(ty)) => lines.push(format!("let {}: {ty} := {v}", raw(name))),
                            _ => lines.push(format!("let {} := {v}", raw(name))),
                        }
                    }
                    inner.insert(name.clone());
                }
                Stmt::Var {
                    name,
                    ty,
                    value,
                    borrow: false,
                } => {
                    let v = self.expr(path, value, &inner, depth + 1)?;
                    match ty {
                        Some(ty) => {
                            let ty = self.ty(path, ty, &inner)?;
                            lines.push(format!("var {}: {ty} := {v}", raw(name)))
                        }
                        None => lines.push(format!("var {} := {v}", raw(name))),
                    }
                    inner.insert(name.clone());
                }
                Stmt::Assign { name, place, value } => {
                    let v = self.expr(path, value, &inner, depth + 1)?;
                    let target = match place {
                        Some(p) => self.expr(path, p, &inner, depth + 1)?,
                        None => raw(name),
                    };
                    lines.push(format!("{target} := {v}"));
                }
                Stmt::Expr(e) => lines.push(self.expr(path, e, &inner, depth + 1)?),
                _ => {
                    return fail(path, msg!("tauto-extract-a-block-holds-only-let"));
                }
            }
        }
        if let Some(last) = last {
            lines.push(self.expr(path, last, &inner, depth + 1)?);
        }
        Ok(braces(&lines, depth))
    }

    /// Whether `ty` is a proposition: its head (under `∀`) makes one.
    fn is_prop(&self, ty: &SurfaceTerm) -> bool {
        match &*ty.kind {
            TermKind::Pi { result, .. } => self.is_prop(result),
            TermKind::Var(n) => self.checked.props.contains(n) || n == "Prop" || n == "=",
            TermKind::App { function, .. } => self.is_prop(function),
            _ => false,
        }
    }

    /// A global applied to `args` (none when it is not applied).
    fn global(
        &mut self,
        path: &Path,
        n: &str,
        args: &[SurfaceTerm],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, String> {
        if matches!(
            n,
            "+" | "*" | "<" | "<=" | ">" | ">=" | "&&" | "||" | "==" | "!="
        ) {
            let [a, b] = args else {
                return fail(path, msg!("tauto-extract-takes-two-arguments", n = n));
            };
            let a = self.expr(path, a, locals, depth)?;
            let b = self.expr(path, b, locals, depth)?;
            return Ok(format!("({a} {n} {b})"));
        }
        if n == "-" {
            // `-a`: the negative of an integer (`-2147483648`). The program
            // language reads `-5` as an `i64`, so it is `Int::neg` of the
            // literal, which is the integer the proofs mean.
            if let [a] = args {
                let a = self.int_operand(path, a, locals, depth)?;
                return Ok(format!("Int::neg({a})"));
            }
            let [a, b] = args else {
                return fail(path, msg!("tauto-extract-minus-takes-two-arguments"));
            };
            let a = self.expr(path, a, locals, depth)?;
            let b = self.expr(path, b, locals, depth)?;
            return Ok(format!("extract_nat_sub({a}, {b})"));
        }
        if n == "the" {
            let Some(last) = args.last() else {
                return fail(path, msg!("tauto-extract-the-takes-a-type-and"));
            };
            return self.expr(path, last, locals, depth);
        }
        let Some(mut sig) = self.checked.signatures.get(n).cloned() else {
            return fail(path, msg!("tauto-extract-is-not-a-declaration-that", n = n));
        };
        // A constructor is built from its fields: the family's parameters,
        // values among them, are not passed.
        if let Some(fam) = self
            .checked
            .families
            .values()
            .find(|f| f.ctors.iter().any(|c| c == n))
        {
            for r in &mut sig.params[..fam.params] {
                if *r == Role::Value {
                    *r = Role::Proof;
                }
            }
        }
        if sig.result != Role::Value {
            return fail(path, msg!("tauto-extract-is-used-as-a-value", n = n));
        }
        // The arguments as the kernel has them: the implicit ones left out
        // are the leading ones.
        let roles: &[Role] = if args.len() == sig.params.len() {
            &sig.params
        } else if args.len() + sig.implicit == sig.params.len() {
            &sig.params[sig.implicit..]
        } else if args.is_empty() {
            &[]
        } else {
            return fail(
                path,
                msg!(
                    "tauto-extract-is-applied-to-arguments-write",
                    n = n,
                    count = args.len()
                ),
            );
        };
        // The standard library's `Int::` functions take integers, and a
        // literal among their arguments is a natural number the program
        // language does not read as an `Int`.
        let int_fn = self.std.of(n).is_some_and(|m| m.starts_with("Int::"));
        // `C::m(…)` of a mapped class: its methods borrow their arguments,
        // and one written already lent (`Ord::compare(&a, &b)`) is lent once.
        let lends = n.rsplit_once("::").is_some_and(|(c, _)| {
            self.checked.classes.contains(c) && self.std.of(c).is_some_and(mapped_class)
        });
        let mut values = Vec::new();
        for (a, r) in args.iter().zip(roles) {
            if *r == Role::Value {
                let v = if int_fn {
                    self.int_operand(path, a, locals, depth)?
                } else {
                    self.expr(path, a, locals, depth)?
                };
                values.push(if lends && !matches!(&*a.kind, TermKind::Borrow { .. }) {
                    format!("&{v}")
                } else {
                    v
                });
            }
        }
        let wanted = sig.params.iter().filter(|r| **r == Role::Value).count();
        if args.is_empty() && wanted > 0 {
            // Used as a function value.
            let xs: Vec<String> = (0..wanted).map(|_| self.fresh("a")).collect();
            let call = self.call(path, n, &xs)?;
            return Ok(format!("({}) => {call}", xs.join(", ")));
        }
        self.call(path, n, &values)
    }

    /// `t` as an `Int`: a numeral is `IntOfNat` of it.
    fn int_operand(
        &mut self,
        path: &Path,
        t: &SurfaceTerm,
        locals: &Locals,
        depth: usize,
    ) -> Result<String, String> {
        match &*t.kind {
            TermKind::Nat(n) => Ok(format!("IntOfNat({n})")),
            _ => self.expr(path, t, locals, depth),
        }
    }

    /// `n` applied to the value arguments `values`.
    fn call(&mut self, path: &Path, n: &str, values: &[String]) -> Result<String, String> {
        if let Some(c) = self.std.of(n).and_then(|m| mapped_ctor(m, values)) {
            return Ok(c);
        }
        // The standard library's constructor of `Text`, by its full name.
        if let ("std::Text::Text::Mk", [bytes]) = (n, values)
            && self.checked.families.contains_key("Text")
        {
            return Ok(format!("extract_text_of_bytes({bytes})"));
        }
        if self.checked.families.iter().any(|(name, family)| {
            matches!(
                self.std.of(name).unwrap_or(""),
                "Text"
                    | "Array"
                    | "Bytes"
                    | "Stack"
                    | "U8"
                    | "U32"
                    | "U64"
                    | "I32"
                    | "I64"
                    | "Float"
                    | "Float32"
            ) && family.ctors.iter().any(|ctor| ctor == n)
        }) {
            return fail(
                path,
                msg!(
                    "tauto-extract-has-no-executable-constructor-representation",
                    n = n
                ),
            );
        }
        if let Some((family, names)) = self.struct_fields(n) {
            let fields: Vec<String> = names
                .iter()
                .zip(values)
                .map(|(f, v)| format!("{}: {v}", raw(f)))
                .collect();
            return Ok(format!("{family} {{ {} }}", fields.join(", ")));
        }
        if let Some(m) = self.std.of(n)
            && let Some(folded) = literal_shift(m, values)
        {
            return Ok(folded);
        }
        if let Some(template) = self.std.of(n).and_then(mapped_fn) {
            return Ok(format!("({})", fill(template, values)));
        }
        if is_eliminator(n) {
            return fail(path, msg!("tauto-extract-is-an-eliminator-write-a", n = n));
        }
        let is_ctor = self
            .checked
            .families
            .values()
            .any(|f| f.ctors.iter().any(|c| c == n));
        if is_ctor && values.is_empty() {
            return Ok(self.ctor_ref(n));
        }
        if is_ctor {
            return Ok(format!("{}({})", self.ctor_ref(n), values.join(", ")));
        }
        Ok(format!("{}({})", raw(n), values.join(", ")))
    }

    /// The path of a variant that kept its short name inside a type written
    /// out in modules: when the type was renamed to its full name (a
    /// program's `Pending` against the prelude's) it is declared inside the
    /// modules of that name, which the bare variant does not find.
    fn qualified_ctor(&self, n: &str) -> Option<String> {
        if n.contains(['.', ':']) || !self.written.contains(n) {
            return None;
        }
        let (family, _) = self
            .checked
            .families
            .iter()
            .find(|(_, f)| f.ctors.iter().any(|c| c == n))?;
        family
            .contains("::")
            .then(|| format!("{family}::{}", raw(n)))
    }

    /// A variant as the extracted code names it: under the name its type is
    /// declared by (`Expr.ExVar`). A variant renamed to its full name
    /// because another declaration shares its short name
    /// (`fluent.src.syntax.Expr.ExVar`) is declared by its own name inside
    /// the type, and the modules of the full name are not written out.
    fn ctor_ref(&self, n: &str) -> String {
        let family = self
            .checked
            .families
            .iter()
            .find(|(_, f)| f.ctors.iter().any(|c| c == n))
            .map(|(family, _)| family.as_str());
        let Some(short) = n.rsplit(['.', ':']).next().filter(|s| s.len() < n.len()) else {
            return self.qualified_ctor(n).unwrap_or_else(|| raw(n));
        };
        match family {
            Some(family) => format!(
                "{}::{}",
                family.rsplit("::").next().unwrap_or(family),
                raw(short)
            ),
            None => raw(n),
        }
    }

    // ---- match --------------------------------------------------------------

    fn matching(
        &mut self,
        path: &Path,
        scrutinee: &SurfaceTerm,
        arms: &[MatchArm],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, String> {
        // `@a p`: the labels come off the value's type in Nib as in the kernel. The
        // value is bound under them once (`match s { @a v => … }`) and the patterns
        // under them are matched against `v`, at the type the kernel gave `p`.
        if let Some(head) = arms.iter().find(|a| a.pattern.label().is_some()) {
            let mut tags = Vec::new();
            let mut p = &head.pattern;
            while let Some((tag, inner)) = p.label() {
                tags.push(format!("@{} ", raw(tag)));
                p = inner;
            }
            let unlabelled: Vec<MatchArm> = arms
                .iter()
                .map(|a| MatchArm {
                    pattern: unlabel(&a.pattern),
                    ..a.clone()
                })
                .collect();
            let s = self.expr(path, scrutinee, locals, depth + 1)?;
            let v = self.fresh("unlabelled");
            let mut inner = locals.clone();
            inner.insert(v.clone());
            let under = SurfaceTerm::var(&v, scrutinee.span);
            let body = self.matching(path, &under, &unlabelled, &inner, depth + 1)?;
            let pad = "  ".repeat(depth + 1);
            let end = "  ".repeat(depth);
            return Ok(format!(
                "match {s} {{\n{pad}{}{} => {body}\n{end}}}",
                tags.concat(),
                raw(&v)
            ));
        }
        // Guards are the `match`es on `Bool` the kernel read them as.
        if arms.iter().any(|a| a.guard.is_some()) {
            let chain = crate::check::guard_chain(scrutinee, None, None, arms, scrutinee.span);
            return self.expr(path, &chain, locals, depth);
        }
        // `false` and `true` are the constructors of `Bool`, as the kernel
        // reads them.
        let read: Vec<MatchArm>;
        let arms = if arms.iter().any(|a| has_bool(&a.pattern)) {
            read = arms
                .iter()
                .map(|a| MatchArm {
                    pattern: bool_constructors(&a.pattern),
                    ..a.clone()
                })
                .collect();
            &read[..]
        } else {
            arms
        };
        let family = arms
            .iter()
            .find_map(|a| self.pattern_family(&a.pattern))
            .unwrap_or_default();
        if self.checked.families.get(&family).is_some_and(|f| f.prop) || arms.is_empty() {
            // A proof is matched only to fix types: its one arm is the value.
            return match arms {
                [] => Ok("extract_unreachable()".into()),
                [arm] => {
                    let mut inner = locals.clone();
                    pattern_names(&arm.pattern, &mut inner);
                    self.expr(path, &arm.body, &inner, depth)
                }
                _ => fail(path, msg!("tauto-extract-a-match-on-a-proof")),
            };
        }
        // `Text::Mk(bs)` binds the bytes of the text.
        if family == "Text"
            && let [arm] = arms
            && arm.guard.is_none()
            && let Pattern::Ctor { args, .. } = &arm.pattern
            && let [inner_pat] = args.as_slice()
        {
            let s = self.expr(path, scrutinee, locals, depth + 1)?;
            let mut inner = locals.clone();
            let bytes = match inner_pat {
                Pattern::Bind(n) if !self.is_ctor(n) => n.clone(),
                Pattern::Wild => self.fresh("bytes"),
                _ => return fail(path, msg!("tauto-extract-a-match-on-text-binds")),
            };
            inner.insert(bytes.clone());
            let body = self.expr(path, &arm.body, &inner, depth + 1)?;
            return Ok(braces(
                &[
                    format!("let {} := extract_text_bytes({s})", raw(&bytes)),
                    body,
                ],
                depth,
            ));
        }
        if self.std.of(&family) == Some("Secret") {
            return fail(path, msg!("tauto-extract-match-on-secret"));
        }
        if matches!(
            self.std.of(&family).unwrap_or(""),
            "Text"
                | "Array"
                | "Bytes"
                | "Stack"
                | "U8"
                | "U32"
                | "U64"
                | "I32"
                | "I64"
                | "Float"
                | "Float32"
        ) {
            return fail(
                path,
                msg!("tauto-extract-a-match-on-has-no", family = family),
            );
        }
        let s = self.expr(path, scrutinee, locals, depth + 1)?;
        if matches!(self.std.of(&family), Some("Nat" | "Bool")) {
            return self.chain(path, &s, arms, locals, depth);
        }
        if let Some(out) = self.shaped(path, &s, arms, locals, depth)? {
            return Ok(out);
        }
        let mut lines = Vec::new();
        for arm in arms {
            if arm.guard.is_some() {
                return fail(path, msg!("tauto-extract-a-guard-is-not-extracted"));
            }
            let mut inner = locals.clone();
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            let pat = self.nib_pattern(path, &arm.pattern, &mut inner, &mut tests, &mut binds)?;
            let body = self.expr(path, &arm.body, &inner, depth + 2)?;
            let guard = if tests.is_empty() {
                String::new()
            } else {
                format!(" if {}", tests.join(" && "))
            };
            let body = if binds.is_empty() {
                body
            } else {
                binds.push(body);
                braces(&binds, depth + 1)
            };
            lines.push(format!("{pat}{guard} => {body}"));
        }
        let pad = "  ".repeat(depth + 1);
        let end = "  ".repeat(depth);
        Ok(format!(
            "match {s} {{\n{}\n{end}}}",
            lines
                .iter()
                .map(|l| format!("{pad}{l}"))
                .collect::<Vec<_>>()
                .join("\n")
        ))
    }

    /// The family of the constructor a pattern names, if it names one.
    fn pattern_family(&self, p: &Pattern) -> Option<String> {
        let name = match p {
            Pattern::Ctor { name, .. } => name,
            Pattern::Bind(name) => name,
            _ => return None,
        };
        self.checked
            .families
            .iter()
            .find(|(_, f)| f.ctors.iter().any(|c| c == name))
            .map(|(n, _)| n.clone())
    }

    fn is_ctor(&self, name: &str) -> bool {
        self.checked
            .families
            .values()
            .any(|f| f.ctors.iter().any(|c| c == name))
    }

    /// A match on `Nat` or `Bool`: each arm's pattern as a test and bindings
    /// on `s`, tried in order.
    fn chain(
        &mut self,
        path: &Path,
        s: &str,
        arms: &[MatchArm],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, String> {
        let (subject, bind) = if is_name(s) {
            (s.to_string(), None)
        } else {
            let v = self.fresh("m");
            (v.clone(), Some(format!("let {v} := {s}")))
        };
        let rows: Vec<(Vec<Pattern>, &SurfaceTerm)> = arms
            .iter()
            .map(|a| (vec![a.pattern.clone()], &a.body))
            .collect();
        let out = self.chain_rows(path, &[subject], &rows, locals, depth)?;
        Ok(match bind {
            Some(b) => braces(&[b, out], depth),
            None => out,
        })
    }

    /// Rows of patterns, one per name of `subjects`, as a chain of tests
    /// tried in order. The last row is not tested: the kernel has checked
    /// that the rows take every value that reaches them.
    fn chain_rows(
        &mut self,
        path: &Path,
        subjects: &[String],
        rows: &[(Vec<Pattern>, &SurfaceTerm)],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, String> {
        let mut out = String::new();
        let n = rows.len();
        for (k, (pats, body)) in rows.iter().enumerate() {
            let mut inner = locals.clone();
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            for (p, at) in pats.iter().zip(subjects) {
                self.test(path, p, at, &mut inner, &mut tests, &mut binds)?;
            }
            binds.push(self.expr(path, body, &inner, depth + 2)?);
            let body = braces(&binds, depth + 1);
            if k + 1 == n {
                if k == 0 {
                    out.push_str(&body);
                } else {
                    let _ = write!(out, " else {body}");
                }
            } else {
                let test = if tests.is_empty() {
                    "true".to_string()
                } else {
                    tests.join(" && ")
                };
                if k == 0 {
                    let _ = write!(out, "if {test} {body}");
                } else {
                    let _ = write!(out, " else if {test} {body}");
                }
            }
        }
        Ok(out)
    }

    /// A match whose patterns have a part on `Nat` or `Bool` under a
    /// constructor (`#(b, Succ(k))`), as the case tree the kernel read it as:
    /// the arms of one shape (the pattern with each such part, each name and
    /// each `_` taken out) are one Nib arm, which binds every part taken out
    /// and tests the parts on `Nat` and `Bool` in its body, by `chain_rows`.
    /// Nib then sees no guard, and checks that the shapes cover every value.
    /// `None` when no arm has such a part.
    fn shaped(
        &mut self,
        path: &Path,
        s: &str,
        arms: &[MatchArm],
        locals: &Locals,
        depth: usize,
    ) -> Result<Option<String>, String> {
        let mut shapes = Vec::new();
        for arm in arms {
            let mut holes = Vec::new();
            let shape = self.shape(&arm.pattern, &mut holes);
            shapes.push((shape, holes));
        }
        let tested = |p: &Pattern| {
            !matches!(p, Pattern::Wild | Pattern::Bind(_))
                || matches!(p, Pattern::Bind(n) if self.is_ctor(n))
        };
        if !shapes.iter().any(|(_, holes)| holes.iter().any(tested)) {
            return Ok(None);
        }
        // The default arm (`_ =>`, or a name) is last, and takes what the
        // arms of each shape leave.
        let default = arms.last().filter(|a| {
            matches!(&a.pattern, Pattern::Wild)
                || matches!(&a.pattern, Pattern::Bind(n) if !self.is_ctor(n))
        });
        let written = arms.len() - usize::from(default.is_some());
        let mut groups: Vec<(Pattern, Vec<usize>)> = Vec::new();
        for (i, (shape, _)) in shapes[..written].iter().enumerate() {
            match groups.iter_mut().find(|(g, _)| g == shape) {
                Some((_, members)) => members.push(i),
                None => groups.push((shape.clone(), vec![i])),
            }
        }
        // Two shapes that some value has would order their arms, which the
        // kernel's case tree does not: each arm's tests would then have to
        // fall through to another Nib arm.
        for (a, (x, _)) in groups.iter().enumerate() {
            if groups[a + 1..].iter().any(|(y, _)| overlap(x, y)) {
                return fail(path, msg!("tauto-extract-nested-arms-overlap"));
            }
        }
        let (subject, bind) = if is_name(s) || default.is_none() {
            (s.to_string(), None)
        } else {
            let v = self.fresh("m");
            (v.clone(), Some(format!("let {v} := {s}")))
        };
        let mut lines = Vec::new();
        for (shape, members) in &groups {
            let count = shapes[members[0]].1.len();
            let names: Vec<String> = (0..count).map(|_| self.fresh("p")).collect();
            let mut next = names.iter();
            let filled = fill_holes(shape, &mut next);
            let mut inner = locals.clone();
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            let pat = self.nib_pattern(path, &filled, &mut inner, &mut tests, &mut binds)?;
            let mut rows: Vec<(Vec<Pattern>, &SurfaceTerm)> = members
                .iter()
                .map(|&i| (shapes[i].1.clone(), &arms[i].body))
                .collect();
            if let Some(d) = default {
                let mut row = vec![Pattern::Wild; count];
                let mut pats = vec![d.pattern.clone()];
                pats.append(&mut row);
                rows.push((pats, &d.body));
            }
            let subjects: Vec<String> = if default.is_some() {
                std::iter::once(subject.clone())
                    .chain(names.iter().cloned())
                    .collect()
            } else {
                names.clone()
            };
            let rows: Vec<(Vec<Pattern>, &SurfaceTerm)> = if default.is_some() {
                rows.into_iter()
                    .enumerate()
                    .map(|(k, (pats, body))| {
                        if k < members.len() {
                            (std::iter::once(Pattern::Wild).chain(pats).collect(), body)
                        } else {
                            (pats, body)
                        }
                    })
                    .collect()
            } else {
                rows
            };
            let body = self.chain_rows(path, &subjects, &rows, &inner, depth + 2)?;
            lines.push(format!("{pat} => {body}"));
        }
        if let Some(d) = default {
            // A name, not `_`: the shapes may already take every value, and
            // an arm no value reaches is left out when the program is lowered.
            let rest = self.fresh("rest");
            let mut inner = locals.clone();
            let mut binds = Vec::new();
            self.test(
                path,
                &d.pattern,
                &subject,
                &mut inner,
                &mut Vec::new(),
                &mut binds,
            )?;
            binds.push(self.expr(path, &d.body, &inner, depth + 2)?);
            lines.push(format!("{rest} => {}", braces(&binds, depth + 1)));
        }
        let pad = "  ".repeat(depth + 1);
        let end = "  ".repeat(depth);
        let out = format!(
            "match {subject} {{\n{}\n{end}}}",
            lines
                .iter()
                .map(|l| format!("{pad}{l}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        Ok(Some(match bind {
            Some(b) => braces(&[b, out], depth),
            None => out,
        }))
    }

    /// `p` with each part that `shaped` takes out (a part on `Nat` or
    /// `Bool`, a name, `_`) put in `holes` and written as [`HOLE`].
    fn shape(&self, p: &Pattern, holes: &mut Vec<Pattern>) -> Pattern {
        let p = unlabel(p);
        let hole = |holes: &mut Vec<Pattern>| {
            holes.push(p.clone());
            Pattern::Bind(HOLE.into())
        };
        match &p {
            Pattern::Wild | Pattern::Int(_) => hole(holes),
            Pattern::Bind(n) if !self.is_ctor(n) => hole(holes),
            Pattern::Bind(_) | Pattern::Ctor { .. }
                if matches!(
                    self.std.of(&self.pattern_family(&p).unwrap_or_default()),
                    Some("Nat" | "Bool")
                ) =>
            {
                hole(holes)
            }
            Pattern::Bind(n) => Pattern::Ctor {
                name: n.clone(),
                args: vec![],
            },
            Pattern::Ctor { name, args } => Pattern::Ctor {
                name: name.clone(),
                args: args.iter().map(|q| self.shape(q, holes)).collect(),
            },
            Pattern::Tuple(items) => {
                Pattern::Tuple(items.iter().map(|q| self.shape(q, holes)).collect())
            }
            other => other.clone(),
        }
    }

    /// What `p` asks of the value `at`: tests, and the names it binds.
    fn test(
        &mut self,
        path: &Path,
        p: &Pattern,
        at: &str,
        locals: &mut Locals,
        tests: &mut Vec<String>,
        binds: &mut Vec<String>,
    ) -> Result<(), String> {
        match p {
            Pattern::Wild => Ok(()),
            Pattern::Bind(n) if !self.is_ctor(n) => {
                binds.push(format!("let {} := {at}", raw(n)));
                locals.insert(n.clone());
                Ok(())
            }
            Pattern::Bind(n) => self.test(
                path,
                &Pattern::Ctor {
                    name: n.clone(),
                    args: vec![],
                },
                at,
                locals,
                tests,
                binds,
            ),
            Pattern::Ctor { name, args } => {
                match (self.std.of(name).unwrap_or(""), args.as_slice()) {
                    ("Zero", []) => {
                        tests.push(format!("{at} == 0"));
                        Ok(())
                    }
                    ("Succ", [q]) => {
                        tests.push(format!("{at} >= 1"));
                        let inner = format!("({at} - 1)");
                        self.test(path, q, &inner, locals, tests, binds)
                    }
                    ("true", []) => {
                        tests.push(at.to_string());
                        Ok(())
                    }
                    ("false", []) => {
                        tests.push(format!("not({at})"));
                        Ok(())
                    }
                    _ => fail(path, msg!("tauto-extract-in-a-match-on-at", name = name)),
                }
            }
            Pattern::Int(k) => {
                tests.push(format!("{at} == {k}"));
                Ok(())
            }
            _ => fail(path, msg!("tauto-extract-a-pattern-that-is-not")),
        }
    }

    /// `p` as a Nib pattern; a part on `Nat` or `Bool` becomes a fresh name
    /// with tests in the guard and bindings in the body.
    fn nib_pattern(
        &mut self,
        path: &Path,
        p: &Pattern,
        locals: &mut Locals,
        tests: &mut Vec<String>,
        binds: &mut Vec<String>,
    ) -> Result<String, String> {
        match p {
            Pattern::Wild => Ok("_".into()),
            Pattern::Bind(n) if !self.is_ctor(n) => {
                locals.insert(n.clone());
                Ok(raw(n))
            }
            Pattern::Bind(n) => self.nib_pattern(
                path,
                &Pattern::Ctor {
                    name: n.clone(),
                    args: vec![],
                },
                locals,
                tests,
                binds,
            ),
            // `@a p`: kept, so Nib takes the label off the value's type as the kernel
            // did; `p` alone would bind the member at `@a T`, and `cur + n` on it
            // would no longer be the sum of two `Nat`s.
            Pattern::Ctor { .. } if let Some((tag, inner)) = p.label() => {
                let inner = self.nib_pattern(path, inner, locals, tests, binds)?;
                Ok(format!("@{} {inner}", raw(tag)))
            }
            Pattern::Ctor { name, args } => {
                let fam = self.pattern_family(p).unwrap_or_default();
                if matches!(self.std.of(&fam), Some("Nat" | "Bool")) {
                    let v = self.fresh("p");
                    locals.insert(v.clone());
                    let mut inner_binds = Vec::new();
                    self.test(path, p, &v, locals, tests, &mut inner_binds)?;
                    binds.extend(inner_binds);
                    return Ok(v);
                }
                let sig = self.checked.signatures[name].clone();
                let fields: &[Role] = if args.len() + sig.implicit == sig.params.len() {
                    &sig.params[sig.implicit..]
                } else {
                    let fam_params = self.checked.families[&fam].params;
                    &sig.params[fam_params..]
                };
                if fields.len() != args.len() {
                    return fail(
                        path,
                        msg!("tauto-extract-in-a-pattern-has-the", name = name),
                    );
                }
                let mut parts = Vec::new();
                for (q, r) in args.iter().zip(fields) {
                    let part = self.nib_pattern(path, q, locals, tests, binds)?;
                    if *r == Role::Value {
                        parts.push(part);
                    }
                }
                Ok(match (self.std.of(name).unwrap_or(""), parts.as_slice()) {
                    ("Pair::Mk", [a, b]) => format!("Pair {{ fst: {a}, snd: {b} }}"),
                    ("Star", []) => "#()".into(),
                    _ if self.struct_fields(name).is_some() => {
                        let (family, names) = self.struct_fields(name).unwrap();
                        let fields: Vec<String> = names
                            .iter()
                            .zip(&parts)
                            .map(|(f, p)| format!("{}: {p}", raw(f)))
                            .collect();
                        format!("{family} {{ {} }}", fields.join(", "))
                    }
                    (_, []) => self.ctor_ref(name),
                    _ => format!("{}({})", self.ctor_ref(name), parts.join(", ")),
                })
            }
            Pattern::Int(_) => {
                let v = self.fresh("p");
                locals.insert(v.clone());
                self.test(path, p, &v, locals, tests, binds)?;
                Ok(v)
            }
            // `#(p, q)`: Nib's own product; the std's `Pair` is written as the record it is.
            Pattern::Tuple(items) => {
                let mut parts = Vec::new();
                for q in items {
                    parts.push(self.nib_pattern(path, q, locals, tests, binds)?);
                }
                Ok(format!("#({})", parts.join(", ")))
            }
            _ => fail(path, msg!("tauto-extract-a-pattern-that-is-not")),
        }
    }
}

/// `()`, which the parser reads as the empty tuple.
/// The items of `Cons(a, Cons(b, Nil))`, the terms `[a, b]` reads as; none
/// when the chain ends in anything but `Nil`.
fn list_items<'t>(mut t: &'t SurfaceTerm, locals: &Locals) -> Option<Vec<&'t SurfaceTerm>> {
    let mut items = Vec::new();
    loop {
        match &*t.kind {
            TermKind::Var(n) if n == "Nil" && !locals.contains(n) => return Some(items),
            TermKind::App {
                function,
                arguments,
            } if arguments.len() == 2
                && matches!(&*function.kind, TermKind::Var(n) if n == "Cons" && !locals.contains(n)) =>
            {
                items.push(&arguments[0]);
                t = &arguments[1];
            }
            _ => return None,
        }
    }
}

fn has_bool(p: &Pattern) -> bool {
    match p {
        Pattern::Bool(_) => true,
        Pattern::Ctor { args, .. } => args.iter().any(has_bool),
        Pattern::Record { fields, .. } => fields.iter().any(|(_, p)| has_bool(p)),
        Pattern::Tuple(items) => items.iter().any(has_bool),
        _ => false,
    }
}

/// `p` with `false` and `true` written as the constructors of `Bool`.
fn bool_constructors(p: &Pattern) -> Pattern {
    match p {
        Pattern::Bool(b) => Pattern::Bind(b.to_string()),
        Pattern::Ctor { name, args } => Pattern::Ctor {
            name: name.clone(),
            args: args.iter().map(bool_constructors).collect(),
        },
        Pattern::Record { name, fields } => Pattern::Record {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(f, p)| (f.clone(), bool_constructors(p)))
                .collect(),
        },
        Pattern::Tuple(items) => Pattern::Tuple(items.iter().map(bool_constructors).collect()),
        other => other.clone(),
    }
}

fn is_unit(t: &SurfaceTerm) -> bool {
    matches!(&*t.kind, TermKind::App { function, arguments }
        if arguments.is_empty() && matches!(&*function.kind, TermKind::Var(f) if f == "Tuple"))
}

/// A constructor of `std/` that is mapped onto Nib, applied.
fn mapped_ctor(n: &str, values: &[String]) -> Option<String> {
    Some(match (n, values) {
        ("Zero", []) => "0".into(),
        ("Succ", [x]) => format!("({x} + 1)"),
        ("true", []) => "true".into(),
        ("false", []) => "false".into(),
        ("Star", []) => "#()".into(),
        ("U8::Mk", [v]) => format!("U8::of_u64(U64::of_nat({v}))"),
        ("U32::Mk", [v]) => format!("U32::of_u64(U64::of_nat({v}))"),
        ("U64::Mk", [v]) => format!("U64::of_nat({v})"),
        ("Bytes::Mk", [l]) => format!("Bytes::of_list({l})"),
        ("Float::Mk", [b]) => format!("Float::of_bits({b})"),
        ("Float32::Mk", [b]) => format!("Float32::of_bits({b})"),
        ("Secret::Mk", [v]) => format!("secret({v})"),
        ("Pair::Mk", [a, b]) => format!("Pair {{ fst: {a}, snd: {b} }}"),
        _ => return None,
    })
}

fn is_eliminator(n: &str) -> bool {
    ["::rec", "::ind", "::nc", "::noconf", "::nc_diag"]
        .iter()
        .any(|s| n.ends_with(s))
}

/// A shift or rotation of `U32` or `U64` by a literal amount: the amount
/// is reduced modulo the width here, once, instead of through `nat` at
/// every call (`u32_rotr(x, 7)` in hash rounds). The result is the one the
/// table's template computes.
fn literal_shift(name: &str, values: &[String]) -> Option<String> {
    let bits: u128 = match name {
        "U32::shl" | "U32::shr" | "U32::rotl" | "U32::rotr" => 32,
        "U64::shl" | "U64::shr" | "U64::rotl" | "U64::rotr" => 64,
        _ => return None,
    };
    let [a, s] = values else { return None };
    let s = s.trim();
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    // Only the low digits matter: 10^k is 0 modulo 32 and 64 for k >= 6.
    let low = &s[s.len().saturating_sub(6)..];
    let s = low.parse::<u128>().ok()? % bits;
    Some(format!("({name}(({a}), {s}))"))
}

fn fill(template: &str, values: &[String]) -> String {
    let mut out = template.to_string();
    for (k, v) in values.iter().enumerate().rev() {
        out = out.replace(&format!("${k}"), &format!("({v})"));
    }
    out
}

/// `<A: Shared, B: Shared>`: the generics of a function, which a call infers.
/// One written `!e` is a row variable and keeps no bound.
fn angle(generics: &[&str]) -> String {
    if generics.is_empty() {
        return String::new();
    }
    let gs: Vec<String> = generics
        .iter()
        .map(|g| {
            if g.starts_with('!') {
                g.to_string()
            } else {
                format!("{g}: Shared")
            }
        })
        .collect();
    format!("<{}>", gs.join(", "))
}

/// `(A: Type, B: Type)`: the parameters of a type declaration.
fn type_params(generics: &[&str]) -> String {
    if generics.is_empty() {
        return String::new();
    }
    let gs: Vec<String> = generics.iter().map(|g| format!("{g}: Type")).collect();
    format!("({})", gs.join(", "))
}

fn braces(lines: &[String], depth: usize) -> String {
    let pad = "  ".repeat(depth + 1);
    let end = "  ".repeat(depth);
    format!(
        "{{\n{}\n{end}}}",
        lines
            .iter()
            .map(|l| format!("{pad}{l}"))
            .collect::<Vec<_>>()
            .join("\n")
    )
}

fn is_name(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| c.is_alphanumeric() || c == '_')
}

fn pattern_names(p: &Pattern, out: &mut Locals) {
    match p {
        Pattern::Bind(n) => {
            out.insert(n.clone());
        }
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| pattern_names(a, out)),
        _ => {}
    }
}

fn text_literal(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{{{:x}}}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn show(t: &SurfaceTerm) -> String {
    crate::check::describe(t)
}

/// The statements an `inductive_syntax!` declaration makes: the types and `<syntax>.parse` of Nib,
/// one `mutual` block of `inductive` types and `<syntax>.<Type>.to_i`.
fn inductive_syntax_stmts(
    name: &str,
    grammar: &crate::surface::SyntaxLit,
    generates: &crate::surface::Generates,
    span: tauto_parol::Span,
) -> Result<Vec<Stmt>, String> {
    let mut cx = crate::syntax::Syntaxes::default();
    let stmts = cx.declare_all(vec![Stmt::Syntax {
        name: name.to_string(),
        grammar: grammar.clone(),
        inductive: true,
        generates: generates.clone(),
        uses: Vec::new(),
        span,
    }]);
    match cx.errors.first() {
        Some((m, _)) => Err(m.clone()),
        None => Ok(stmts),
    }
}

/// The names of what `inductive_syntax!` declarations make for Nib, in the checked files.
fn generated_nib_names(input: &crate::read::ExtractionInput) -> HashSet<String> {
    let mut names = HashSet::new();
    for (file, _) in &input.sources {
        let text = &file.text;
        if !text.contains("inductive_syntax!") {
            continue;
        }
        let Ok(program) = crate::surface::parse_program_unresolved_at(&text, 0) else {
            continue;
        };
        for s in program.stmts {
            if let Stmt::Syntax {
                inductive: true,
                name,
                grammar,
                generates,
                span,
                ..
            } = s
                && let Ok(stmts) = inductive_syntax_stmts(&name, &grammar, &generates, span)
            {
                for g in stmts {
                    match g {
                        Stmt::Fn(f) => {
                            names.insert(f.name);
                        }
                        Stmt::Struct(d) | Stmt::Enum(d) => {
                            names.insert(d.name);
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    names
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The helpers are Tauto source written into every extracted program, so
    /// each one has to be read like a program written by hand. A static name
    /// is written with `::` (`.` takes a field only), and no helper takes a
    /// field of a value named with a capital, so `I64.of_u64` for
    /// `I64::of_u64` is caught here, not in the program of whoever extracts.
    #[test]
    fn every_helper_is_read_as_tauto() {
        for (name, text) in [
            ("HELPERS", HELPERS.to_string()),
            ("TEXT_HELPERS", TEXT_HELPERS.to_string()),
            ("sint_helpers", sint_helpers()),
            ("uint_helpers", uint_helpers()),
        ] {
            if let Err(e) = crate::read::parse_program(&text) {
                panic!("{name} is not read as Tauto: {e}");
            }
            let b = text.as_bytes();
            for (i, _) in text.match_indices('.') {
                let mut s = i;
                while s > 0 && (b[s - 1].is_ascii_alphanumeric() || b[s - 1] == b'_') {
                    s -= 1;
                }
                let after = b.get(i + 1).copied().unwrap_or(b' ');
                assert!(
                    !(s < i
                        && b[s].is_ascii_uppercase()
                        && (after.is_ascii_lowercase() || after == b'_')),
                    "{name} writes the static name `{}` with `.`, not `::`",
                    &text[s..text[i..]
                        .find(|c: char| c == '(' || c.is_whitespace())
                        .map_or(text.len(), |n| i + n)]
                );
            }
        }
    }

    #[test]
    fn hygienic_names_become_fresh_names_outside_text() {
        let (out, renamed) =
            legal_names("fn f(t_1: Nat) { let t#1 := \"t#1\" // t#2\n  g#r2(t#1, t_1) }");
        assert_eq!(
            out,
            "fn f(t_1: Nat) { let t_2 := \"t#1\" // t#2\n  g_1(t_2, t_1) }"
        );
        assert_eq!(renamed.len(), 2);
    }

    #[test]
    fn extraction_uses_the_checked_source_and_include_snapshot() {
        let root =
            std::env::temp_dir().join(format!("tauto-extraction-snapshot-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let source = root.join("source.tauto");
        let included = root.join("message.txt");
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../std/Base.taut")
            .canonicalize()
            .unwrap();
        std::fs::write(&included, "checked text").unwrap();
        std::fs::write(
            &source,
            format!(
                "import \"{}\"\n{}",
                base.display(),
                r#"fn twice(n: Nat): Nat {
  match n: Nat {
    Zero => Zero
    Succ(k) => Succ(Succ(twice(k)))
  }
}
fn message(): Text { include_text!("message.txt") }
perform show("value", twice(2))
"#
            ),
        )
        .unwrap();
        let roots = vec![source.clone()];
        let input = crate::read::check_files_for_extraction(&roots, false, true).unwrap();
        std::fs::write(
            &source,
            r#"fn twice(n: Nat): Nat { twice(n) }"#,
        )
        .unwrap();
        std::fs::remove_file(&included).unwrap();
        let (text, runtime, total) = extract_checked(&input, true, &roots).unwrap();
        assert!(total.contains("twice"));
        assert!(text.contains("+ 1"), "{text}");
        assert!(
            runtime
                .iter()
                .any(|(_, text)| text.contains("checked text"))
        );
        assert!(
            runtime
                .iter()
                .all(|(_, text)| !text.contains("include_text!"))
        );
        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn a_function_with_effects_the_kernel_rejects_does_not_run() {
        let src = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/fixed-width/src");
        let roots = vec![src.join("counter.taut"), src.join("main.taut")];
        let mut input = crate::read::check_files_for_extraction(&roots, true, true).unwrap();
        let name = "U8::add_or_overflow";
        let entry = input
            .checked
            .entries
            .iter_mut()
            .find(|e| e.entry.name == name)
            .unwrap();
        entry.entry.verdict =
            Verdict::Failed(tauto_surface::diagnostic::Diagnostic::new("rejected", None));
        input.checked.runtime.insert(name.into());
        let Err(e) = extract_checked(&input, true, &roots) else {
            panic!("a rejected function was extracted");
        };
        assert!(e.contains(name) && e.contains("rejected"), "{e}");
    }
}

/// A row as written, a set expression: its effects `{A, B}`, then its variable united with them,
/// `{A, B} ∪ e`; a row of a variable alone is `e`.
fn row_text(row: &[String]) -> String {
    let (vars, effects): (Vec<&String>, Vec<&String>) =
        row.iter().partition(|e| e.starts_with('|'));
    let effects = effects
        .iter()
        .map(|e| e.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    match vars.first() {
        Some(v) if effects.is_empty() => v[1..].to_string(),
        Some(v) => format!("{{{effects}}} ∪ {}", &v[1..]),
        None => format!("{{{effects}}}"),
    }
}

/// Whether the prelude every Nib program sees declares a function `name` (`not`): extraction calls
/// it and does not write it out.
fn nib_prelude_fn(name: &str) -> bool {
    static NAMES: std::sync::OnceLock<HashSet<String>> = std::sync::OnceLock::new();
    NAMES
        .get_or_init(|| {
            crate::surface::parse_program_as_written(crate::nibstd::PRELUDE)
                .map(|p| {
                    p.stmts
                        .iter()
                        .filter_map(|s| match s {
                            Stmt::Fn(f) => Some(f.name.clone()),
                            _ => None,
                        })
                        .collect()
                })
                .unwrap_or_default()
        })
        .contains(name)
}

/// Where `Extractor::shape` took a part out of a pattern; not a name a
/// program can write.
const HOLE: &str = "\u{0}hole";

/// `shape` with its holes, in order, as the names of `names`.
fn fill_holes<'n>(shape: &Pattern, names: &mut impl Iterator<Item = &'n String>) -> Pattern {
    match shape {
        Pattern::Bind(n) if n == HOLE => Pattern::Bind(names.next().cloned().unwrap_or_default()),
        Pattern::Ctor { name, args } => Pattern::Ctor {
            name: name.clone(),
            args: args.iter().map(|q| fill_holes(q, names)).collect(),
        },
        Pattern::Tuple(items) => {
            Pattern::Tuple(items.iter().map(|q| fill_holes(q, names)).collect())
        }
        other => other.clone(),
    }
}

/// Whether some value has both shapes (a hole has every value). A pattern
/// `shape` does not take apart is taken to overlap.
fn overlap(a: &Pattern, b: &Pattern) -> bool {
    match (a, b) {
        (Pattern::Bind(n), _) | (_, Pattern::Bind(n)) if n == HOLE => true,
        (Pattern::Ctor { name: m, args: x }, Pattern::Ctor { name: n, args: y }) => {
            m == n && x.len() == y.len() && x.iter().zip(y).all(|(p, q)| overlap(p, q))
        }
        (Pattern::Tuple(x), Pattern::Tuple(y)) => {
            x.len() == y.len() && x.iter().zip(y).all(|(p, q)| overlap(p, q))
        }
        _ => true,
    }
}

/// `p` with the labels at its head taken off: `@a @b q` is `q`.
fn unlabel(p: &Pattern) -> Pattern {
    let mut p = p;
    while let Some((_, inner)) = p.label() {
        p = inner;
    }
    p.clone()
}
