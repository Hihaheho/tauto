//! The prelude every program sees, as source (`std/prelude/`): `std/prelude/Std.taut`, the ω library
//! (`Shared.taut`) and the affine one (`Affine.taut`) of
//! `docs/design/ownership.md`「標準ライブラリ」.
//! Every program sees its declarations before its own; a program's own
//! declaration of a name hides the library's.

/// `std/prelude/Std.taut`, whose `Option`, `List`, `Pair` and `Ordering`
/// the proofs see as families too (`crates/tauto-kernel/src/check.rs`).
pub const STD: &str = include_str!("../../../std/prelude/Std.taut");

/// `std/prelude/Ord.taut`: the class `Ord` and the instances whose laws the
/// kernel proves, which the proofs see too (`crates/tauto-kernel/src/check.rs`).
pub const ORD: &str = include_str!("../../../std/prelude/Ord.taut");

/// The kernel's own inductives (`Nat`, `Eq`, `And`, …): what a macro's
/// output may name in a pattern before any file declares it.
pub const KERNEL: &str = include_str!("../../tauto-kernel/src/prelude.taut");

/// The kernel's functions on numerals and decidable equality
/// (`Nat::lt`, …), declared in modules: what a module of a file may call by
/// its short name.
pub const KERNEL_MODULES: &[&str] = &[
    include_str!("../../tauto-kernel/src/prelude_nat.taut"),
    include_str!("../../tauto-kernel/src/prelude_deq.taut"),
];

pub const PRELUDE: &str = concat!(
    include_str!("../../../std/prelude/Std.taut"),
    "\n",
    include_str!("../../../std/prelude/Shared.taut"),
    "\n",
    include_str!("../../../std/prelude/Affine.taut"),
    "\n",
    include_str!("../../../std/prelude/Text.taut"),
    "\n",
    include_str!("../../../std/prelude/Num.taut"),
    "\n",
    include_str!("../../../std/prelude/Os.taut"),
    "\n",
    include_str!("../../../std/prelude/Macro.taut"),
    "\n",
    include_str!("../../../std/prelude/Ord.taut"),
    "\n",
    include_str!("../../../std/prelude/Classes.taut"),
    "\n",
    include_str!("../../../std/prelude/Par.taut"),
    "\n",
    include_str!("../../../std/prelude/Secret.taut"),
);

// The functions the evaluator implements are the prelude's `extern`
// functions; a program's own `extern` functions are the host's.

/// The files of [`PRELUDE`], in order, each followed by one `\n`.
pub const PRELUDE_FILES: &[(&str, &str)] = &[
    (
        "std/prelude/Std.taut",
        include_str!("../../../std/prelude/Std.taut"),
    ),
    (
        "std/prelude/Shared.taut",
        include_str!("../../../std/prelude/Shared.taut"),
    ),
    (
        "std/prelude/Affine.taut",
        include_str!("../../../std/prelude/Affine.taut"),
    ),
    (
        "std/prelude/Text.taut",
        include_str!("../../../std/prelude/Text.taut"),
    ),
    (
        "std/prelude/Num.taut",
        include_str!("../../../std/prelude/Num.taut"),
    ),
    (
        "std/prelude/Os.taut",
        include_str!("../../../std/prelude/Os.taut"),
    ),
    (
        "std/prelude/Macro.taut",
        include_str!("../../../std/prelude/Macro.taut"),
    ),
    (
        "std/prelude/Ord.taut",
        include_str!("../../../std/prelude/Ord.taut"),
    ),
    (
        "std/prelude/Classes.taut",
        include_str!("../../../std/prelude/Classes.taut"),
    ),
    (
        "std/prelude/Par.taut",
        include_str!("../../../std/prelude/Par.taut"),
    ),
    (
        "std/prelude/Secret.taut",
        include_str!("../../../std/prelude/Secret.taut"),
    ),
];

/// The files of [`PRELUDE_FILES`] that are core: seen by every file without an
/// import. They are the files whose declarations literals, tuples, lists and
/// `perform show` produce or need (`docs/design/visibility.md`「prelude」); the other
/// files of `std/prelude/` are seen by importing `std::prelude::<file>`.
pub const CORE_PRELUDE_FILES: &[&str] = &[
    "std/prelude/Std.taut",
    "std/prelude/Text.taut",
    "std/prelude/Num.taut",
];

/// Whether the file at `path` of [`PRELUDE_FILES`] is core.
pub fn is_core_prelude_file(path: &str) -> bool {
    CORE_PRELUDE_FILES.contains(&path)
}

/// An error of reading prelude text whose spans start at `base`, with its
/// ` at byte N` written as the place in the file it is in
/// (` at std/prelude/Ord.taut:412:20`): a byte past `PRELUDE_BASE` names
/// no file anyone can open. `files` are the files the text is made of, each
/// followed by one `\n` (a single file is `&[(path, text)]`). An error
/// without a byte, or with one outside the text, stays as it is.
pub fn locate_error(error: String, base: u32, files: &[(&str, &str)]) -> String {
    const AT: &str = " at byte ";
    let Some(i) = error.rfind(AT) else {
        return error;
    };
    let digits = &error[i + AT.len()..];
    let end = digits
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(digits.len());
    let Some(mut at) = digits[..end]
        .parse::<u64>()
        .ok()
        .and_then(|n| n.checked_sub(base as u64))
        .map(|n| n as usize)
    else {
        return error;
    };
    for (path, text) in files {
        if at <= text.len() {
            let before = &text[..text.floor_char_boundary(at)];
            let line = before.matches('\n').count() + 1;
            let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
            return format!("{} at {path}:{line}:{col}{}", &error[..i], &digits[end..]);
        }
        at -= text.len() + 1;
    }
    error
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prelude_files_make_the_prelude() {
        let joined: String = PRELUDE_FILES
            .iter()
            .map(|(_, t)| format!("{t}\n"))
            .collect();
        assert_eq!(
            joined.trim_end_matches('\n'),
            PRELUDE.trim_end_matches('\n')
        );
    }

    #[test]
    fn core_prelude_files_are_prelude_files() {
        for core in CORE_PRELUDE_FILES {
            assert!(PRELUDE_FILES.iter().any(|(path, _)| path == core), "{core}");
        }
    }

    #[test]
    fn an_error_names_the_file_line_and_column() {
        let files = [("a.taut", "x\ny"), ("b.taut", "ab\ncd")];
        let base = 1 << 31;
        let e = |n: u64| {
            locate_error(
                format!("parse-unexpected at byte {}", base as u64 + n),
                base,
                &files,
            )
        };
        assert_eq!(e(0), "parse-unexpected at a.taut:1:1");
        assert_eq!(e(2), "parse-unexpected at a.taut:2:1");
        assert_eq!(e(4), "parse-unexpected at b.taut:1:1");
        assert_eq!(e(8), "parse-unexpected at b.taut:2:2");
        assert_eq!(
            e(100),
            format!("parse-unexpected at byte {}", base as u64 + 100)
        );
        assert_eq!(locate_error("no place".into(), base, &files), "no place");
    }
}
