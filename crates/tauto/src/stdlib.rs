//! The standard library that comes with tauto: `import std::List` reads
//! `std/List.taut` as it was when tauto was built, wherever the importing
//! file is. The files are read under [`ROOT`], a path that is not on disk, so
//! the imports between them (`import "Base.taut"`) resolve among themselves.
//! The same `import name.Module` names a module of a dependency tote.

use std::path::{Path, PathBuf};

use tauto_message::{Message, msg};

/// The directory the standard library's files are read from.
pub const ROOT: &str = "/<tauto-std>";

/// Each file of `std/` (the prelude aside, which every program has) and its text.
pub const FILES: &[(&str, &str)] = &[
    ("Array.taut", include_str!("../../../std/Array.taut")),
    ("Base.taut", include_str!("../../../std/Base.taut")),
    ("BinNat.taut", include_str!("../../../std/BinNat.taut")),
    ("Bytes.taut", include_str!("../../../std/Bytes.taut")),
    ("Data.taut", include_str!("../../../std/Data.taut")),
    ("Deque.taut", include_str!("../../../std/Deque.taut")),
    ("Effect.taut", include_str!("../../../std/Effect.taut")),
    ("Float.taut", include_str!("../../../std/Float.taut")),
    ("Float32.taut", include_str!("../../../std/Float32.taut")),
    (
        "FloatBoundsA.taut",
        include_str!("../../../std/FloatBoundsA.taut"),
    ),
    (
        "FloatBoundsB.taut",
        include_str!("../../../std/FloatBoundsB.taut"),
    ),
    (
        "FloatBoundsC.taut",
        include_str!("../../../std/FloatBoundsC.taut"),
    ),
    (
        "FloatDecode.taut",
        include_str!("../../../std/FloatDecode.taut"),
    ),
    (
        "FloatEncode.taut",
        include_str!("../../../std/FloatEncode.taut"),
    ),
    (
        "FloatError.taut",
        include_str!("../../../std/FloatError.taut"),
    ),
    (
        "FloatOfRat.taut",
        include_str!("../../../std/FloatOfRat.taut"),
    ),
    (
        "FloatPack.taut",
        include_str!("../../../std/FloatPack.taut"),
    ),
    (
        "FloatReal.taut",
        include_str!("../../../std/FloatReal.taut"),
    ),
    (
        "FloatRound.taut",
        include_str!("../../../std/FloatRound.taut"),
    ),
    ("HashMap.taut", include_str!("../../../std/HashMap.taut")),
    ("Heap.taut", include_str!("../../../std/Heap.taut")),
    ("Int.taut", include_str!("../../../std/Int.taut")),
    ("IntLaws.taut", include_str!("../../../std/IntLaws.taut")),
    ("IntNorm.taut", include_str!("../../../std/IntNorm.taut")),
    ("IntOrder.taut", include_str!("../../../std/IntOrder.taut")),
    ("List.taut", include_str!("../../../std/List.taut")),
    ("Map.taut", include_str!("../../../std/Map.taut")),
    ("MapLaws.taut", include_str!("../../../std/MapLaws.taut")),
    (
        "MapRemoveFloor.taut",
        include_str!("../../../std/MapRemoveFloor.taut"),
    ),
    ("MapText.taut", include_str!("../../../std/MapText.taut")),
    ("Mode.taut", include_str!("../../../std/Mode.taut")),
    ("Nat.taut", include_str!("../../../std/Nat.taut")),
    ("NatDiv.taut", include_str!("../../../std/NatDiv.taut")),
    ("NatNorm.taut", include_str!("../../../std/NatNorm.taut")),
    ("Ord.taut", include_str!("../../../std/Ord.taut")),
    ("Quot.taut", include_str!("../../../std/Quot.taut")),
    ("Rat.taut", include_str!("../../../std/Rat.taut")),
    ("RatField.taut", include_str!("../../../std/RatField.taut")),
    ("RatLaws.taut", include_str!("../../../std/RatLaws.taut")),
    ("Real.taut", include_str!("../../../std/Real.taut")),
    ("Refined.taut", include_str!("../../../std/Refined.taut")),
    ("Rewrite.taut", include_str!("../../../std/Rewrite.taut")),
    ("Row.taut", include_str!("../../../std/Row.taut")),
    ("SInt.taut", include_str!("../../../std/SInt.taut")),
    ("Secret.taut", include_str!("../../../std/Secret.taut")),
    ("Set.taut", include_str!("../../../std/Set.taut")),
    ("Sort.taut", include_str!("../../../std/Sort.taut")),
    ("Stack.taut", include_str!("../../../std/Stack.taut")),
    ("State.taut", include_str!("../../../std/State.taut")),
    ("Std.taut", include_str!("../../../std/Std.taut")),
    ("Tactic.taut", include_str!("../../../std/Tactic.taut")),
    ("Text.taut", include_str!("../../../std/Text.taut")),
    ("TextOps.taut", include_str!("../../../std/TextOps.taut")),
    ("UInt.taut", include_str!("../../../std/UInt.taut")),
    (
        "WellFounded.taut",
        include_str!("../../../std/WellFounded.taut"),
    ),
    // The files of the prelude that are not core
    // (`docs/design/visibility.md`「prelude」): `import std::prelude::Os`
    // reads an empty file, and a file that imports it sees the names of
    // `std/prelude/Os.taut`.
    ("prelude/Affine.taut", ""),
    ("prelude/Classes.taut", ""),
    ("prelude/Macro.taut", ""),
    ("prelude/Ord.taut", ""),
    ("prelude/Os.taut", ""),
    ("prelude/Par.taut", ""),
    ("prelude/Secret.taut", ""),
    ("prelude/Shared.taut", ""),
];

/// The file the module import `import std::List` names, or why it names none.
/// A name other than `std::` is a dependency of the importing file's tote:
/// [`import_target`].
pub fn import_path(name: &str) -> Result<PathBuf, String> {
    match name.strip_prefix("std::") {
        Some(module) => {
            let file = format!("{}.taut", module.replace("::", "/"));
            if FILES.iter().any(|(f, _)| *f == file) {
                Ok(Path::new(ROOT).join(file))
            } else {
                Err(import_error(
                    name,
                    msg!("tauto-import-no-std-module", module = module),
                ))
            }
        }
        None => Err(import_error(
            name,
            msg!(
                "tauto-import-not-dependency",
                dependency = name.split("::").next().unwrap_or(name)
            ),
        )),
    }
}

/// The file an import in `from` names: `import std::List` from the standard
/// library, `import text::Utf8` (`Utf8.taut`) from the `src` of
/// the dependency `text` (`import text::proof::Utf8` from its additional source `proof`) in the `dependencies` of `from`'s tote, and a quoted
/// path (not `module`) relative to `from`, whatever it is spelled like.
pub fn import_target(from: &Path, name: &str, module: bool) -> Result<PathBuf, String> {
    if !module {
        return Ok(from.parent().unwrap_or(Path::new(".")).join(name));
    }
    let named = import_path(name);
    if name.starts_with("std::") {
        return named;
    }
    let (dependency, module) = name.split_once("::").unwrap_or((name, ""));
    let tote = (text(from).is_none())
        .then(|| crate::program::canonical_path(from))
        .and_then(|f| {
            f.ancestors()
                .skip(1)
                .find(|d| d.join("Tauto.eure").is_file())
                .map(Path::to_path_buf)
        });
    let Some(tote) = tote else {
        return named;
    };
    let manifest = crate::manifest::read(&tote)?;
    let Some((_, found)) = manifest.dependencies.iter().find(|(n, _)| n == dependency) else {
        return named;
    };
    let dir = crate::manifest::dependency_dir(&tote, dependency, found)
        .map_err(|e| import_error(name, Message::text(e)))?;
    let found = crate::manifest::read(&dir).map_err(|e| {
        let e = msg!("tauto-dep-error", name = dependency, error = e);
        import_error(name, e)
    })?;
    if found.package.name != dependency {
        return Err(import_error(
            name,
            msg!(
                "tauto-import-misnamed",
                dir = dir.display().to_string(),
                found = &found.package.name,
                dependency = dependency
            ),
        ));
    }
    if module.is_empty()
        || module
            .split("::")
            .any(|p| p.is_empty() || p.contains(['/', '\\']))
    {
        return Err(import_error(
            name,
            msg!("tauto-import-name-module", dependency = dependency),
        ));
    }
    let stem = module.replace("::", "/");
    let mut hits = Vec::new();
    // A file of `src` is named by its path from `src`; one of an additional
    // source by its path from the tote's root, which starts with the source.
    for ext in ["taut", "tauto"] {
        let path = dir
            .join(crate::manifest::DEFAULT_SOURCE)
            .join(format!("{stem}.{ext}"));
        if path.is_file() {
            hits.push(path);
        }
        let path = dir.join(format!("{stem}.{ext}"));
        if path.is_file()
            && found
                .package
                .additional_sources
                .iter()
                .any(|source| path.starts_with(dir.join(source)))
        {
            hits.push(path);
        }
    }
    match hits.len() {
        1 => Ok(hits.pop().unwrap()),
        0 => Err(import_error(
            name,
            msg!(
                "tauto-import-no-module",
                dependency = dependency,
                module = module,
                stem = stem.as_str(),
                sources = found.package.source_paths().join(", ")
            ),
        )),
        _ => Err(import_error(
            name,
            msg!(
                "tauto-import-many-modules",
                dependency = dependency,
                module = module,
                paths = hits
                    .iter()
                    .map(|p| p.display().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        )),
    }
}

/// For "`nat_max` is not defined", where the standard library declares
/// `nat_max`: "; it is in the standard library: `import std::Nat`".
pub fn not_imported(message: &str) -> Option<String> {
    let name = message.strip_suffix("` is not defined")?;
    let name = &name[name.rfind('`')? + 1..];
    not_imported_name(name).map(|m| m.to_string())
}

/// For `nat_max`, which the standard library declares: "; it is in the
/// standard library: `import std::Nat`".
pub fn not_imported_name(name: &str) -> Option<tauto_message::Message> {
    let module = module_of(name)?;
    Some(tauto_message::msg!("tauto-in-std", module = module))
}

/// The module of the standard library that declares `name`, as
/// `import std::MODULE` names it: for a built-in of the prelude such as
/// `text_len`, the model the kernel checks of it.
pub fn module_of(name: &str) -> Option<&'static str> {
    // `M::f` is `f` in a `module M { … }` block (a declaration at column 0 ends it).
    let (module, short) = match name.rsplit_once("::") {
        Some((m, s)) => (Some(m), s),
        None => (None, name),
    };
    FILES.iter().find_map(|(file, text)| {
        let mut current: Option<&str> = None;
        let declares = text.lines().any(|raw| {
            if let Some(rest) = raw.strip_prefix("module ") {
                current = rest.strip_suffix('{').map(str::trim);
                return false;
            }
            if raw.starts_with('}') {
                current = None;
                return false;
            }
            if current != module {
                return false;
            }
            let line = raw.trim_start();
            let line = line
                .strip_prefix("pub(open) ")
                .or_else(|| line.strip_prefix("pub "))
                .unwrap_or(line);
            let mut words = line
                .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .filter(|w| !w.is_empty());
            matches!(
                words.next(),
                Some("fn" | "theorem" | "def" | "inductive" | "struct" | "class" | "axiom")
            ) && words.next() == Some(short)
        });
        declares.then(|| file.strip_suffix(".taut").unwrap_or(file))
    })
}

pub fn text(path: &Path) -> Option<&'static str> {
    let name = path.strip_prefix(ROOT).ok()?.to_str()?;
    FILES.iter().find(|(f, _)| *f == name).map(|(_, t)| *t)
}

/// The module a path names as a standard library file, `Base` for
/// `…/Base.taut`, when the standard library has a file of that name.
pub fn module_of_path(path: &Path) -> Option<&'static str> {
    let name = path.file_name()?.to_str()?;
    FILES
        .iter()
        .find(|(f, _)| *f == name)
        .map(|(f, _)| f.strip_suffix(".taut").unwrap_or(f))
}

/// The module of the standard library that a file read from disk is a copy
/// of: one named as a standard library file, with its text or in a
/// directory `std`. Reading it by path as well as `import std.…` reads the
/// same declarations twice.
pub fn std_copy(path: &Path, text: &str) -> Option<&'static str> {
    let module = module_of_path(path)?;
    let same_text = FILES
        .iter()
        .any(|(f, t)| f.strip_suffix(".taut") == Some(module) && *t == text);
    let in_std = path
        .parent()
        .and_then(Path::file_name)
        .is_some_and(|d| d == "std");
    (same_text || in_std).then_some(module)
}

/// The text of a source file: the standard library's from tauto, others from disk.
pub fn read(path: &Path) -> std::io::Result<String> {
    match text(path) {
        Some(t) => Ok(t.to_string()),
        None => std::fs::read_to_string(path),
    }
}

/// "`import NAME`: MESSAGE", as text.
fn import_error(name: &str, message: Message) -> String {
    msg!("tauto-import-error", name = name, message = message).to_string()
}
