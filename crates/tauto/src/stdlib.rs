//! The standard library that comes with tauto: `import std::List` reads
//! `std/List.taut` as it was when tauto was built, wherever the importing
//! file is. The files are read under [`ROOT`], a path that is not on disk, so
//! the imports between them (`import "Base.taut"`) resolve among themselves.
//! The same `import name.Module` names a module of a dependency tote.

use std::path::{Path, PathBuf};

use tauto_message::{Message, msg};

/// The directory the standard library's files are read from.
pub const ROOT: &str = "/<tauto-std>";

/// The parser tables of the syntaxes the standard library declares
/// (`std/.tauto-syntax/` and `std/proof/.tauto-syntax/`), as they were when
/// tauto was built: a program that imports `std::Mode` has no
/// `.tauto-syntax` beside the library's files to read them from.
pub const SYNTAX_TABLES: &[&str] = &[
    include_str!("../../../std/.tauto-syntax/e3a1daede76b420879e8b463d6b4ff34d67accf16ce8b669437837ce7fb0d8ad.tables"),
    include_str!("../../../std/.tauto-syntax/8002b584d6ccfb34dd9822833dd92f3dfac96ef475b74066dbc58eaa6ea4fba7.tables"),
    include_str!("../../../std/.tauto-syntax/d082dbd36acfbc610dde69051b3d77d25305e8106db261bb13452d874f1277de.tables"),
    include_str!("../../../std/proof/.tauto-syntax/8ea91dead6c8a3d9aadf0ccad902e4728eac1b7ebe3a984f8a7f12e735dfed0b.tables"),
];

/// Each file of `std/` (the prelude aside, which every program has) and its text.
pub const FILES: &[(&str, &str)] = &[
("proof/Forms.taut", include_str!("../../../std/proof/Forms.taut")),
("proof/Lang.taut", include_str!("../../../std/proof/Lang.taut")),
    (
        "proof/Tooling.taut",
        include_str!("../../../std/proof/Tooling.taut"),
    ),
    ("Array.taut", include_str!("../../../std/Array.taut")),
    ("Base.taut", include_str!("../../../std/Base.taut")),
    ("BinNat.taut", include_str!("../../../std/BinNat.taut")),
    ("Calc.taut", include_str!("../../../std/Calc.taut")),
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
    ("SynTree.taut", include_str!("../../../std/SynTree.taut")),
    ("Tactic.taut", include_str!("../../../std/Tactic.taut")),
    ("Text.taut", include_str!("../../../std/Text.taut")),
    ("TextOps.taut", include_str!("../../../std/TextOps.taut")),
    ("UInt.taut", include_str!("../../../std/UInt.taut")),
    (
        "WellFounded.taut",
        include_str!("../../../std/WellFounded.taut"),
    ),
    ("asm.taut", include_str!("../../../std/asm.taut")),
    // The files of the prelude (`docs/design/visibility.md`「prelude」):
    // `import std::prelude::Os` reads an empty file, and a file that imports
    // it sees the names of `std/prelude/Os.taut`. A file sees the core ones
    // (`Std`, `Text`, `Num`) without the import, unless its tote has no prelude.
    ("prelude/Affine.taut", ""),
    ("prelude/Classes.taut", ""),
    ("prelude/Macro.taut", ""),
    ("prelude/Num.taut", ""),
    ("prelude/Ord.taut", ""),
    ("prelude/Os.taut", ""),
    ("prelude/Par.taut", ""),
    ("prelude/Secret.taut", ""),
    ("prelude/Shared.taut", ""),
    ("prelude/Std.taut", ""),
    ("prelude/Text.taut", ""),
];

/// The file the module import `import std::List` names, or why it names none.
/// A name other than `std::` is a dependency of the importing file's tote:
/// [`import_target`].
pub fn import_path(name: &str) -> Result<PathBuf, Message> {
    match tauto_surface::surface::qualify::module_root(name) {
        (tauto_surface::surface::qualify::STD_ROOT, Some(module)) => {
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
        _ => Err(import_error(
            name,
            msg!(
                "tauto-import-not-dependency",
                dependency = crate::manifest::tote_of_import_name(
                    name.split("::").next().unwrap_or(name)
                )
            ),
        )),
    }
}

/// The file an import in `from` names: `import std::List` from the standard
/// library, `import text::Utf8` (`Utf8.taut`) from the `src` of
/// the dependency `text` (`import text::proof::Utf8` from its additional source `proof`) in the `dependencies` of `from`'s tote, and a quoted
/// path (not `module`) relative to `from`, whatever it is spelled like, and
/// `import self::b` (`b.taut` in the directory named like `from`, without `.taut`).
pub fn import_target(from: &Path, name: &str, module: bool) -> Result<PathBuf, Message> {
    if !module {
        let joined = from.parent().unwrap_or(Path::new(".")).join(name);
        // The standard library's files are not on disk, so nothing resolves
        // `..` in an import such as `import "../Tactic.taut"` from a file of `proof/`: the path
        // is folded here, staying under [`ROOT`].
        if from.starts_with(ROOT) {
            return Ok(fold_parents(&joined));
        }
        return Ok(joined);
    }
    // `import self::b::c` in `a.taut` is `a/b/c.taut`: the file's own
    // modules, in the directory named like the file.
    if let (crate::manifest::SELF_ROOT, rest) =
        tauto_surface::surface::qualify::module_root(name)
    {
        let Some(rest) = rest else {
            return Err(import_error(name, msg!("tauto-import-self-alone")));
        };
        let stem = from.file_stem().unwrap_or_default();
        let joined = from
            .parent()
            .unwrap_or(Path::new("."))
            .join(stem)
            .join(format!("{}.taut", rest.replace("::", "/")));
        if from.starts_with(ROOT) {
            return Ok(fold_parents(&joined));
        }
        return Ok(joined);
    }
    let named = import_path(name);
    if matches!(
        tauto_surface::surface::qualify::module_root(name),
        (tauto_surface::surface::qualify::STD_ROOT, Some(_))
    ) {
        return named;
    }
    let (written, module) = name.split_once("::").unwrap_or((name, ""));
    let dependency = &crate::manifest::tote_of_import_name(written);
    let dependency = dependency.as_str();
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
            msg!("tauto-import-name-module", dependency = written),
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
    // A file that is there but outside the sources: the dependency has not
    // made it readable, and says how it can.
    let outside = ["taut", "tauto"]
        .iter()
        .map(|ext| dir.join(format!("{stem}.{ext}")))
        .find(|path| path.is_file());
    match hits.len() {
        1 => Ok(hits.pop().unwrap()),
        0 if let Some(path) = outside => Err(import_error(
            name,
            msg!(
                "tauto-import-outside-sources",
                dependency = dependency,
                module = module,
                path = path.display().to_string(),
                sources = found.package.source_paths().join(", "),
                source = stem.split('/').next().unwrap_or_default()
            ),
        )),
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
    declaration_modules().get(name).copied()
}

fn declaration_modules() -> &'static std::collections::HashMap<String, &'static str> {
    static MODULES: std::sync::OnceLock<std::collections::HashMap<String, &'static str>> =
        std::sync::OnceLock::new();
    MODULES.get_or_init(|| {
        let mut modules = std::collections::HashMap::new();
        for (file, text) in FILES {
            let mut current = None;
            for raw in text.lines() {
                if let Some(rest) = raw.strip_prefix("module ") {
                    current = rest.strip_suffix('{').map(str::trim);
                    continue;
                }
                if raw.starts_with('}') {
                    current = None;
                    continue;
                }
                let line = raw.trim_start();
                let line = line
                    .strip_prefix("pub(open) ")
                    .or_else(|| line.strip_prefix("pub "))
                    .unwrap_or(line);
                let mut words = line
                    .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                    .filter(|word| !word.is_empty());
                if matches!(
                    words.next(),
                    Some("fn" | "theorem" | "def" | "inductive" | "struct" | "class" | "axiom")
                ) && let Some(short) = words.next()
                {
                    let name = current
                        .map_or_else(|| short.to_string(), |module| format!("{module}::{short}"));
                    modules
                        .entry(name)
                        .or_insert_with(|| file.strip_suffix(".taut").unwrap_or(file));
                }
            }
        }
        modules
    })
}

/// `path` with each `a/..` and `.` removed, without reading the disk.
fn fold_parents(path: &Path) -> PathBuf {
    use std::path::Component;
    let mut out = PathBuf::new();
    for c in path.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir if out.file_name().is_some() => {
                out.pop();
            }
            c => out.push(c),
        }
    }
    out
}

pub fn text(path: &Path) -> Option<&'static str> {
    let name = path.strip_prefix(ROOT).ok()?.to_str()?;
    // A syntax of the library is read with its file, on whichever thread and
    // through whichever command reads it.
    static TABLES: std::sync::Once = std::sync::Once::new();
    TABLES.call_once(|| {
        for text in SYNTAX_TABLES {
            // Tables embedded at build time and checked by a test.
            let _ = crate::syntax::register_tables(text);
        }
    });
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
fn import_error(name: &str, message: Message) -> Message {
    msg!("tauto-import-error", name = name, message = message)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn linear_module_of(name: &str) -> Option<&'static str> {
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

    #[test]
    fn indexed_declaration_modules_match_source_lookup() {
        let modules = declaration_modules();
        let mut names: Vec<_> = modules.keys().collect();
        names.sort();
        for name in names.iter().step_by(101) {
            assert_eq!(module_of(name), linear_module_of(name), "{name}");
        }
        for name in [
            "Nat::add",
            "List::map",
            "Rat::add",
            "Text",
            "no_such_declaration",
            "Missing::add",
            "",
            "Nat::",
        ] {
            assert_eq!(module_of(name), linear_module_of(name), "{name}");
        }
    }

    /// Every table under `std/` is listed in [`SYNTAX_TABLES`], so adding a
    /// syntax to the library cannot leave `import std::…` without its tables.
    #[test]
    fn every_std_table_is_embedded() {
        let std = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
        let mut found = 0;
        for dir in [std.join(".tauto-syntax"), std.join("proof/.tauto-syntax")] {
            for entry in std::fs::read_dir(dir).unwrap() {
                let text = std::fs::read_to_string(entry.unwrap().path()).unwrap();
                assert!(SYNTAX_TABLES.contains(&text.as_str()));
                found += 1;
            }
        }
        assert_eq!(found, SYNTAX_TABLES.len());
    }
}
