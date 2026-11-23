//! `tauto build --backend llvm`: the program goes through the same NIR passes
//! as niri and the Rust backend (`mono::specialize`, `anf::normalize`,
//! `ownership::insert`), `tauto_llvm::emit` writes it as one LLVM module, and
//! `clang` turns the module into a program. Where the runtime has a layer of
//! system calls (Linux on x86_64) the program links no library; elsewhere it
//! is built on the C library.
//!
//! The build is reproducible: the same module gives the same bytes. The
//! module is compiled as `main.ll` in a directory of its own, so no path of
//! the machine reaches the object; no debug information is written, and the
//! linker writes no build ID. What still varies is the `clang` and the linker
//! themselves, which the caller fixes.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

/// The flags `clang` compiles and links the module with, besides the ones of
/// the system the program is built on (`tauto_llvm::Sys::link_flags`).
pub(crate) const CLANG_FLAGS: &[&str] =
    &["-O2", "-g0", "-Wno-override-module", "-Wl,--build-id=none"];

pub(crate) fn command(args: &[String]) -> ExitCode {
    // `--emit llvm` writes the module instead of the program, and `--emit nir`
    // the package the backend reads, as NIR text (what `totes/llvm` reads);
    // `-o` names the
    // file written. The rest is read as `tauto run` reads it.
    let mut emit = false;
    let mut emit_nir = false;
    // `--export NAME`: entries added to the tote's `exports`.
    let mut added_exports: Vec<String> = Vec::new();
    let mut out: Option<String> = None;
    let mut rest = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--emit" => match it.next().map(String::as_str) {
                Some("llvm") => emit = true,
                Some("nir") => emit_nir = true,
                _ => return super::usage(),
            },
            "--export" => match it.next() {
                Some(name) => added_exports.push(name.clone()),
                None => return super::usage(),
            },
            "-o" => match it.next() {
                Some(o) => out = Some(o.clone()),
                None => return super::usage(),
            },
            _ => rest.push(a.clone()),
        }
    }
    let run = match super::parse_run_args(&rest) {
        Ok(run) => run,
        Err(code) => return code,
    };
    if run.check_ownership || run.steps.is_some() || run.yes || !run.program_args.is_empty() {
        return super::usage();
    }
    let loaded = match run.load_exporting(&added_exports) {
        Ok(loaded) => loaded,
        Err(code) => return code,
    };
    let entry = run.entry();
    if let Err(code) = super::require_entry(&loaded, &entry) {
        return code;
    }
    // The functions a host calls by name: the tote's `exports` and those
    // `--export` adds. A program with none has only its top level.
    let (tote_dir, mut exports) = match &run.tote {
        Some(_) => {
            let dir = match run.tote_dir() {
                Ok(d) => d,
                Err(code) => return code,
            };
            let exports = match tauto::manifest::load(&dir) {
                Ok(m) => m.exports,
                Err(e) => {
                    eprintln!("{e}");
                    return ExitCode::FAILURE;
                }
            };
            (Some(dir), exports)
        }
        None => (None, None),
    };
    let selection = match &run.tote {
        Some(_) => {
            if !added_exports.is_empty() {
                exports.get_or_insert_with(Vec::new).extend(added_exports);
            }
            match &exports {
                Some(list) => {
                    let totes = match &tote_dir {
                        Some(d) => match tauto::program::tote_dirs(d) {
                            Ok(t) => t,
                            Err(e) => {
                                eprintln!("{e}");
                                return ExitCode::FAILURE;
                            }
                        },
                        None => Vec::new(),
                    };
                    tauto_nibcheck::lower::select_exports(&loaded, list, &totes, None).map(Some)
                }
                None => Ok(None),
            }
        }
        // A file entry belongs to the tote that holds it: that tote's
        // `exports` and the totes it reads count as for the tote itself.
        None => match run.file.as_deref() {
            Some(file) => tauto::program::select_file_exports(&loaded, Path::new(file), &added_exports),
            None => Ok(None),
        },
    };
    let selection = match selection {
        Ok(Some(s)) => {
            for name in &s.skipped {
                eprintln!(
                    "{}",
                    crate::i18n::t!("rust-export-generic-skipped", path = &entry, name = name)
                );
            }
            Some(s)
        }
        Ok(None) => None,
        Err(e) => {
            eprintln!("{entry}: {e}");
            return ExitCode::FAILURE;
        }
    };
    let mut pkg = match tauto_nibcheck::lower::compile_loaded_entries_with_observer(
        &loaded,
        selection.is_some(),
        tauto_nir::Target::Llvm,
        selection.as_ref().map(|s| &s.names),
        |_| {},
    ) {
        Ok(pkg) => pkg,
        Err(
            tauto_nibcheck::lower::CompileError::Front(m)
            | tauto_nibcheck::lower::CompileError::Package(m),
        ) => {
            eprintln!("{}", super::locate_front(&loaded, &entry, &m));
            return ExitCode::FAILURE;
        }
        Err(e) => return refused(&entry, &format!("{e:?}")),
    };
    // A host finds an export by its tote, module and name, whatever else the
    // program declares.
    if let Some(selection) = &selection {
        selection.name_exports(&mut pkg.exports);
    }
    if let Err(e) = tauto_nir::mono::specialize(&mut pkg) {
        return refused(&entry, &e);
    }
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    if emit_nir {
        let stem = Path::new(&entry)
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "main".into());
        let out = out.unwrap_or_else(|| format!("{stem}.nir"));
        let text = match tauto_nir::text::print(&pkg) {
            Ok(t) => t,
            Err(e) => return refused(&entry, &e),
        };
        return match std::fs::write(&out, text) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("{out}: {e}");
                ExitCode::FAILURE
            }
        };
    }
    let module = match tauto_llvm::emit_on(&pkg, tauto_llvm::Sys::host()) {
        Ok(m) => m,
        Err(e) => return refused(&entry, &e.0),
    };
    let stem = Path::new(&entry)
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "main".into());
    if emit {
        let out = out.unwrap_or_else(|| format!("{stem}.ll"));
        return match std::fs::write(&out, module) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("{out}: {e}");
                ExitCode::FAILURE
            }
        };
    }
    let out = PathBuf::from(out.unwrap_or(stem));
    match link(&module, &out) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{}", crate::i18n::t!("llvm-clang", what = e));
            ExitCode::FAILURE
        }
    }
}

fn refused(entry: &str, what: &str) -> ExitCode {
    eprintln!(
        "{}",
        crate::i18n::t!("llvm-refused", entry = entry, what = what)
    );
    ExitCode::from(2)
}

/// Compiles `module` with `clang` into the program `out`.
fn link(module: &str, out: &Path) -> Result<(), String> {
    let dir = tempdir()?;
    let result = (|| {
        std::fs::write(dir.join("main.ll"), module).map_err(|e| e.to_string())?;
        let built = Command::new("clang")
            .current_dir(&dir)
            .args(CLANG_FLAGS)
            .args(tauto_llvm::Sys::host().link_flags())
            .args(["-o", "main", "main.ll"])
            .output()
            .map_err(|e| format!("clang: {e}"))?;
        if !built.status.success() {
            return Err(String::from_utf8_lossy(&built.stderr).trim().to_string());
        }
        std::fs::copy(dir.join("main"), out).map_err(|e| format!("{}: {e}", out.display()))?;
        Ok(())
    })();
    let _ = std::fs::remove_dir_all(&dir);
    result
}

fn tempdir() -> Result<PathBuf, String> {
    let base = std::env::temp_dir();
    for n in 0..1000u32 {
        let d = base.join(format!("tauto-llvm-{}-{n}", std::process::id()));
        if std::fs::create_dir(&d).is_ok() {
            return Ok(d);
        }
    }
    Err("no temporary directory".into())
}
