//! `tauto run --backend rust FILE` and `tauto build [--emit rust] FILE
//! [-o DIR]`.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use tauto_nibcheck::lower::CompileError;
use tauto_rustgen::{BuildEvent, Sources};

use super::timings::{Format, Timings};

fn crate_name(path: &str) -> String {
    let stem = Path::new(path)
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "program".into());
    let mut name: String = stem
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() {
                c.to_ascii_lowercase()
            } else {
                '-'
            }
        })
        .collect();
    if name.is_empty() || !name.chars().next().unwrap().is_ascii_alphabetic() {
        name.insert_str(0, "tauto-");
    }
    name
}

/// Where generated crates are built: `$TAUTO_TARGET_DIR`, else `target/tauto`
/// in the tote's directory, so the output does not depend on where `tauto`
/// was started (like the macro cache). Lone source files use separate
/// namespaces for their canonical paths under the current directory.
fn target_root(tote_dir: Option<&Path>, source: &Path) -> std::io::Result<PathBuf> {
    if let Some(directory) = std::env::var_os("TAUTO_TARGET_DIR") {
        return Ok(directory.into());
    }
    if let Some(directory) = tote_dir {
        return Ok(directory.join("target/tauto"));
    }
    let source = source.canonicalize()?;
    let identity = tauto_syntax::sha256_hex(source.as_os_str().as_encoded_bytes());
    Ok(Path::new("target/tauto").join(format!("run-{identity}")))
}

pub fn command(args: &[String]) -> ExitCode {
    command_with(args, None)
}

pub(crate) fn command_with(
    args: &[String],
    after_build: Option<&mut dyn FnMut(&Path) -> ExitCode>,
) -> ExitCode {
    let command = args[0].as_str();
    let mut path = None;
    let mut tote_name = None;
    let mut target = None;
    let mut declarations = false;
    let mut timing_format = None;
    let mut explain_budget = false;
    // `--export NAME`: entries added to the manifest's `exports`.
    let mut added_exports: Vec<String> = Vec::new();
    let mut update_lock = false;
    let (mut backend, mut emit, mut out_dir, mut release) = (None, None, None, false);
    // What `run` passes to the program after `--`; the permission flags
    // before it are what the user allows at the start (`run_prompt`).
    let mut program_args = Vec::new();
    let mut yes = false;
    let mut allow: Vec<String> = Vec::new();
    let mut steps: Option<u64> = None;
    let mut rest = args[1..].iter();
    while let Some(a) = rest.next() {
        match a.as_str() {
            "--yes" => yes = true,
            // What a built program is allowed, given to `build` and fixed in
            // it; `run` takes none, and asks (`run_prompt`).
            f if command == "build" && (f.starts_with("--allow-") || f == "-A") => {
                allow.push(f.to_string())
            }
            // A limit for the run: `div` is then not asked, and the program
            // reads it as `TAUTO_STEP_LIMIT`.
            "--steps" if command == "run" => {
                match rest.next().and_then(|n| n.parse::<u64>().ok()) {
                    Some(n) if n > 0 => steps = Some(n),
                    _ => return usage(),
                }
            }
            "--" if command == "run" => {
                program_args.extend(rest.by_ref().cloned());
                break;
            }
            "--backend" => {
                backend = rest.next().cloned();
                if backend.is_none() {
                    return usage();
                }
            }
            "--emit" => {
                emit = rest.next().cloned();
                if emit.is_none() {
                    return usage();
                }
            }
            "-o" => {
                out_dir = rest.next().cloned();
                if out_dir.is_none() {
                    return usage();
                }
            }
            "--target" => {
                target = rest.next().cloned();
                if target.is_none() {
                    return usage();
                }
            }
            "--timings" | "--timings=json" if timing_format.is_none() => {
                timing_format = Some(if a == "--timings" {
                    Format::Text
                } else {
                    Format::Json
                });
            }
            "--release" => release = true,
            "--declarations" => declarations = true,
            "--explain-budget" => explain_budget = true,
            "--export" => match rest.next() {
                Some(name) => added_exports.push(name.clone()),
                None => return usage(),
            },
            "--update-lock" => update_lock = true,
            "--tote" => match rest.next() {
                Some(name) if path.is_none() && tote_name.is_none() => {
                    tote_name = Some(name.clone());
                }
                _ => return usage(),
            },
            f if f.starts_with('-') => return usage(),
            p if path.is_none() && tote_name.is_none() => path = Some(p.to_string()),
            _ => return usage(),
        }
    }
    let path = match (path, tote_name) {
        (Some(p), None) => p,
        (None, Some(name)) => {
            let cwd = match std::env::current_dir() {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("{e}");
                    return ExitCode::from(2);
                }
            };
            match tauto::workspace::tote_flag_dir(&cwd, &name) {
                Ok(dir) => dir.display().to_string(),
                Err(e) => {
                    eprintln!("{e}");
                    return ExitCode::from(2);
                }
            }
        }
        _ => return usage(),
    };
    let selected = backend.as_deref().or(emit.as_deref()).unwrap_or("rust");
    if (timing_format.is_some() && command != "build")
        || !matches!(selected, "rust" | "javascript")
        || emit.as_deref().is_some_and(|e| e != selected)
        || (command == "run" && (emit.is_some() || backend.is_none()))
        || (selected == "javascript" && release)
        || (command == "run" && selected == "rust" && target.is_some())
        || (declarations && (selected != "javascript" || command != "build"))
        || (explain_budget && selected != "rust")
        || (update_lock && (selected != "rust" || command != "build" || emit.is_some()))
        || target.as_deref().is_some_and(|t| match selected {
            "javascript" => !matches!(t, "node" | "browser"),
            _ => !tauto_rustgen::WASM_TARGETS.contains(&t),
        })
    {
        return usage();
    }
    // The Rust backend's target triple; the JavaScript backend's target.
    let rust_target = target.clone().filter(|_| selected == "rust");
    let target = match selected {
        "javascript" => target.as_deref().unwrap_or("node"),
        _ => rust_target.as_deref().unwrap_or("host"),
    };
    if command == "run" && selected == "javascript" && target == "browser" {
        eprintln!(
            "{}",
            crate::i18n::t!(
                "rust-browser-run",
                command = "tauto build --backend javascript --target browser"
            )
        );
        return ExitCode::from(2);
    }
    let mut timings = Timings::new(timing_format, selected, target);
    let result = (|| {
        // A tote is a directory with a `Tauto.eure` (or that file); otherwise
        // `path` is one source file, and a `Tauto.eure` beside it is its manifest.
        let p = Path::new(&path);
        let tote_dir = if p.is_dir() {
            Some(p.to_path_buf())
        } else if p.file_name().is_some_and(|n| n == "Tauto.eure") {
            Some(
                p.parent()
                    .filter(|d| !d.as_os_str().is_empty())
                    .unwrap_or(Path::new("."))
                    .to_path_buf(),
            )
        } else {
            None
        };
        let dir_of = match &tote_dir {
            Some(d) => d.clone(),
            None => p
                .parent()
                .filter(|d| !d.as_os_str().is_empty())
                .unwrap_or(Path::new("."))
                .to_path_buf(),
        };
        let mut manifest = if dir_of.join("Tauto.eure").exists() {
            match tauto::manifest::load(&dir_of) {
                Ok(m) => Some(m),
                Err(e) => {
                    eprintln!("{e}");
                    return ExitCode::FAILURE;
                }
            }
        } else {
            None
        };
        // A source file built on its own reads the `exports` of the tote that
        // holds it when no manifest sits beside it, as `tauto build --backend llvm` does.
        let enclosing = match (&tote_dir, &manifest) {
            (None, m) if m.as_ref().is_none_or(|m| m.exports.is_none()) => {
                tauto::manifest::enclosing_tote_dir(p)
            }
            _ => None,
        };
        if let Some(dir) = &enclosing {
            match tauto::manifest::load(dir) {
                // The tote that holds the file decides how the file is built:
                // its `rust` section (`main-thread`, `executor`, `stack-mb`, the
                // bridge) applies to the file as it does to the tote, so one
                // program is built the same way whichever way it is named.
                Ok(m) => match &mut manifest {
                    Some(own) => {
                        if m.exports.is_some() {
                            own.exports = m.exports;
                        }
                    }
                    None => {
                        manifest = Some(tauto::manifest::Manifest {
                            // The name is the bridge crate's (`<name>_bridge`)
                            // and the trust list approves the dependencies'
                            // externs, both as for the tote's own build.
                            package: tauto::manifest::Package {
                                name: m.package.name,
                                ..Default::default()
                            },
                            exports: m.exports,
                            rust: m.rust,
                            dependencies: m.dependencies,
                            trust_extern: m.trust_extern,
                            file: m.file,
                            ..Default::default()
                        })
                    }
                },
                Err(e) => {
                    eprintln!("{e}");
                    return ExitCode::FAILURE;
                }
            }
        }
        if !added_exports.is_empty() {
            match &mut manifest {
                Some(m) => m.exports.get_or_insert_with(Vec::new).extend(added_exports.clone()),
                None => {
                    manifest = Some(tauto::manifest::Manifest {
                        exports: Some(added_exports.clone()),
                        ..Default::default()
                    })
                }
            }
        }
        // A tote's crate is read back while nothing it was made from has
        // changed (`rust_cache`); `--emit` and `--explain-budget` say what
        // the front end finds, so they always run it.
        let cached = match (&tote_dir, &manifest) {
            (Some(d), Some(_)) if selected == "rust" && emit.is_none() && !explain_budget => {
                let own: Vec<String> = args
                    .iter()
                    .take_while(|a| *a != "--")
                    .filter(|a| !(*a == "--yes" || a.starts_with("--timings")))
                    .cloned()
                    .collect();
                super::rust_cache::lookup(d, &own)
            }
            _ => None,
        };
        let (lookup, kept) = match cached {
            Some((lookup, kept)) => (Some(lookup), kept),
            None => (None, None),
        };
        let mut loaded = None;
        // The kinds a run is asked for (`super::needed_kinds`).
        let needed: Vec<String>;
        let (mut ws, name, root, trusted) = 'front: {
            if let (Some(kept), Some(m)) = (kept, &manifest) {
                needed = kept.needed;
                let name = crate_name(&m.package.name);
                let root = match target_root(tote_dir.as_deref(), p) {
                    Ok(root) => root,
                    Err(error) => {
                        eprintln!("{}: {error}", p.display());
                        return ExitCode::FAILURE;
                    }
                };
                timings.phase("codegen");
                break 'front (
                    tauto_rustgen::Workspace { files: kept.files },
                    name,
                    root,
                    kept.trusted,
                );
            }
            let source = match (&tote_dir, &manifest) {
                (Some(d), Some(_)) => {
                    timings.phase("tote_load_check_extract");
                    tauto::program::load_tote_for_build(d).map(|program| {
                        timings.phase("parse_expand");
                        let source = program.source_text();
                        loaded = Some(program);
                        source
                    })
                }
                (Some(d), None) => Err(crate::i18n::t!(
                    "rust-no-manifest",
                    path = d.display().to_string()
                )),
                // A source file is read with its imports, checked and extracted as
                // `tauto run` reads it, so every backend runs the same checked program.
                (None, _)
                    if p.is_file()
                        && p.extension().is_some_and(|e| e == "taut" || e == "tauto") =>
                {
                    timings.phase("tote_load_check_extract");
                    match tauto::program::load_extracted_exporting(p, &added_exports) {
                        Ok(program) => {
                            timings.phase("parse_expand");
                            let source = program.source_text();
                            loaded = Some(program);
                            Ok(source)
                        }
                        Err(e) => {
                            eprintln!("{e}");
                            return ExitCode::FAILURE;
                        }
                    }
                }
                (None, _) => std::fs::read_to_string(&path).map_err(|e| format!("{path}: {e}")),
            };
            // The Rust that dependency totes bind their externs to; the
            // dependencies are read only after the tote has loaded.
            // A file is read with the tote that holds it, as the tote is.
            let holder = tote_dir.as_ref().or(enclosing.as_ref());
            if let (Some(d), Some(m), Ok(_)) = (holder, &mut manifest, &source)
                && let Err(e) = tauto::manifest::add_dependency_rust(m, d)
            {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
            let source = match source {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{e}");
                    return ExitCode::from(2);
                }
            };
            // Diagnostics and explicit qualified entries must also see library
            // functions that the program's top-level expression never calls.
            let library_entries = explain_budget
                || manifest
                    .as_ref()
                    .is_some_and(|m| !m.rust.nonresuming_entries.is_empty());
            let observe = |phase| {
                timings.phase(match phase {
                    tauto_nibcheck::lower::CompilePhase::ParseExpand => "parse_expand",
                    tauto_nibcheck::lower::CompilePhase::Check => "check",
                    tauto_nibcheck::lower::CompilePhase::Lower => "lower",
                })
            };
            // The `exports` entries, each `TOTE::*` read as the functions it
            // names; the manifest keeps those names from here on.
            // The entries named one by one: a `TOTE::*` brings the others.
            let named_exports: std::collections::BTreeSet<String> = manifest
                .as_ref()
                .and_then(|m| m.exports.as_ref())
                .map(|l| l.iter().filter(|e| !e.ends_with("::*")).cloned().collect())
                .unwrap_or_default();
            if let (Some(loaded), Some(m)) = (&loaded, &mut manifest)
                && let Some(list) = &m.exports
            {
                let totes = match tote_dir.as_ref().or(enclosing.as_ref()) {
                    Some(d) => match tauto::program::tote_dirs(d) {
                        Ok(t) => t,
                        Err(e) => {
                            eprintln!("{e}");
                            return ExitCode::FAILURE;
                        }
                    },
                    None => Vec::new(),
                };
                match tauto_nibcheck::lower::select_exports(loaded, list, &totes, None) {
                    Ok(selection) => {
                        for name in &selection.skipped {
                            eprintln!(
                                "{}",
                                crate::i18n::t!("rust-export-generic-skipped", path = &path, name = name)
                            );
                        }
                        m.exports = Some(selection.names.into_iter().collect());
                    }
                    Err(e) => {
                        eprintln!("{path}: {e}");
                        return ExitCode::FAILURE;
                    }
                }
            }
            let exports: Vec<String> = manifest
                .as_ref()
                .and_then(|m| m.exports.clone())
                .unwrap_or_default();
            let javascript_entries = manifest.as_ref().map(|m| {
                exports
                    .iter()
                    .chain(m.javascript.chunks.values().flatten())
                    .cloned()
                    .collect::<std::collections::BTreeSet<_>>()
            });
            let rust_entries: Option<std::collections::BTreeSet<String>> =
                Some(exports.iter().cloned().collect());
            let compiled = if let Some(loaded) = &loaded {
                tauto_nibcheck::lower::compile_loaded_entries_with_observer(
                    loaded,
                    if selected == "javascript" {
                        !exports.is_empty()
                            || manifest.as_ref().is_some_and(|m| !m.javascript.chunks.is_empty())
                    } else {
                        // The functions `exports` names are roots of the library, as
                        // for JavaScript and LLVM: they stay though nothing calls them.
                        library_entries || !exports.is_empty()
                    },
                    if selected == "javascript" {
                        tauto_nir::Target::JavaScript
                    } else {
                        tauto_nir::Target::Rust
                    },
                    if selected == "javascript" {
                        javascript_entries.as_ref()
                    } else if !exports.is_empty() {
                        rust_entries.as_ref()
                    } else {
                        None
                    },
                    observe,
                )
            } else if selected == "javascript" {
                tauto::nir::compile_javascript_with_observer(&source, observe)
            } else {
                tauto::nir::compile_with_observer(&source, library_entries, observe)
            };
            let mut package = match compiled {
                Ok(p) => p,
                Err(CompileError::Front(m) | CompileError::Package(m)) => {
                    let message = match &loaded {
                        Some(loaded) => super::locate_front(loaded, &path, &m),
                        None => super::locate(&path, &source, &m),
                    };
                    eprintln!("{message}");
                    return ExitCode::FAILURE;
                }
                Err(CompileError::Unsupported(u)) => {
                    let place = u
                        .span
                        .and_then(|span| {
                            let (file, line, col) = loaded.as_ref()?.locate(span.start)?;
                            Some(format!("{}:{line}:{col}", file.display()))
                        })
                        .unwrap_or_else(|| path.clone());
                    eprintln!(
                        "{}",
                        crate::i18n::t!(
                            "rust-unsupported",
                            place = &place,
                            backend = selected,
                            what = u.what.clone()
                        )
                    );
                    return ExitCode::FAILURE;
                }
                Err(e) => {
                    eprintln!("{path}: {e}");
                    return ExitCode::FAILURE;
                }
            };
            if selected != "javascript"
                && let Some(u) = package.rust_unsupported.take()
            {
                let place = u
                    .span
                    .and_then(|span| {
                        let (file, line, col) = loaded.as_ref()?.locate(span.start)?;
                        Some(format!("{}:{line}:{col}", file.display()))
                    })
                    .unwrap_or_else(|| path.clone());
                eprintln!(
                    "{}",
                    crate::i18n::t!(
                        "rust-unsupported",
                        place = &place,
                        backend = selected,
                        what = u.what.clone()
                    )
                );
                return ExitCode::FAILURE;
            }
            timings.phase("codegen");
            let name = match &manifest {
                Some(m) if tote_dir.is_some() => crate_name(&m.package.name),
                _ => crate_name(&path),
            };
            let root = match target_root(tote_dir.as_deref().filter(|_| manifest.is_some()), p) {
                Ok(root) => root,
                Err(error) => {
                    eprintln!("{}: {error}", p.display());
                    return ExitCode::FAILURE;
                }
            };
            needed = match &loaded {
                Some(l) if command == "run" => {
                    super::needed_permissions(l, &l.check_rows(tauto::rows::Target::Rust))
                }
                _ => package.permissions.clone(),
            };
            if selected == "javascript" {
                // A method's row holds only what the instance answers: a
                // function a `TOTE::*` brought with another effect is left out.
                let left_out: Vec<String> = package
                    .exports
                    .iter()
                    .filter(|e| !e.foreign_row.is_empty() && !named_exports.contains(&e.name))
                    .map(|e| e.name.clone())
                    .collect();
                for name in &left_out {
                    eprintln!(
                        "{}",
                        crate::i18n::t!("js-export-row-skipped", path = &path, name = name)
                    );
                }
                package.exports.retain(|e| !left_out.contains(&e.name));
                if let Some(m) = &mut manifest
                    && let Some(list) = &mut m.exports
                {
                    list.retain(|n| !left_out.contains(n));
                }
                let baked = if target == "node" {
                    match grant_flags(&path, &needed, &allow, yes, steps) {
                        Ok(flags) => flags,
                        Err(code) => return code,
                    }
                } else {
                    Vec::new()
                };
                return super::javascript::execute(
                    &root,
                    &package,
                    manifest.as_ref(),
                    command,
                    out_dir,
                    &name,
                    target,
                    declarations,
                    &mut timings,
                    &baked,
                    &program_args,
                );
            }
            let bridge = manifest.as_ref().and_then(|m| {
                m.rust
                    .bridge
                    .as_ref()
                    .map(|_| tauto_rustgen::bridge_ident(&m.package.name))
            });
            if library_entries || !exports.is_empty() {
                if manifest.as_ref().is_some_and(|m| m.exports.is_some()) {
                    package.exports.retain(|e| exports.contains(&e.name));
                }
            }
            let bindings = match tauto_rustgen::Bindings::resolve(
                &mut package,
                manifest.as_ref(),
                bridge.as_deref(),
            ) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("{path}: {e}");
                    return ExitCode::FAILURE;
                }
            };
            if explain_budget {
                for report in tauto_rustgen::budget_diagnostics(
                    &package,
                    &Sources {
                        file: &path,
                        text: &source,
                    },
                    &bindings,
                ) {
                    let at = source_location(&package, &path, &source, report.span);
                    if report.eligible() {
                        eprintln!(
                            "{}",
                            crate::i18n::t!(
                                "rust-budget-eligible",
                                at = &at,
                                budget = report.budget_id.to_string(),
                                function = report.function.to_string(),
                                variant = report.variant.to_string()
                            )
                        );
                        eprintln!("  {}", crate::i18n::t!("rust-budget-checks"));
                    } else {
                        eprintln!(
                            "{}",
                            crate::i18n::t!(
                                "rust-budget-ordinary",
                                at = &at,
                                budget = report.budget_id.to_string(),
                                function = report.function.to_string(),
                                variant = report.variant.to_string()
                            )
                        );
                    }
                    for assumption in &report.assumptions {
                        eprintln!(
                            "  {}",
                            crate::i18n::t!(
                                "rust-budget-assumption",
                                kind = assumption.kind.to_string(),
                                name = assumption.name.to_string(),
                                at = assumption.at.to_string(),
                                contract = assumption.contract.to_string()
                            )
                        );
                    }
                    for reason in report.reasons {
                        let at = source_location(&package, &path, &source, reason.span);
                        eprintln!(
                            "  [{}] {} at {at}: {}",
                            reason.code, reason.function, reason.message
                        );
                    }
                }
            }
            let mut opts = manifest
                .as_ref()
                .map(tauto_rustgen::Options::from_manifest)
                .unwrap_or_default();
            // The binary carries what it is allowed (`src/permissions.txt`,
            // written below), so it reads no `--allow-*` of its own.
            opts.baked_permissions = Some(Vec::new());
            if let Some(t) = &rust_target {
                // What the wasm32 targets lack: a blocking HTTP client.
                // They have no reactor either: each task runs to its end at its
                // `spawn` (`tauto_rt::exec::Inline`).
                let lacking = if package.permissions.iter().any(|p| p == "net") {
                    Some(crate::i18n::t!("rust-wasm-lacks-net"))
                } else {
                    None
                };
                if let Some(what) = lacking {
                    eprintln!(
                        "{}",
                        crate::i18n::t!("rust-target-lacks", path = &path, target = t, what = what)
                    );
                    return ExitCode::FAILURE;
                }
            }
            let ws = tauto_rustgen::workspace(
                &name,
                &package,
                &Sources {
                    file: &path,
                    text: &source,
                },
                &bindings,
                &opts,
            );
            // What `build` says of the trusted code, kept with the crate.
            let mut trusted = String::new();
            if !bindings.externs.is_empty() {
                trusted.push_str(&crate::i18n::t!("rust-trusted-code"));
                trusted.push('\n');
                for (n, b) in &bindings.externs {
                    trusted.push_str(&crate::i18n::t!(
                        "rust-trusted-extern",
                        name = n.to_string(),
                        rust = b.rust.to_string(),
                        at = b.at.to_string()
                    ));
                    trusted.push('\n');
                }
            }
            (ws, name, root, trusted)
        };
        // What the program is allowed is asked before the native build,
        // which takes minutes: a refusal or a missing terminal must not cost
        // it. It is fixed in the binary, for `build` as for `run`. A bench's
        // binary and an emitted crate are allowed nothing.
        let baked = if after_build.is_some() || emit.is_some() {
            Vec::new()
        } else {
            match grant_flags(&path, &needed, &allow, yes, steps) {
                Ok(flags) => flags,
                Err(code) => return code,
            }
        };
        if let Some(file) = ws.files.iter_mut().find(|(p, _)| p == "src/permissions.txt") {
            file.1 = baked.join("\n");
        }
        if command == "build" {
            eprint!("{trusted}");
        }
        if command == "build" && emit.is_some() {
            let dir = out_dir
                .map(PathBuf::from)
                .unwrap_or_else(|| root.join("emit").join(&name));
            timings.phase("write");
            match ws.write_with_stats(&dir) {
                Ok(stats) => timings.written(stats),
                Err(e) => {
                    eprintln!("{}: {e}", dir.display());
                    return ExitCode::from(2);
                }
            }
            timings.phase("finish");
            println!("{}", dir.display());
            return ExitCode::SUCCESS;
        }
        let dir = out_dir
            .map(PathBuf::from)
            .unwrap_or_else(|| root.join("ws").join(&name));
        // A tote's lock sits beside its `Tauto.eure`: `Cargo.lock`, or
        // `Tauto.Cargo.lock` where a `Cargo.toml` of another crate owns that
        // name (`docs/design/rust-backend.md`, `Cargo.lock`).
        let lock = tote_dir
            .as_ref()
            .filter(|_| manifest.is_some())
            .map(|directory| tauto_rustgen::Lock::beside(directory, update_lock));
        let lock_file = lock.as_ref().map(|l| l.file.display().to_string());
        let bin = match ws.build_with_observer(
            &name,
            &dir,
            &root.join("target"),
            release,
            rust_target.as_deref(),
            lock.as_ref(),
            |event| match event {
                BuildEvent::Write => timings.phase("write"),
                BuildEvent::Written(stats) => timings.written(stats),
                BuildEvent::NativeCompile => timings.phase("native_compile"),
                BuildEvent::LockCreated => eprintln!(
                    "{}",
                    crate::i18n::t!(
                        "rust-lock-created",
                        path = lock_file.clone().unwrap_or_default()
                    )
                ),
            },
        ) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
        };
        if let (Some(lookup), Some(loaded)) = (&lookup, &loaded) {
            super::rust_cache::keep(lookup, loaded, &ws.files, &trusted, &needed);
        }
        timings.phase("finish");
        if let Some(after_build) = after_build {
            return after_build(&bin);
        }
        if command == "build" {
            println!("{}", bin.display());
            return ExitCode::SUCCESS;
        }
        let mut child = std::process::Command::new(&bin);
        // A program that runs `tauto` (`proc_run`) runs this one.
        if let Ok(me) = std::env::current_exe() {
            child.env("TAUTO_EXE", me);
        }
        if let Some(n) = steps {
            child.env("TAUTO_STEP_LIMIT", n.to_string());
        }
        match child.args(&program_args).status() {
            Ok(s) => ExitCode::from(s.code().unwrap_or(1) as u8),
            Err(e) => {
                eprintln!("{}: {e}", bin.display());
                ExitCode::FAILURE
            }
        }
    })();
    timings.finish(result == ExitCode::SUCCESS);
    result
}

/// The flags of what the user allows the program (`run_prompt`), asked now.
///
/// `allow`, the flags given to `build`, are kept as given, and only the
/// kinds they leave are asked.
fn grant_flags(
    path: &str,
    needed: &[String],
    allow: &[String],
    yes: bool,
    steps: Option<u64>,
) -> Result<Vec<String>, ExitCode> {
    let given = match tauto_rt::permissions::Permissions::from_args(allow) {
        Ok((given, _)) => given,
        Err(e) => {
            eprintln!("{e}");
            return Err(ExitCode::from(2));
        }
    };
    let needed: Vec<&str> = needed
        .iter()
        .map(String::as_str)
        .filter(|k| !(steps.is_some() && *k == "div"))
        .filter(|k| given.missing([super::run_prompt::kind_of(k)]).len() == 1)
        .collect();
    let mut flags = allow.to_vec();
    if !needed.is_empty() {
        flags.extend(crate::run_prompt::flags(&super::grant(path, needed, yes)?));
    }
    Ok(flags)
}

fn source_location(
    package: &tauto_nir::Package,
    path: &str,
    source: &str,
    span: tauto_nir::Span,
) -> String {
    if let Some((file, line, col)) = package
        .sources
        .as_ref()
        .and_then(|map| map.locate(span.start))
    {
        format!("{}:{line}:{col}", file.display())
    } else {
        format!("{path}:{}", source_place(source, span))
    }
}

fn source_place(source: &str, span: tauto_nir::Span) -> String {
    if span.start >= tauto::surface::PRELUDE_BASE {
        return "prelude".into();
    }
    let offset = (span.start as usize).min(source.len());
    let before = &source[..offset];
    let line = before.bytes().filter(|b| *b == b'\n').count() + 1;
    let col = before
        .rsplit('\n')
        .next()
        .map_or(1, |line| line.chars().count() + 1);
    format!("{line}:{col}")
}

fn usage() -> ExitCode {
    eprintln!(
        "{}",
        crate::i18n::t!(
            "rust-usage",
            run = "tauto run --backend rust|javascript [--explain-budget] FILE",
            build = "tauto build [--allow-KIND[=…]…] [--yes] [--backend rust|javascript] [--emit rust|javascript] [--target node|browser|wasm32-wasip1|wasm32-unknown-unknown] [--declarations] [--explain-budget] [-o DIR] [--release] [--update-lock] [--timings[=json]] FILE"
        )
    );
    ExitCode::from(2)
}
