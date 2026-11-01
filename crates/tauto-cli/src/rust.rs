//! `tauto run --backend rust FILE` and `tauto build [--emit rust] FILE
//! [-o DIR]`.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use tauto_nir::CompileError;
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
/// was started (like the macro cache). A lone source file without a tote
/// keeps `target/tauto` under the current directory.
fn target_root(tote_dir: Option<&Path>) -> PathBuf {
    std::env::var_os("TAUTO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| tote_dir.unwrap_or(Path::new("")).join("target/tauto"))
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
    let mut target = None;
    let mut declarations = false;
    let mut timing_format = None;
    let mut explain_budget = false;
    let (mut backend, mut emit, mut out_dir, mut release) = (None, None, None, false);
    // What `run` passes to the program: its permission flags, then `--` and
    // its arguments (`docs/design/host-effects.md`).
    let mut run_args = Vec::new();
    let mut rest = args[1..].iter();
    while let Some(a) = rest.next() {
        match a.as_str() {
            a if command == "run" && (a == "-A" || a.starts_with("--allow-")) => {
                run_args.push(a.to_string());
            }
            "--" if command == "run" => {
                run_args.push("--".to_string());
                run_args.extend(rest.by_ref().cloned());
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
            f if f.starts_with('-') => return usage(),
            p if path.is_none() => path = Some(p.to_string()),
            _ => return usage(),
        }
    }
    let Some(path) = path else {
        return usage();
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
        let mut loaded = None;
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
                if p.is_file() && p.extension().is_some_and(|e| e == "taut" || e == "tauto") =>
            {
                timings.phase("tote_load_check_extract");
                match tauto::program::load_extracted(p) {
                    Ok(program) => {
                        timings.phase("parse_expand");
                        let source = program.source_text();
                        loaded = Some(program);
                        Ok(source)
                    }
                    // A program that does not check fails as a front-end error.
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
        if let (Some(d), Some(m), Ok(_)) = (&tote_dir, &mut manifest, &source)
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
                tauto_nir::CompilePhase::ParseExpand => "parse_expand",
                tauto_nir::CompilePhase::Check => "check",
                tauto_nir::CompilePhase::Lower => "lower",
            })
        };
        let compiled = if let Some(loaded) = &loaded {
            tauto_nir::compile_loaded_with_observer(
                loaded,
                if selected == "javascript" {
                    manifest.as_ref().is_some_and(|m| {
                        !m.javascript.exports.is_empty() || !m.javascript.chunks.is_empty()
                    })
                } else {
                    library_entries
                },
                selected == "javascript",
                observe,
            )
        } else if selected == "javascript" {
            tauto_nir::compile_javascript_with_observer(&source, observe)
        } else {
            tauto_nir::compile_with_observer(&source, library_entries, observe)
        };
        let mut package = match compiled {
            Ok(p) => p,
            Err(CompileError::Front(m)) => {
                let message = match &loaded {
                    Some(loaded) => super::locate_in(loaded, &path, &m),
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
                        what = u.what.to_string()
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
                    what = u.what.to_string()
                )
            );
            return ExitCode::FAILURE;
        }
        timings.phase("codegen");
        let name = match &manifest {
            Some(m) if tote_dir.is_some() => crate_name(&m.package.name),
            _ => crate_name(&path),
        };
        let root = target_root(tote_dir.as_deref().filter(|_| manifest.is_some()));
        if selected == "javascript" {
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
                &run_args,
            );
        }
        let bridge = manifest.as_ref().and_then(|m| {
            m.rust
                .bridge
                .as_ref()
                .map(|_| format!("{}_bridge", m.package.name.replace('-', "_")))
        });
        if library_entries {
            if let Some(exports) = manifest.as_ref().and_then(|m| m.rust.exports.as_ref()) {
                let mut seen = std::collections::BTreeSet::new();
                for name in exports {
                    if !seen.insert(name.clone()) {
                        eprintln!(
                            "{}",
                            crate::i18n::t!("rust-exports-duplicate", path = &path, name = name)
                        );
                        return ExitCode::FAILURE;
                    }
                    if !package.exports.iter().any(|e| &e.name == name) {
                        eprintln!(
                            "{}",
                            crate::i18n::t!("rust-exports-unknown", path = &path, name = name)
                        );
                        return ExitCode::FAILURE;
                    }
                }
                package.exports.retain(|e| seen.contains(&e.name));
            }
        }
        let bindings = match tauto_rustgen::Bindings::resolve(
            &package,
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
        let opts = manifest
            .as_ref()
            .map(tauto_rustgen::Options::from_manifest)
            .unwrap_or_default();
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
        if command == "build" && !bindings.externs.is_empty() {
            // The Rust the build trusts.
            eprintln!("{}", crate::i18n::t!("rust-trusted-code"));
            for (n, b) in &bindings.externs {
                eprintln!(
                    "{}",
                    crate::i18n::t!(
                        "rust-trusted-extern",
                        name = n.to_string(),
                        rust = b.rust.to_string(),
                        at = b.at.to_string()
                    )
                );
            }
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
        let bin = match ws.build_with_observer(
            &name,
            &dir,
            &root.join("target"),
            release,
            rust_target.as_deref(),
            |event| match event {
                BuildEvent::Write => timings.phase("write"),
                BuildEvent::Written(stats) => timings.written(stats),
                BuildEvent::NativeCompile => timings.phase("native_compile"),
            },
        ) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::FAILURE;
            }
        };
        timings.phase("finish");
        if let Some(after_build) = after_build {
            return after_build(&bin);
        }
        if command == "build" {
            println!("{}", bin.display());
            return ExitCode::SUCCESS;
        }
        match std::process::Command::new(&bin).args(&run_args).status() {
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
            build = "tauto build [--backend rust|javascript] [--emit rust|javascript] [--target node|browser|wasm32-wasip1|wasm32-unknown-unknown] [--declarations] [--explain-budget] [-o DIR] [--release] [--timings[=json]] FILE"
        )
    );
    ExitCode::from(2)
}
