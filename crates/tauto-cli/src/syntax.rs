//! `tauto syntax gen`, `show` and `source`: the
//! tables of a tote's `syntax` declarations, in
//! `DIR/.tauto-syntax/<sha256>.tables`.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};

use tauto::surface::{Stmt, parse_program_unresolved_at};
use tauto::syntax::{grammar_sha, load_tables, table_path, types_text, with_search_dirs};

/// The host's step limit for the generator, high enough for a grammar as
/// large as `crates/tauto-parol/tauto.par`.
const GENERATOR_STEPS: &str = "200000000000";

pub fn command(args: &[String]) -> ExitCode {
    match args.first().map(String::as_str) {
        Some("gen") => {
            let flag = args.get(1).map(String::as_str);
            let check = flag == Some("--check");
            let force = flag == Some("--force");
            let index = 1 + usize::from(check || force);
            if args.len() > index + 1 || args.get(index).is_some_and(|a| a.starts_with('-')) {
                return usage();
            }
            let dir = args.get(index).map_or(".", String::as_str);
            gen_tables(Path::new(dir), check, force)
        }
        Some("source") if args.len() == 3 => source(Path::new(&args[1]), &args[2]),
        Some("show") => match (args.get(1), args.get(2)) {
            (Some(dir), Some(name)) => show(Path::new(dir), name),
            _ => usage(),
        },
        _ => usage(),
    }
}

const USAGE: &str = "tauto syntax gen [--check | --force] [DIR]\n       \
                     tauto syntax show DIR NAME\n       \
                     tauto syntax source DIR NAME";

fn usage() -> ExitCode {
    eprintln!("{}", crate::i18n::t!("syntax-usage", usage = USAGE));
    ExitCode::from(2)
}

struct Declared {
    name: String,
    grammar: String,
    file: PathBuf,
}

fn sources(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if path.is_dir() {
            if !name.starts_with('.') && name != "target" {
                sources(&path, out)?;
            }
        } else if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("taut" | "tauto" | "nib")
        ) {
            out.push(path);
        }
    }
    out.sort();
    Ok(())
}

fn declared(dir: &Path) -> Result<Vec<Declared>, String> {
    let files = if dir.join("Tauto.eure").exists() {
        tauto::program::package_source_files(dir)?
    } else {
        // Standalone source directories do not have a package manifest.
        let mut files = Vec::new();
        sources(dir, &mut files).map_err(|e| format!("{}: {e}", dir.display()))?;
        files
    };
    let mut out = Vec::new();
    for file in files {
        let text =
            std::fs::read_to_string(&file).map_err(|e| format!("{}: {e}", file.display()))?;
        if !text.contains("syntax") {
            continue;
        }
        let program = parse_program_unresolved_at(&text, 0)
            .map_err(|e| format!("{}: {e}", file.display()))?;
        for stmt in program.stmts {
            if let Stmt::Syntax { name, grammar, .. } = stmt {
                out.push(Declared {
                    name,
                    grammar: grammar.text,
                    file: file.clone(),
                });
            }
        }
    }
    Ok(out)
}

/// Whether the tables at `path` were made by the current generator. Unreadable tables are not.
fn is_current(path: &Path) -> bool {
    std::fs::read_to_string(path)
        .ok()
        .is_some_and(|t| tauto::syntax::tables_text_is_current(&t))
}

/// The directory whose `.tauto-syntax` holds the tables of `d`.
fn tables_dir(root: &Path, d: &Declared) -> PathBuf {
    match d.file.parent() {
        Some(p) if p.starts_with(root) => p.to_path_buf(),
        _ => root.to_path_buf(),
    }
}

fn gen_tables(dir: &Path, check: bool, force: bool) -> ExitCode {
    let found = match declared(dir) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    // The tables of a declaration are in the `.tauto-syntax` of the directory
    // of the file that declares it: that is where the reader looks first, and
    // a tote's subdirectory keeps its own.
    // A grammar with several start symbols (`%start A, B`) has tables for each.
    let wanted: BTreeMap<(PathBuf, String), (&Declared, Option<String>)> = found
        .iter()
        .flat_map(|d| {
            let sha = grammar_sha(&d.grammar);
            let others = tauto::syntax::start_symbols(&d.grammar).into_iter().skip(1);
            std::iter::once(None)
                .chain(others.map(Some))
                .map(move |start| {
                    let key = tauto::syntax::tables_key(&sha, start.as_deref());
                    ((tables_dir(dir, d), key), (d, start))
                })
                .collect::<Vec<_>>()
        })
        .collect();
    let mut stale = false;
    for ((table_dir, key), (d, start)) in &wanted {
        let tables = table_dir.join(".tauto-syntax");
        let path = table_path(table_dir, key);
        if path.is_file() && !force && is_current(&path) {
            continue;
        }
        if check {
            eprintln!(
                "{}",
                crate::i18n::t!(
                    "syntax-tables-missing",
                    file = d.file.display().to_string(),
                    name = &d.name
                )
            );
            stale = true;
            continue;
        }
        match generate(&d.grammar, start.as_deref()) {
            Ok(text) => {
                if let Err(e) =
                    std::fs::create_dir_all(&tables).and_then(|()| std::fs::write(&path, text))
                {
                    eprintln!("{}: {e}", path.display());
                    return ExitCode::from(2);
                }
                println!(
                    "{}",
                    crate::i18n::t!("syntax-wrote", path = path.display().to_string())
                );
            }
            Err(e) => {
                eprintln!("{}: syntax {}: {e}", d.file.display(), d.name);
                return ExitCode::FAILURE;
            }
        }
    }
    // Tables no declaration asks for any more.
    let mut table_dirs: Vec<PathBuf> = wanted.keys().map(|(d, _)| d.clone()).collect();
    table_dirs.push(dir.to_path_buf());
    table_dirs.sort();
    table_dirs.dedup();
    for table_dir in table_dirs {
        let Ok(entries) = std::fs::read_dir(table_dir.join(".tauto-syntax")) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let sha = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
            if path.extension().is_some_and(|e| e == "tables")
                && !wanted.contains_key(&(table_dir.clone(), sha.to_string()))
            {
                if check {
                    eprintln!(
                        "{}",
                        crate::i18n::t!("syntax-tables-unused", path = path.display().to_string())
                    );
                    stale = true;
                } else if std::fs::remove_file(&path).is_ok() {
                    println!(
                        "{}",
                        crate::i18n::t!("syntax-removed", path = path.display().to_string())
                    );
                }
            }
        }
    }
    if stale {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Runs the generator: the tote `totes/syntaxgen`, compiled into this
/// executable when it was built (`tauto-cli-totes`), as `tauto
/// --tote-main syntaxgen --allow-read=FILE -- --gen FILE`. It reads the grammar from `FILE` and writes the table file on standard
/// output. The grammar goes through a file of its own, not standard input:
/// the generator hashes the exact bytes it reads, and the read permission it
/// is given covers that one file and nothing else.
/// `start` is a start symbol other than the first, the tables are made for (`--start`).
fn generate(grammar: &str, start: Option<&str>) -> Result<String, String> {
    let program = std::env::current_exe()
        .map_err(|e| crate::i18n::t!("syntax-cannot-run-generator", error = e.to_string()))?;
    let input = GrammarFile::new(grammar)?;
    let file = input
        .path
        .to_str()
        .ok_or_else(|| crate::i18n::t!("syntax-temp-not-utf8"))?;
    let mut command = Command::new(program);
    command.args([
        crate::tote_main::TOTE_FLAG,
        "syntaxgen",
        &format!("--allow-read={file}"),
        "--",
        "--gen",
        file,
    ]);
    if let Some(start) = start {
        command.args(["--start", start]);
    }
    if std::env::var_os("TAUTO_STEP_LIMIT").is_none() {
        command.env("TAUTO_STEP_LIMIT", GENERATOR_STEPS);
    }
    let out = command
        .stdin(Stdio::null())
        .output()
        .map_err(|e| crate::i18n::t!("syntax-cannot-run-generator", error = e.to_string()))?;
    if out.status.success() {
        String::from_utf8(out.stdout).map_err(|e| e.to_string())
    } else {
        Err(String::from_utf8_lossy(&out.stderr).trim().to_string())
    }
}

/// The grammar written to `grammar` in a directory made for it alone,
/// removed when dropped.
struct GrammarFile {
    dir: PathBuf,
    path: PathBuf,
}

impl GrammarFile {
    fn new(grammar: &str) -> Result<GrammarFile, String> {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let dir = std::env::temp_dir().join(format!(
            "tauto-syntax-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        // `create_dir` fails on a directory already there, so nobody else's
        // file is read in place of the grammar.
        std::fs::create_dir(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        let file = GrammarFile {
            path: dir.join("grammar"),
            dir,
        };
        std::fs::File::create_new(&file.path)
            .and_then(|mut f| f.write_all(grammar.as_bytes()))
            .map_err(|e| format!("{}: {e}", file.path.display()))?;
        Ok(file)
    }
}

impl Drop for GrammarFile {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

fn show(dir: &Path, name: &str) -> ExitCode {
    let found = match declared(dir) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    let Some(d) = found.iter().find(|d| d.name == name) else {
        eprintln!(
            "{}",
            crate::i18n::t!(
                "syntax-not-found",
                name = name,
                dir = dir.display().to_string()
            )
        );
        return ExitCode::from(2);
    };
    match with_search_dirs(vec![dir.to_path_buf()], || load_tables(&d.grammar)) {
        Ok(tables) => {
            print!("{}", types_text(name, &tables));
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!(
                "{}",
                crate::i18n::t!(
                    "syntax-error-in",
                    name = name.to_string(),
                    error = e.to_string()
                )
            );
            ExitCode::FAILURE
        }
    }
}

/// The original grammar text, not a reconstruction from the parse tables.
/// This lets the bootstrap parser and the declared parser share one source.
fn source(dir: &Path, name: &str) -> ExitCode {
    let found = match declared(dir) {
        Ok(found) => found,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::from(2);
        }
    };
    let mut matching = found.iter().filter(|decl| decl.name == name);
    let Some(decl) = matching.next() else {
        eprintln!(
            "{}",
            crate::i18n::t!(
                "syntax-not-found",
                name = name,
                dir = dir.display().to_string()
            )
        );
        return ExitCode::from(2);
    };
    if matching.next().is_some() {
        eprintln!(
            "{}",
            crate::i18n::t!(
                "syntax-ambiguous",
                name = name,
                dir = dir.display().to_string()
            )
        );
        return ExitCode::from(2);
    }
    print!("{}", decl.grammar);
    ExitCode::SUCCESS
}
