//! `tauto doc`: the source files as highlighted, linked HTML pages
//! (`docs/design/doc.md`). Which files and where they go is decided here; the
//! pages are written by the tote `doc` (`totes/doc`).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use tauto::program;

pub fn command(args: &[String]) -> ExitCode {
    if args == ["--help"] || args == ["-h"] {
        println!("{}", crate::i18n::t!("doc-help"));
        return ExitCode::SUCCESS;
    }
    let mut input = None;
    let mut output = None;
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "-o" if output.is_none() => match rest.next() {
                Some(value) if !value.starts_with('-') => output = Some(PathBuf::from(value)),
                _ => return usage(),
            },
            value if !value.starts_with('-') && input.is_none() => {
                input = Some(PathBuf::from(value))
            }
            _ => return usage(),
        }
    }
    let Some(input) = input else { return usage() };
    let output = output.unwrap_or_else(|| PathBuf::from("target/tauto/doc"));
    match generate(&input, &output) {
        Ok(code) => {
            println!("{}", output.join("index.html").display());
            code
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

fn usage() -> ExitCode {
    eprintln!("{}", crate::i18n::t!("doc-usage"));
    ExitCode::from(2)
}

fn generate(input: &Path, output: &Path) -> Result<ExitCode, String> {
    // Even an empty directory or dangling symlink belongs to the caller.
    match fs::symlink_metadata(output) {
        Ok(_) => {
            return Err(crate::i18n::t!(
                "doc-output-exists",
                path = output.display().to_string()
            ));
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(format!("{}: {e}", output.display())),
    }
    let package = if input.is_dir() {
        Some(input)
    } else if input.file_name().is_some_and(|n| n == "Tauto.eure") {
        Some(input.parent().unwrap_or(Path::new(".")))
    } else {
        None
    };
    let (root, files) = match package {
        Some(dir) => (
            dir.to_path_buf(),
            program::tote_sources(dir)?
                .into_iter()
                .filter(|p| tauto::program::is_source_file(p))
                .collect::<Vec<_>>(),
        ),
        None => (
            input
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or(Path::new("."))
                .to_path_buf(),
            vec![input.to_path_buf()],
        ),
    };
    // The tote writes each page at the source's path under the root, so only
    // the files under it (not the standard library or dependencies) are given.
    let root_abs = program::canonical_path(&root);
    let mut paths = Vec::new();
    for file in &files {
        let Ok(rel) = program::canonical_path(file)
            .strip_prefix(&root_abs)
            .map(Path::to_path_buf)
        else {
            continue;
        };
        if !rel
            .components()
            .all(|c| matches!(c, std::path::Component::Normal(_)))
        {
            continue;
        }
        let rel = rel
            .to_str()
            .ok_or_else(|| format!("{}: not UTF-8", file.display()))?
            .replace('\\', "/");
        paths.push(rel);
    }
    if paths.is_empty() {
        return Err(crate::i18n::t!("doc-no-sources"));
    }
    paths.sort();
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    fs::create_dir_all(parent).map_err(|e| format!("{}: {e}", parent.display()))?;
    fs::create_dir(output).map_err(|e| format!("{}: {e}", output.display()))?;
    let title = root_abs
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("doc")
        .to_string();
    let path_text = |p: &Path| -> Result<String, String> {
        p.to_str()
            .map(String::from)
            .ok_or_else(|| format!("{}: not UTF-8", p.display()))
    };
    // The tote reads under the root and writes under the output, nothing else.
    let mut args = vec![
        format!("--allow-read={}", path_text(&root)?),
        format!("--allow-write={}", path_text(output)?),
        "--allow-div".to_string(),
        "--".to_string(),
        path_text(output)?,
        path_text(&root)?,
        title,
    ];
    // The tokens inside each file's macros, as an editor colours them; a
    // file whose program does not expand has none and keeps the scanner's.
    let tokens: Vec<String> = paths
        .iter()
        .filter_map(|rel| dsl_argument(&root, rel))
        .collect();
    args.extend(paths);
    args.extend(tokens);
    Ok(tauto_cli_totes::main("doc", args).unwrap_or(ExitCode::FAILURE))
}

/// The argument giving the tote the tokens inside the macros of the file at
/// `rel` under `root` (`tauto_analyzer::editor::dsl_tokens`): the path, then
/// one line `START END KIND` per token, in bytes of the file.
fn dsl_argument(root: &Path, rel: &str) -> Option<String> {
    if rel.contains('\n') {
        return None;
    }
    let path = root.join(rel);
    let text = fs::read_to_string(&path).ok()?;
    let (tokens, _) = tauto_analyzer::editor::dsl_tokens(&path, &text).ok()?;
    if tokens.is_empty() {
        return None;
    }
    let mut arg = rel.to_string();
    for t in tokens {
        arg.push_str(&format!("\n{} {} {}", t.start, t.end, t.kind));
    }
    Some(arg)
}
