//! Creates a local tote without running its code or resolving dependencies.
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;

use crate::i18n;

const SOURCE: &str = "perform show(\"hello\", 42)\n";

pub fn command(args: &[String]) -> ExitCode {
    if args == ["--help"] || args == ["-h"] {
        println!("{}", i18n::t!("init-help"));
        return ExitCode::SUCCESS;
    }
    let path = match args {
        [] => ".",
        [path] if !path.starts_with('-') => path.as_str(),
        _ => return usage(),
    };
    match initialize(Path::new(path)) {
        Ok(root) => {
            println!(
                "{}",
                i18n::t!(
                    "init-created",
                    path = root.join("Tauto.eure").display().to_string()
                )
            );
            println!("{}", i18n::t!("init-run-hint"));
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{}", i18n::t!("init-failed", error = error));
            ExitCode::FAILURE
        }
    }
}

fn usage() -> ExitCode {
    eprintln!("{}", i18n::t!("init-help"));
    ExitCode::from(2)
}

fn valid_name(name: &str) -> bool {
    name.starts_with(|c: char| c.is_ascii_lowercase())
        && name
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
}

fn directory(path: &Path) -> Result<bool, String> {
    match fs::symlink_metadata(path) {
        Ok(meta) if meta.is_dir() && !meta.file_type().is_symlink() => Ok(true),
        Ok(_) => Err(i18n::t!(
            "init-not-plain-directory",
            path = path.display().to_string()
        )),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(e) => Err(format!("{}: {e}", path.display())),
    }
}

fn initialize(path: &Path) -> Result<PathBuf, String> {
    if path.as_os_str().is_empty() || path.components().any(|c| c == Component::ParentDir) {
        return Err(i18n::t!("init-bad-path"));
    }
    let root = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map_err(|e| e.to_string())?
            .join(path)
    };
    // Check each existing component rather than following a directory symlink.
    let mut prefix = PathBuf::new();
    for component in root.components() {
        prefix.push(component);
        if prefix != root && !directory(&prefix)? {
            return Err(i18n::t!(
                "init-parent-missing",
                path = prefix.display().to_string()
            ));
        }
    }
    let root_exists = directory(&root)?;
    let resolved = if root_exists {
        fs::canonicalize(&root).map_err(|e| e.to_string())?
    } else {
        root.clone()
    };
    let name = resolved
        .file_name()
        .and_then(|s| s.to_str())
        .ok_or_else(|| i18n::t!("init-no-name"))?;
    if !valid_name(name) {
        return Err(i18n::t!("init-bad-name"));
    }
    let src = root.join("src");
    let src_exists = directory(&src)?;
    let files = [root.join("Tauto.eure"), src.join("main.taut")];
    for file in &files {
        match fs::symlink_metadata(file) {
            Ok(_) => {
                return Err(i18n::t!(
                    "init-refuse-overwrite",
                    path = file.display().to_string()
                ));
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(format!("{}: {e}", file.display())),
        }
    }
    let manifest = format!(
        "package {{\n  name = \"{name}\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}}\n"
    );
    let mut made_dirs = Vec::new();
    let mut made_files = Vec::new();
    let result = (|| -> std::io::Result<()> {
        for (dir, exists) in [(&root, root_exists), (&src, src_exists)] {
            if !exists {
                fs::create_dir(dir)?;
                made_dirs.push(dir);
            }
        }
        for (file, content) in files.iter().zip([manifest.as_str(), SOURCE]) {
            let mut out = OpenOptions::new().write(true).create_new(true).open(file)?;
            made_files.push(file);
            out.write_all(content.as_bytes())?;
        }
        Ok(())
    })();
    if let Err(error) = result {
        let mut cleanup = Vec::new();
        for file in made_files.into_iter().rev() {
            if let Err(e) = fs::remove_file(file) {
                cleanup.push(format!("{}: {e}", file.display()));
            }
        }
        for dir in made_dirs.into_iter().rev() {
            if let Err(e) = fs::remove_dir(dir) {
                cleanup.push(format!("{}: {e}", dir.display()));
            }
        }
        return Err(if cleanup.is_empty() {
            error.to_string()
        } else {
            i18n::t!(
                "init-cleanup-failed",
                error = error.to_string(),
                paths = cleanup.join(", ")
            )
        });
    }
    Ok(root)
}
