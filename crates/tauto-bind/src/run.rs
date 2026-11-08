//! `tauto bind CRATE [--config FILE] [--check]`.

use std::path::{Path, PathBuf};
use std::process::Command;

use tauto_message::msg;

use crate::config::Config;
use crate::generate::{Output, generate};

/// The `tauto bind` command; returns the process exit code.
pub fn command(args: &[String]) -> i32 {
    let mut krate = None;
    let mut config = None;
    let mut check = false;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--check" => check = true,
            "--config" => config = it.next().cloned(),
            other if krate.is_none() && !other.starts_with('-') => krate = Some(other.to_string()),
            other => {
                eprintln!("{}", msg!("bind-unexpected", arg = other));
                return 2;
            }
        }
    }
    let Some(krate) = krate else {
        eprintln!(
            "{}",
            msg!(
                "bind-usage",
                usage = "tauto bind CRATE [--config bind/CRATE.config.eure] [--check]"
            )
        );
        return 2;
    };
    match bind(Path::new("."), &krate, config.as_deref(), check) {
        Ok(true) => 0,
        Ok(false) => 1,
        Err(e) => {
            eprintln!("{e}");
            1
        }
    }
}

/// Binds `krate` for the tote at `tote`. With `check`, writes nothing and
/// returns `false` when the files differ from what the config generates.
pub fn bind(tote: &Path, krate: &str, config: Option<&str>, check: bool) -> Result<bool, String> {
    let config_rel = config
        .map(str::to_string)
        .unwrap_or_else(|| format!("bind/{krate}.config.eure"));
    let config_path = tote.join(&config_rel);
    let text = std::fs::read_to_string(&config_path)
        .map_err(|e| format!("{}: {e}", config_path.display()))?;
    let cfg = Config::parse(&text, &config_rel)?;
    if cfg.crate_name != krate {
        return Err(msg!(
            "bind-crate-mismatch",
            file = &config_rel,
            found = &cfg.crate_name,
            wanted = krate
        )
        .to_string());
    }
    let json = rustdoc_json(tote, &cfg)?;
    let parsed: serde_json::Value =
        serde_json::from_str(&json).map_err(|e| format!("rustdoc JSON: {e}"))?;
    let format = parsed
        .get("format_version")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    if format != u64::from(crate::FORMAT_VERSION) {
        return Err(msg!(
            "bind-format-version",
            found = format,
            wanted = crate::FORMAT_VERSION
        )
        .to_string());
    }
    let doc: rustdoc_types::Crate =
        serde_json::from_value(parsed).map_err(|e| format!("rustdoc JSON: {e}"))?;
    let out = generate(&doc, &cfg, &config_rel);
    write_or_check(tote, krate, &out, check)
}

fn write_or_check(tote: &Path, krate: &str, out: &Output, check: bool) -> Result<bool, String> {
    let preferred = format!("bind/{krate}.taut");
    let legacy = format!("bind/{krate}.tauto");
    let source = if !tote.join(&preferred).exists() && tote.join(&legacy).is_file() {
        legacy
    } else {
        preferred
    };
    let files = [
        (source, &out.tauto),
        (format!("bind/{krate}.eure"), &out.eure),
        (format!("bind/{krate}.report.md"), &out.report),
    ];
    if check {
        let mut ok = true;
        for (rel, want) in &files {
            let have = std::fs::read_to_string(tote.join(rel)).unwrap_or_default();
            if &have != *want {
                eprintln!(
                    "{}",
                    msg!(
                        "bind-out-of-date",
                        file = rel,
                        command = format!("tauto bind {krate} --config bind/{krate}.config.eure")
                    )
                );
                ok = false;
            }
        }
        return Ok(ok);
    }
    std::fs::create_dir_all(tote.join("bind")).map_err(|e| e.to_string())?;
    for (rel, text) in &files {
        std::fs::write(tote.join(rel), text).map_err(|e| format!("{rel}: {e}"))?;
    }
    Ok(true)
}

/// A scratch workspace that depends on the crate alone, and the rustdoc JSON
/// of the crate built there.
fn rustdoc_json(tote: &Path, cfg: &Config) -> Result<String, String> {
    let ws = tote
        .join("target/tauto")
        .join(format!("bind-{}", cfg.crate_name));
    std::fs::create_dir_all(ws.join("src")).map_err(|e| e.to_string())?;
    let dependency = dependency_line(tote, &cfg.crate_name)?;
    let manifest = format!(
        "[package]\nname = \"tauto-bind-{}\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n[workspace]\n\n[dependencies]\n{} = {}\n",
        cfg.crate_name, cfg.crate_name, dependency
    );
    std::fs::write(ws.join("Cargo.toml"), manifest).map_err(|e| e.to_string())?;
    std::fs::write(ws.join("src/lib.rs"), "").map_err(|e| e.to_string())?;
    let lock = tote.join("Cargo.lock");
    let locked = lock.exists();
    if locked {
        std::fs::copy(&lock, ws.join("Cargo.lock")).map_err(|e| e.to_string())?;
    }
    let mut cmd = Command::new("cargo");
    // The toolchain of `rust-toolchain.toml` is a nightly; the JSON output of
    // rustdoc is unstable on any other.
    cmd.current_dir(&ws)
        .env("RUSTC_BOOTSTRAP", "1")
        .env_remove("CARGO_TARGET_DIR")
        .args(["rustdoc", "-p", &cfg.crate_name]);
    if locked {
        cmd.arg("--locked");
    }
    cmd.args(["--", "-Z", "unstable-options", "--output-format", "json"]);
    let out = cmd.output().map_err(|e| format!("cargo: {e}"))?;
    if !out.status.success() {
        return Err(msg!(
            "bind-rustdoc-failed",
            stderr = String::from_utf8_lossy(&out.stderr).into_owned()
        )
        .to_string());
    }
    let file = ws
        .join("target/doc")
        .join(format!("{}.json", cfg.crate_name.replace('-', "_")));
    std::fs::read_to_string(&file).map_err(|e| format!("{}: {e}", file.display()))
}

/// The right-hand side of the crate's line in `[dependencies]`: from
/// `rust.dependencies` of the tote's `Tauto.eure`, or any version.
fn dependency_line(tote: &Path, name: &str) -> Result<String, String> {
    let file: PathBuf = tote.join("Tauto.eure");
    let text = match std::fs::read_to_string(&file) {
        Ok(text) => text,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok("\"*\"".into()),
        Err(e) => return Err(format!("{}: {e}", file.display())),
    };
    manifest_dependency(&text, &file.display().to_string(), name)
}

fn manifest_dependency(text: &str, file: &str, name: &str) -> Result<String, String> {
    use eure_document::document::node::NodeValue;
    use eure_document::value::PrimitiveValue as P;

    let doc = eure_reader::parse_to_document(text, file).map_err(|e| format!("{file}: {e}"))?;
    let child = |id, key: &str| match &doc.node(id).content {
        NodeValue::Map(m) => Ok(m.get_node_id(&key.into())),
        NodeValue::Hole(_) => Ok(None),
        _ => Err(msg!("bind-expected-block-containing", file = file, key = key).to_string()),
    };
    let mut id = doc.get_root_id();
    for key in ["rust", "dependencies", name] {
        let Some(next) = child(id, key)? else {
            return Ok("\"*\"".into());
        };
        id = next;
    }
    let quoted = |s: &str| serde_json::to_string(s).expect("serializing a string");
    match &doc.node(id).content {
        NodeValue::Primitive(P::Text(t)) => Ok(quoted(t.as_str())),
        NodeValue::Map(fields) => {
            let mut parts = Vec::new();
            for (key, id) in fields.iter() {
                let value = match &doc.node(*id).content {
                    NodeValue::Primitive(P::Text(t)) => quoted(t.as_str()),
                    NodeValue::Primitive(P::Bool(b)) => b.to_string(),
                    NodeValue::Array(items) => {
                        let values = items
                            .iter()
                            .map(|id| match &doc.node(*id).content {
                                NodeValue::Primitive(P::Text(t)) => Ok(quoted(t.as_str())),
                                _ => Err(msg!(
                                    "bind-dependency-texts",
                                    file = file,
                                    path = format!("rust.dependencies.{name}.{key}")
                                )
                                .to_string()),
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        format!("[{}]", values.join(", "))
                    }
                    _ => {
                        return Err(msg!(
                            "bind-dependency-unsupported",
                            file = file,
                            path = format!("rust.dependencies.{name}.{key}")
                        )
                        .to_string());
                    }
                };
                parts.push(format!("{key} = {value}"));
            }
            Ok(format!("{{ {} }}", parts.join(", ")))
        }
        _ => Err(msg!(
            "bind-dependency-version",
            file = file,
            path = format!("rust.dependencies.{name}")
        )
        .to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bindings_use_taut_by_default_and_preserve_existing_source_extensions() {
        let root = std::env::temp_dir().join(format!(
            "tauto-bind-extensions-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
        ));
        let output = Output {
            tauto: r#"fn value(): i64 { 1 }"#.to_string(),
            eure: String::new(),
            report: String::new(),
            unbound: Vec::new(),
        };
        for existing in [None, Some("taut"), Some("tauto")] {
            let dir = root.join(existing.unwrap_or("new"));
            std::fs::create_dir_all(dir.join("bind")).unwrap();
            if let Some(extension) = existing {
                std::fs::write(dir.join(format!("bind/demo.{extension}")), "old").unwrap();
            }
            assert!(write_or_check(&dir, "demo", &output, false).unwrap());
            let extension = existing.unwrap_or("taut");
            assert_eq!(
                std::fs::read_to_string(dir.join(format!("bind/demo.{extension}"))).unwrap(),
                output.tauto,
            );
            let other = if extension == "taut" { "tauto" } else { "taut" };
            assert!(!dir.join(format!("bind/demo.{other}")).exists());
            assert!(write_or_check(&dir, "demo", &output, true).unwrap());
        }
        std::fs::remove_dir_all(root).unwrap();
    }

    fn dependency(text: &str) -> Result<String, String> {
        manifest_dependency(text, "Tauto.eure", "regex")
    }

    #[test]
    fn dependency_version_is_independent_of_formatting() {
        for text in [
            "rust { dependencies { regex = \"=1.12.3\" } }",
            "rust {\n dependencies {\n regex = \"=1.12.3\" // pinned\n }\n }",
        ] {
            assert_eq!(dependency(text).unwrap(), "\"=1.12.3\"");
        }
    }

    #[test]
    fn only_rust_dependencies_are_selected() {
        assert_eq!(dependency("dependencies { regex { path = \"../regex\" } }\nrust { dependencies { regex = \"=1.12.3\" } }").unwrap(), "\"=1.12.3\"");
        assert_eq!(
            dependency("dependencies { regex = \"other\" }").unwrap(),
            "\"*\""
        );
    }

    #[test]
    fn dependency_blocks_preserve_cargo_options() {
        let value = dependency("rust { dependencies { regex { version = \"=1.12.3\" default-features = false features = [\"std\", \"unicode\"] } } }").unwrap();
        assert!(value.contains("\"version\" = \"=1.12.3\""), "{value}");
        assert!(value.contains("\"default-features\" = false"), "{value}");
        assert!(
            value.contains("\"features\" = [\"std\", \"unicode\"]"),
            "{value}"
        );
    }

    #[test]
    fn malformed_dependencies_are_errors() {
        for text in [
            "rust = false",
            "rust { dependencies = false }",
            "rust { dependencies { regex = false } }",
            "rust { dependencies { regex { version = 123 } } }",
            "rust { dependencies { regex { features = [true] } } }",
        ] {
            assert!(dependency(text).is_err(), "{text}");
        }
    }

    #[test]
    fn absent_dependency_uses_the_default() {
        for text in [
            "",
            "package { name = \"demo\" }",
            "rust { dependencies {} }",
        ] {
            assert_eq!(dependency(text).unwrap(), "\"*\"");
        }
    }
}
