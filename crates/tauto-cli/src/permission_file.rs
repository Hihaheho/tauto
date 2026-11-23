//! `trust.run` of a project's `Tauto.eure`: the paths, variables and hosts
//! `tauto run` of its programs is narrowed to (`docs/design/host-effects.md`).
//!
//! ```eure
//! trust {
//!   run {
//!     read = ["data", "/etc/hosts"]
//!     write = ["out"]
//!     env = ["HOME"]
//!     net = ["api.example.com", "localhost:8080"]
//!     interactive = true
//!   }
//! }
//! ```
//!
//! Each key is read into the grant it stands for (`net = ["a", "b"]` only
//! those hosts, `net = true` every host); a kind written here is not asked
//! at the start of a run, since it was approved with the rest of `trust`.
//! `interactive = true` asks the rest of the user when the program reaches
//! it, at the terminal, instead of at the start; a binary that `tauto build`
//! makes carries it as it carries the grants.
//! A relative path under `read` or `write` is taken from the project's
//! folder, so it means the same wherever the run starts. The reading is
//! strict: an unknown key or a malformed value is an error.

use std::path::Path;

use eure_document::document::EureDocument;
use eure_document::document::node::NodeValue;
use eure_document::value::PrimitiveValue as P;

/// The `--allow-*` flags the keys of `text` stand for; relative paths are
/// taken from `dir`.
#[cfg(test)]
fn flags(text: &str, dir: &Path) -> Result<Vec<String>, String> {
    if text.len() > 1 << 20 {
        return Err(crate::i18n::t!("permissions-too-large"));
    }
    let doc = eure_reader::parse_to_document(text, "permissions").map_err(|e| e.to_string())?;
    flags_of(&doc, doc.get_root_id(), dir)
}

/// The flags of `trust.run` in the project file `text` of the folder `dir`;
/// none when it has no such key.
pub(crate) fn run_trust(text: &str, dir: &Path) -> Result<Vec<String>, String> {
    run_trust_patterns(text, dir).map(|(flags, _)| flags)
}

/// [`run_trust`] and what each key grants to: `write(app::*)` for a key
/// `"write(app::*)"`, `write` (every origin) for a key `write`.
pub(crate) fn run_trust_patterns(
    text: &str,
    dir: &Path,
) -> Result<(Vec<String>, Vec<String>), String> {
    let doc = eure_reader::parse_to_document(text, "Tauto.eure").map_err(|e| e.to_string())?;
    let child = |id, name: &str| match &doc.node(id).content {
        NodeValue::Map(m) => m
            .iter()
            .find(|(k, _)| k.to_string().trim_matches('"') == name)
            .map(|(_, v)| *v),
        _ => None,
    };
    match child(doc.get_root_id(), "trust").and_then(|t| child(t, "run")) {
        Some(id) => flags_and_patterns(&doc, id, dir).map_err(|e| format!("trust.run: {e}")),
        None => Ok((Vec::new(), Vec::new())),
    }
}

fn flags_of(
    doc: &EureDocument,
    root: eure_document::document::NodeId,
    dir: &Path,
) -> Result<Vec<String>, String> {
    flags_and_patterns(doc, root, dir).map(|(flags, _)| flags)
}

/// A key `kind` or `kind(pattern)`: the kind and the pattern of the
/// functions it grants to (`docs/design/host-effects.md`「Origins」).
fn split_key(key: &str) -> Result<(&str, Option<&str>), String> {
    match key.split_once('(') {
        None => Ok((key, None)),
        Some((kind, rest)) => match rest.strip_suffix(')') {
            Some(p) if valid_pattern(p) => Ok((kind, Some(p))),
            _ => Err(crate::i18n::t!("permissions-unknown-key", key = key)),
        },
    }
}

/// `*`, a full name (`app::store::save`), or a prefix of full names
/// (`app::*`).
fn valid_pattern(p: &str) -> bool {
    let name = p.strip_suffix("::*").unwrap_or(p);
    p == "*"
        || (!name.is_empty()
            && name.split("::").all(|part| {
                !part.is_empty() && part.chars().all(|c| c.is_alphanumeric() || c == '_')
            }))
}

fn flags_and_patterns(
    doc: &EureDocument,
    root: eure_document::document::NodeId,
    dir: &Path,
) -> Result<(Vec<String>, Vec<String>), String> {
    let doc = doc;
    let NodeValue::Map(m) = &doc.node(root).content else {
        return Err(crate::i18n::t!("permissions-expected-keys"));
    };
    let mut flags = Vec::new();
    let mut patterns = Vec::new();
    for (key, id) in m.iter() {
        let written = key.to_string().trim_matches('"').to_string();
        // `interactive = true`: what nothing grants is asked of the user at
        // the terminal when the program reaches it, not at its start.
        if written == "interactive" {
            match value(doc, *id)
                .map_err(|e| crate::i18n::t!("permissions-key-error", kind = "interactive", error = e))?
            {
                None => flags.push("--allow-interactive".into()),
                Some(_) => {
                    return Err(crate::i18n::t!(
                        "permissions-true-names-nothing",
                        kind = "interactive"
                    ));
                }
            }
            continue;
        }
        let (key, pattern) = split_key(&written)?;
        let key = key.to_string();
        patterns.push(match pattern {
            Some(p) => format!("{key}({p})"),
            None => key.clone(),
        });
        let kind = match key.as_str() {
            "all" | "read" | "write" | "env" | "net" | "run" | "clipboard" | "div" => key.as_str(),
            other => {
                return Err(crate::i18n::t!("permissions-unknown-key", key = other));
            }
        };
        match value(doc, *id)
            .map_err(|e| crate::i18n::t!("permissions-key-error", kind = kind, error = e))?
        {
            None => flags.push(format!("--allow-{kind}")),
            None if kind == "env" || kind == "net" || kind == "all" => {
                return Err(crate::i18n::t!("permissions-needs-list", kind = kind));
            }
            Some(_) if kind == "all" || kind == "clipboard" || kind == "div" => {
                return Err(crate::i18n::t!(
                    "permissions-true-names-nothing",
                    kind = kind
                ));
            }
            Some(items) => {
                let items: Vec<String> = items
                    .into_iter()
                    .map(|i| match kind {
                        "read" | "write" if Path::new(&i).is_relative() => {
                            dir.join(&i).to_string_lossy().into_owned()
                        }
                        _ => i,
                    })
                    .collect();
                flags.push(format!("--allow-{kind}={}", items.join(",")));
            }
        }
    }
    Ok((merge_flags(flags), patterns))
}

/// One flag per kind: the lists of several keys of a kind
/// (`"read(app::*)"`, `"read(log::*)"`) joined, and the whole kind when one
/// grants it whole. Until targets are told apart by origin, each origin a
/// kind is granted to may reach every target of the kind.
fn merge_flags(flags: Vec<String>) -> Vec<String> {
    let mut kinds: Vec<(String, Option<Vec<String>>)> = Vec::new();
    for f in flags {
        let (kind, items) = match f.split_once('=') {
            Some((k, v)) => (
                k.to_string(),
                Some(v.split(',').map(String::from).collect::<Vec<_>>()),
            ),
            None => (f, None),
        };
        match kinds.iter_mut().find(|(k, _)| *k == kind) {
            Some((_, have)) => match (have.as_mut(), items) {
                (Some(h), Some(i)) => h.extend(i),
                _ => *have = None,
            },
            None => kinds.push((kind, items)),
        }
    }
    kinds
        .into_iter()
        .map(|(k, items)| match items {
            Some(i) => format!("{k}={}", i.join(",")),
            None => k,
        })
        .collect()
}

/// `true` (everything of the kind) as `None`, a list of names as `Some`.
fn value(
    doc: &EureDocument,
    id: eure_document::document::NodeId,
) -> Result<Option<Vec<String>>, String> {
    match &doc.node(id).content {
        NodeValue::Primitive(P::Bool(true)) => Ok(None),
        NodeValue::Primitive(P::Bool(false)) => Err(crate::i18n::t!("permissions-false-default")),
        NodeValue::Array(items) => {
            let mut names = Vec::new();
            for item in items.iter() {
                let NodeValue::Primitive(P::Text(t)) = &doc.node(*item).content else {
                    return Err(crate::i18n::t!("permissions-expected-texts"));
                };
                let name = t.as_str();
                // A flag's list is split at commas: a name with one would be
                // read as two.
                if name.is_empty() || name.contains(',') {
                    return Err(crate::i18n::t!(
                        "permissions-bad-name",
                        name = format!("{name:?}")
                    ));
                }
                names.push(name.to_string());
            }
            if names.is_empty() {
                return Err(crate::i18n::t!("permissions-empty-list"));
            }
            Ok(Some(names))
        }
        _ => Err(crate::i18n::t!("permissions-expected-value")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tauto_rt::permissions::{Grant, Permissions};

    fn read(text: &str) -> Result<Permissions, String> {
        let flags = flags(text, Path::new("/conf"))?;
        Ok(Permissions::from_args(&flags)?.0)
    }

    #[test]
    fn keys_are_the_flags() {
        let p = read(
            "read = [\"data\", \"/etc/hosts\"]\nenv = [\"HOME\"]\nnet = [\"api.example.com\", \"localhost:8080\"]\nclipboard = true\n",
        )
        .unwrap();
        assert_eq!(
            p.read,
            Grant::Only(vec!["/conf/data".into(), "/etc/hosts".into()])
        );
        assert_eq!(p.write, Grant::Denied);
        assert_eq!(p.env, Grant::Only(vec!["HOME".into()]));
        assert_eq!(
            p.net,
            Grant::Only(vec!["api.example.com".into(), "localhost:8080".into()])
        );
        assert_eq!(p.clipboard, Grant::All);
        assert!(p.allows("net", "https://localhost:8080/"));
        assert!(!p.allows("net", "https://localhost:9090/"));
    }

    #[test]
    fn empty_file_denies_everything() {
        assert_eq!(read("").unwrap(), Permissions::default());
    }

    #[test]
    fn trust_run_of_a_project() {
        let text = "package { name = \"a\" }\ntrust {\n  run {\n    read = [\"data\"]\n    net = true\n  }\n}\n";
        let flags = run_trust(text, Path::new("/p")).unwrap();
        assert_eq!(flags, ["--allow-read=/p/data", "--allow-net"]);
        assert!(
            run_trust("package { name = \"a\" }\n", Path::new("/p"))
                .unwrap()
                .is_empty()
        );
        assert!(
            run_trust(
                "trust {\n  run {\n    disk = true\n  }\n}\n",
                Path::new("/p")
            )
            .is_err()
        );
    }

    #[test]
    fn trust_run_keys_name_origins() {
        let text = "trust {\n  run {\n    \"read(app::*)\" = [\"data\"]\n    \"read(log::*)\" = [\"logs\"]\n    write = true\n  }\n}\n";
        let (flags, patterns) = run_trust_patterns(text, Path::new("/p")).unwrap();
        assert_eq!(flags, ["--allow-read=/p/data,/p/logs", "--allow-write"]);
        assert_eq!(patterns, ["read(app::*)", "read(log::*)", "write"]);
        for bad in [
            "\"read(app::)\" = true",
            "\"read(a b)\" = true",
            "\"read(*\" = true",
        ] {
            let text = format!("trust {{\n  run {{\n    {bad}\n  }}\n}}\n");
            assert!(run_trust_patterns(&text, Path::new("/p")).is_err(), "{bad}");
        }
    }

    #[test]
    fn all() {
        assert_eq!(read("all = true\n").unwrap(), Permissions::all());
    }

    #[test]
    fn malformed_is_an_error() {
        for text in [
            "nets = true\n",
            "net = false\n",
            "net = []\n",
            "net = [\"a,b\"]\n",
            "net = [\"\"]\n",
            "net = \"a\"\n",
            "clipboard = [\"x\"]\n",
            "all = [\"x\"]\n",
        ] {
            assert!(read(text).is_err(), "{text}");
        }
    }
}
