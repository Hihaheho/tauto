//! `--permissions FILE`: the permissions of a run written once in an Eure
//! file instead of as many `--allow-*` flags (`docs/design/host-effects.md`).
//!
//! ```eure
//! read = ["data", "/etc/hosts"]
//! write = ["out"]
//! env = ["HOME"]
//! net = ["api.example.com", "localhost:8080"]
//! clipboard = true
//! ```
//!
//! A file grants nothing a flag could not: each key is read into the flag it
//! stands for (`net = ["a", "b"]` is `--allow-net=a,b`, `net = true` is
//! `--allow-net`, `all = true` is `--allow-all`), and the flags are read as
//! if written where `--permissions FILE` stands. So the file and the flags
//! around it widen each other as repeated flags do, and what is not written
//! stays denied. A relative path under `read` or `write` is taken from the
//! file's own folder, so the file means the same wherever the run starts.
//! The reading is strict: an unknown key or a malformed value is an error.

use std::path::Path;

use eure_document::document::EureDocument;
use eure_document::document::node::NodeValue;
use eure_document::value::PrimitiveValue as P;

/// `args` with each `--permissions FILE` before a `--` replaced by the flags
/// the file stands for.
pub(crate) fn expand(args: &[String]) -> Result<Vec<String>, String> {
    let mut out = Vec::with_capacity(args.len());
    let mut rest = args.iter();
    while let Some(a) = rest.next() {
        if a == "--" {
            out.push(a.clone());
            out.extend(rest.by_ref().cloned());
            break;
        }
        let file = match a.strip_prefix("--permissions") {
            Some("") => match rest.next() {
                Some(f) => f.clone(),
                None => return Err(crate::i18n::t!("permissions-needs-file")),
            },
            Some(f) if f.starts_with('=') => f[1..].to_string(),
            _ => {
                out.push(a.clone());
                continue;
            }
        };
        let text = std::fs::read_to_string(&file).map_err(|e| {
            crate::i18n::t!(
                "permissions-file-error",
                file = &file,
                error = e.to_string()
            )
        })?;
        let dir = Path::new(&file).parent().unwrap_or(Path::new(""));
        out.extend(
            flags(&text, dir)
                .map_err(|e| crate::i18n::t!("permissions-file-error", file = &file, error = e))?,
        );
    }
    Ok(out)
}

/// The `--allow-*` flags the file `text` stands for; relative paths are
/// taken from `dir`.
pub(crate) fn flags(text: &str, dir: &Path) -> Result<Vec<String>, String> {
    if text.len() > 1 << 20 {
        return Err(crate::i18n::t!("permissions-too-large"));
    }
    let doc = eure_reader::parse_to_document(text, "permissions").map_err(|e| e.to_string())?;
    let NodeValue::Map(m) = &doc.node(doc.get_root_id()).content else {
        return Err(crate::i18n::t!("permissions-expected-keys"));
    };
    let mut flags = Vec::new();
    for (key, id) in m.iter() {
        let key = key.to_string().trim_matches('"').to_string();
        let kind = match key.as_str() {
            "all" | "read" | "write" | "env" | "net" | "run" | "clipboard" | "div" => key.as_str(),
            other => {
                return Err(crate::i18n::t!("permissions-unknown-key", key = other));
            }
        };
        match value(&doc, *id)
            .map_err(|e| crate::i18n::t!("permissions-key-error", kind = kind, error = e))?
        {
            None => flags.push(format!("--allow-{kind}")),
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
    Ok(flags)
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

    #[test]
    fn widens_with_flags_around_it() {
        let dir = std::env::temp_dir().join(format!("tauto-perm-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("p.eure");
        std::fs::write(&file, "net = [\"a.example\"]\n").unwrap();
        let args: Vec<String> = [
            "--allow-net=b.example",
            "--permissions",
            file.to_str().unwrap(),
            "main.taut",
            "--",
            "--permissions",
            "x",
        ]
        .map(String::from)
        .to_vec();
        let out = expand(&args).unwrap();
        assert_eq!(
            out,
            [
                "--allow-net=b.example",
                "--allow-net=a.example",
                "main.taut",
                "--",
                "--permissions",
                "x"
            ]
            .map(String::from)
            .to_vec()
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
