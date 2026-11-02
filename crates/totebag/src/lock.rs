//! `Tauto.lock`: the exact commit and content of each tote a project
//! fetches from Git, beside its `Tauto.eure`.
//!
//! ```eure
//! format = 1
//!
//! @ totes[] {
//!   name = "semver"
//!   git = "https://example.com/tauto/monorepo"
//!   ref = "refs/heads/main"
//!   dir = "semver"
//!   project = "sha256:…"
//!   rev = "sha1:0123456789abcdef0123456789abcdef01234567"
//!   source = "sha256:…"
//! }
//! ```
//!
//! A project has one instance of each tote, so a name is in the lock once.
//! The reading is strict: an unknown key, a missing key or a malformed value
//! is an error.

use std::path::Path;

use eure_document::document::node::NodeValue;
use eure_document::document::{EureDocument, NodeId};
use eure_document::value::PrimitiveValue as P;

use tauto_rt::Text;

use crate::core::generated::{List, api};
use crate::spec::{GitSource, Rev, SourceId};
use crate::{list, of_list};

pub const FILE: &str = "Tauto.lock";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Locked {
    pub name: String,
    pub source: GitSource,
    pub rev: Rev,
    pub id: SourceId,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Lock {
    /// In name order.
    pub totes: Vec<Locked>,
}

impl Lock {
    pub fn get(&self, name: &str) -> Option<&Locked> {
        self.totes.iter().find(|t| t.name == name)
    }

    pub fn put(&mut self, locked: Locked) {
        let lock = api::tb_put(to_list(&self.totes), locked.to_core());
        self.totes = of_list(&lock).iter().map(Locked::of_core).collect();
    }

    pub fn render(&self) -> String {
        api::tb_render(to_list(&self.totes)).to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Change {
    Added(Locked),
    Moved(Locked, Locked),
    Removed(Locked),
}

/// What changed from `before` to `after`: what was added or moved in
/// `after`'s order, then what was removed in `before`'s. A name in
/// `unlocked`, found but not locked without the network, is not removed.
pub fn changes(before: &Lock, after: &Lock, unlocked: &[String]) -> Vec<Change> {
    let unlocked = list(unlocked.iter().map(|n| Text::from(n.as_str())));
    let found = api::tb_changes(to_list(&before.totes), to_list(&after.totes), unlocked);
    of_list(&found)
        .into_iter()
        .map(|c| match c {
            api::TbChange::Added(l) => Change::Added(Locked::of_core(&l)),
            api::TbChange::Moved(o, l) => Change::Moved(Locked::of_core(&o), Locked::of_core(&l)),
            api::TbChange::Removed(o) => Change::Removed(Locked::of_core(&o)),
        })
        .collect()
}

pub use crate::core::generated::api::TbPlan as Plan;

/// Where the commit of a Git dependency comes from. `moves`: the update asks
/// for the newest commit of its ref. `report_only`: nothing is locked or
/// fetched. `offline`: the network may not be used. `locked`: the lock has it
/// for the same source. `cached`: that commit's tree is in the cache.
pub fn plan(moves: bool, report_only: bool, offline: bool, locked: bool, cached: bool) -> Plan {
    api::tb_plan(moves, report_only, offline, locked, cached)
}

impl Locked {
    fn to_core(&self) -> api::TbLocked {
        api::TbLocked {
            name: Text::from(self.name.as_str()),
            git: Text::from(self.source.url.as_str()),
            reference: Text::from(self.source.reference.as_str()),
            dir: Text::from(self.source.dir.as_str()),
            project: self.source.project.as_deref().map(Text::from),
            rev: Text::from(self.rev.to_string()),
            source: Text::from(self.id.to_string()),
        }
    }

    /// Only of entries made by [`Locked::to_core`], so their parts are checked.
    fn of_core(l: &api::TbLocked) -> Locked {
        Locked {
            name: l.name.to_string(),
            source: GitSource {
                url: l.git.to_string(),
                reference: l.reference.to_string(),
                dir: l.dir.to_string(),
                project: l.project.as_ref().map(|p| p.to_string()),
            },
            rev: Rev::parse(&l.rev).expect("checked"),
            id: SourceId::parse(&l.source).expect("checked"),
        }
    }
}

fn to_list(totes: &[Locked]) -> List<api::TbLocked> {
    list(totes.iter().map(Locked::to_core))
}

pub fn read(dir: &Path) -> Result<Option<Lock>, String> {
    let file = dir.join(FILE);
    match std::fs::read_to_string(&file) {
        Ok(text) => parse(&text).map(Some).map_err(|e| {
            say!(
                "totebag-at",
                place = file.display().to_string(),
                error = e.to_string()
            )
        }),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(say!(
            "totebag-at",
            place = file.display().to_string(),
            error = e.to_string()
        )),
    }
}

/// Writes the lock beside the manifest in `dir`, replacing the old one whole.
pub fn write(dir: &Path, lock: &Lock) -> Result<(), String> {
    let file = dir.join(FILE);
    let tmp = dir.join(format!(".{FILE}.{}.tmp", std::process::id()));
    std::fs::write(&tmp, lock.render()).map_err(|e| {
        say!(
            "totebag-at",
            place = tmp.display().to_string(),
            error = e.to_string()
        )
    })?;
    std::fs::rename(&tmp, &file).map_err(|e| {
        let _ = std::fs::remove_file(&tmp);
        say!(
            "totebag-at",
            place = file.display().to_string(),
            error = e.to_string()
        )
    })
}

pub fn parse(text: &str) -> Result<Lock, String> {
    if text.len() > 4 << 20 {
        return Err(say!("totebag-lock-too-large"));
    }
    let doc = eure_reader::parse_to_document(text, FILE).map_err(|e| e.to_string())?;
    let mut lock = Lock::default();
    let mut format = None;
    for (key, id) in map(&doc, doc.get_root_id())? {
        match key.as_str() {
            "format" => match &doc.node(id).content {
                NodeValue::Primitive(P::Integer(n)) if n.to_string() == "1" => format = Some(1),
                _ => return Err(say!("totebag-lock-format")),
            },
            "totes" => {
                let NodeValue::Array(items) = &doc.node(id).content else {
                    return Err(say!("totebag-lock-totes-list"));
                };
                for item in items.iter() {
                    let t = locked(&doc, *item)?;
                    if lock.get(&t.name).is_some() {
                        return Err(say!("totebag-locked-twice", name = &t.name));
                    }
                    lock.totes.push(t);
                }
            }
            other => return Err(say!("totebag-unknown-key", key = other)),
        }
    }
    if format.is_none() {
        return Err(say!("totebag-lock-no-format"));
    }
    lock.totes.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(lock)
}

fn locked(doc: &EureDocument, id: NodeId) -> Result<Locked, String> {
    let (mut name, mut url, mut reference, mut dir, mut rev, mut source) =
        (None, None, None, String::new(), None, None);
    let mut project = None;
    for (key, v) in map(doc, id)? {
        let value = text(doc, v).map_err(|e| say!("totebag-at", place = &key, error = e))?;
        match key.as_str() {
            "name" => name = Some(value),
            "git" => url = Some(value),
            "ref" => reference = Some(value),
            "dir" => dir = value,
            "project" => project = Some(value),
            "rev" => rev = Some(Rev::parse(&value)?),
            "source" => source = Some(SourceId::parse(&value)?),
            other => return Err(say!("totebag-lock-unknown-key", key = other)),
        }
    }
    let missing = |k: &str| say!("totebag-lock-missing", key = k.to_string());
    let name = name.ok_or_else(|| missing("name"))?;
    if !crate::valid_name(&name) {
        return Err(say!("totebag-not-a-tote-name", name = format!("{name:?}")));
    }
    let git = GitSource {
        url: url.ok_or_else(|| missing("git"))?,
        reference: reference.ok_or_else(|| missing("ref"))?,
        dir,
        project,
    };
    git.check()?;
    Ok(Locked {
        name,
        source: git,
        rev: rev.ok_or_else(|| missing("rev"))?,
        id: source.ok_or_else(|| missing("source"))?,
    })
}

fn map(doc: &EureDocument, id: NodeId) -> Result<Vec<(String, NodeId)>, String> {
    match &doc.node(id).content {
        NodeValue::Map(m) => Ok(m
            .iter()
            .map(|(k, v)| (k.to_string().trim_matches('"').to_string(), *v))
            .collect()),
        _ => Err(say!("totebag-expected-block")),
    }
}

fn text(doc: &EureDocument, id: NodeId) -> Result<String, String> {
    match &doc.node(id).content {
        NodeValue::Primitive(P::Text(t)) => Ok(t.as_str().to_string()),
        _ => Err(say!("totebag-expected-text")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Lock {
        let mut lock = Lock::default();
        lock.put(Locked {
            name: "text".into(),
            source: GitSource {
                url: "https://example.org/text".into(),
                reference: "refs/heads/main".into(),
                dir: String::new(),
                project: None,
            },
            rev: Rev::from_git(&"1".repeat(40)).unwrap(),
            id: SourceId::parse(&format!("sha256:{}", "a".repeat(64))).unwrap(),
        });
        lock.put(Locked {
            name: "semver".into(),
            source: GitSource {
                url: "https://example.com/tauto/monorepo".into(),
                reference: "refs/tags/v1".into(),
                dir: "semver".into(),
                project: Some(format!("sha256:{}", "c".repeat(64))),
            },
            rev: Rev::from_git(&"2".repeat(40)).unwrap(),
            id: SourceId::parse(&format!("sha256:{}", "b".repeat(64))).unwrap(),
        });
        lock
    }

    #[test]
    fn a_lock_reads_back_as_written() {
        let lock = sample();
        assert_eq!(lock.totes[0].name, "semver");
        let text = lock.render();
        assert_eq!(parse(&text).unwrap(), lock);
        assert_eq!(parse(&Lock::default().render()).unwrap(), Lock::default());
    }

    #[test]
    fn a_bad_lock_is_refused() {
        let text = sample().render();
        for (from, to) in [
            ("format = 1", "format = 2"),
            ("format = 1", ""),
            (
                "  dir = \"semver\"\n",
                "  dir = \"semver\"\n  extra = \"x\"\n",
            ),
            ("name = \"text\"", "name = \"semver\""),
            ("name = \"text\"", "name = \"Text\""),
            ("refs/heads/main", "main"),
            ("https://example.org/text", "http://example.org/text"),
            ("sha1:1111", "sha1:111"),
            ("sha256:aaaa", "sha256:aaa"),
        ] {
            let bad = text.replacen(from, to, 1);
            assert_ne!(bad, text, "{from}");
            assert!(parse(&bad).is_err(), "{from} -> {to}");
        }
        let no_rev: String = text
            .lines()
            .filter(|l| !l.trim_start().starts_with("rev"))
            .map(|l| format!("{l}\n"))
            .collect();
        assert!(parse(&no_rev).is_err());
    }
}
