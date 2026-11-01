//! What this machine has established about the indexes it trusts, kept
//! where nothing fetched can write: the pin of each index, the prefix of its
//! history taken in, whether that ledger is frozen, the last check of its
//! origin, when each checkpoint was first seen here, and the latest time an
//! evaluation ran at. Fetched records never create these facts.
//!
//! It lives in `$TAUTO_INDEX_STATE`, else `$XDG_STATE_HOME/tauto/index`, else
//! `~/.local/state/tauto/index`, as `state.eure` beside the Git mirrors of
//! the indexes. A writer holds the lock on `state.lock` from reading to
//! writing; the file is replaced whole.
//!
//! ```eure
//! format = 1
//! kind = "index-state"
//! evaluated_at = "2026-10-01T12:00:00Z"
//!
//! @ indexes[] {
//!   index = "sha256:…"
//!   git = "https://example.org/alice/index"
//!   ref = "refs/heads/main"
//!   pin = "sha1:…"
//!   pin_digest = "sha256:…"
//!   prefix = "sha1:…"
//!   prefix_digest = "sha256:…"
//!   checked = "sha1:…"
//!   checked_digest = "sha256:…"
//!   checked_at = "2026-10-01T11:59:00Z"
//! }
//!
//! @ receipts[] {
//!   index = "sha256:…"
//!   git = "https://example.org/alice/index"
//!   ref = "refs/heads/main"
//!   rev = "sha1:…"
//!   digest = "sha256:…"
//!   first_seen_at = "2026-10-01T11:00:00Z"
//! }
//! ```

use std::fs::File;
use std::path::{Path, PathBuf};

use super::ledger::{Sha256, quote};
use super::strict::{self, Doc, hex_of};
use crate::spec::Rev;

pub const FILE: &str = "state.eure";
pub const MAX_STATE: usize = 16 << 20;
const MAX_ITEMS: usize = 1 << 16;

/// A checkpoint: its commit and its digest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Point {
    pub rev: Rev,
    pub digest: Sha256,
}

/// The latest answer the origin of an index gave: its head, and when.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Check {
    pub head: Point,
    pub at: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ledger {
    /// The index's ID, the digest of its root.
    pub index: Sha256,
    pub url: String,
    pub reference: String,
    /// The checkpoint this machine trusts the index's history through.
    pub pin: Point,
    /// The last checkpoint of the history taken in.
    pub prefix: Point,
    /// Why the ledger stopped taking in batches, when it has.
    pub frozen: Option<String>,
    pub checked: Option<Check>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Receipt {
    pub index: Sha256,
    pub url: String,
    pub reference: String,
    pub point: Point,
    pub first_seen_at: u64,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct State {
    /// No evaluation runs at an earlier time than this.
    pub evaluated_at: u64,
    pub ledgers: Vec<Ledger>,
    pub receipts: Vec<Receipt>,
}

impl State {
    pub fn ledger(&self, index: &Sha256) -> Option<&Ledger> {
        self.ledgers.iter().find(|l| &l.index == index)
    }

    /// Notes that this machine saw `point` of an index at `now`; the
    /// first time it was seen stays.
    pub fn receive(&mut self, index: Sha256, url: &str, reference: &str, point: Point, now: u64) {
        let known = self.receipts.iter().any(|r| {
            r.index == index && r.url == url && r.reference == reference && r.point.rev == point.rev
        });
        if !known {
            self.receipts.push(Receipt {
                index,
                url: url.to_string(),
                reference: reference.to_string(),
                point,
                first_seen_at: now,
            });
        }
    }

    pub fn render(&self) -> String {
        let mut out = format!(
            "// Written by tauto: what this machine has established about the indexes\n\
             // it trusts. Do not edit it.\n\
             format = 1\nkind = \"index-state\"\nevaluated_at = \"{}\"\n",
            strict::time_text(self.evaluated_at)
        );
        if self.ledgers.is_empty() {
            out.push_str("indexes = []\n");
        }
        for l in &self.ledgers {
            out.push_str(&format!(
                "\n@ indexes[] {{\n  index = \"sha256:{}\"\n  git = {}\n  ref = {}\n",
                hex_of(&l.index),
                quote(&l.url),
                quote(&l.reference)
            ));
            point(&mut out, "pin", &l.pin);
            point(&mut out, "prefix", &l.prefix);
            if let Some(why) = &l.frozen {
                out.push_str(&format!("  frozen = {}\n", quote(why)));
            }
            if let Some(c) = &l.checked {
                point(&mut out, "checked", &c.head);
                out.push_str(&format!("  checked_at = \"{}\"\n", strict::time_text(c.at)));
            }
            out.push_str("}\n");
        }
        if self.receipts.is_empty() {
            out.push_str("receipts = []\n");
        }
        for r in &self.receipts {
            out.push_str(&format!(
                "\n@ receipts[] {{\n  index = \"sha256:{}\"\n  git = {}\n  ref = {}\n",
                hex_of(&r.index),
                quote(&r.url),
                quote(&r.reference)
            ));
            point(&mut out, "rev", &r.point);
            out.push_str(&format!(
                "  first_seen_at = \"{}\"\n}}\n",
                strict::time_text(r.first_seen_at)
            ));
        }
        out
    }
}

/// `name = "<rev>"` and the digest beside it: `pin_digest`, or `digest` for `rev`.
fn point(out: &mut String, name: &str, p: &Point) {
    let digest = if name == "rev" {
        "digest".to_string()
    } else {
        format!("{name}_digest")
    };
    out.push_str(&format!(
        "  {name} = \"{}\"\n  {digest} = \"sha256:{}\"\n",
        p.rev,
        hex_of(&p.digest)
    ));
}

pub fn parse(bytes: &[u8]) -> Result<State, String> {
    let doc = Doc::parse(bytes, FILE, MAX_STATE)?;
    let mut f = doc.fields(doc.root(), FILE)?;
    let format = f.integer("format")?;
    if format != 1 {
        return Err(say!(
            "totebag-at",
            place = FILE,
            error = tauto_message::msg!("totebag-unknown-format", format = format)
        ));
    }
    f.text_as("kind", |s| {
        (s == "index-state").then_some(()).ok_or_else(|| {
            say!(
                "totebag-expected-value",
                value = format!("{s:?}"),
                want = "\"index-state\""
            )
        })
    })?;
    let evaluated_at = f.text_as("evaluated_at", strict::time)?;
    let ledgers = f.read("indexes", |d, id| d.list(id, MAX_ITEMS))?;
    let receipts = f.read("receipts", |d, id| d.list(id, MAX_ITEMS))?;
    f.finish()?;
    let mut state = State {
        evaluated_at,
        ..State::default()
    };
    for (i, id) in ledgers.into_iter().enumerate() {
        let what = format!("{FILE}: indexes[{i}]");
        let mut f = doc.fields(id, &what)?;
        let index = f.text_as("index", strict::sha256)?;
        let (url, reference) = origin(&mut f)?;
        let pin = read_point(&mut f, "pin")?;
        let prefix = read_point(&mut f, "prefix")?;
        let frozen = match f.optional("frozen") {
            Some(id) => Some(doc.text(id)?),
            None => None,
        };
        let checked = match f.optional("checked") {
            Some(id) => {
                let rev = Rev::parse(&doc.text(id)?)?;
                let digest = f.text_as("checked_digest", strict::sha256)?;
                let at = f.text_as("checked_at", strict::time)?;
                Some(Check {
                    head: Point { rev, digest },
                    at,
                })
            }
            None => None,
        };
        f.finish()
            .map_err(|e| say!("totebag-at", place = &what, error = e))?;
        if state.ledger(&index).is_some() {
            return Err(say!("totebag-state-index-twice", what = &what));
        }
        state.ledgers.push(Ledger {
            index,
            url,
            reference,
            pin,
            prefix,
            frozen,
            checked,
        });
    }
    for (i, id) in receipts.into_iter().enumerate() {
        let what = format!("{FILE}: receipts[{i}]");
        let mut f = doc.fields(id, &what)?;
        let index = f.text_as("index", strict::sha256)?;
        let (url, reference) = origin(&mut f)?;
        let rev = f.text_as("rev", Rev::parse)?;
        let digest = f.text_as("digest", strict::sha256)?;
        let first_seen_at = f.text_as("first_seen_at", strict::time)?;
        f.finish()
            .map_err(|e| say!("totebag-at", place = &what, error = e))?;
        state.receipts.push(Receipt {
            index,
            url,
            reference,
            point: Point { rev, digest },
            first_seen_at,
        });
    }
    Ok(state)
}

fn origin(f: &mut strict::Fields<'_>) -> Result<(String, String), String> {
    let url = f.text_as("git", |s| crate::spec::check_url(s).map(|()| s.to_string()))?;
    let reference = f.text_as("ref", strict::branch)?;
    Ok((url, reference))
}

fn read_point(f: &mut strict::Fields<'_>, name: &str) -> Result<Point, String> {
    Ok(Point {
        rev: f.text_as(name, Rev::parse)?,
        digest: f.text_as(&format!("{name}_digest"), strict::sha256)?,
    })
}

/// Where the state is kept.
pub struct Store {
    dir: PathBuf,
}

/// The state, read under the lock; the lock is held until this is dropped.
pub struct Held {
    _lock: File,
    file: PathBuf,
    pub state: State,
}

impl Store {
    pub fn from_env() -> Result<Store, String> {
        let var = |k: &str| {
            std::env::var_os(k)
                .filter(|v| !v.is_empty())
                .map(PathBuf::from)
        };
        if let Some(dir) = var("TAUTO_INDEX_STATE") {
            return Ok(Store::at(dir));
        }
        if let Some(dir) = var("XDG_STATE_HOME") {
            return Ok(Store::at(dir.join("tauto/index")));
        }
        match var("HOME") {
            Some(home) => Ok(Store::at(home.join(".local/state/tauto/index"))),
            None => Err(say!("totebag-no-state-place")),
        }
    }

    pub fn at(dir: PathBuf) -> Store {
        Store { dir }
    }

    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// The bare repository an index is fetched into. It is kept with the
    /// state, not in the cache: the history taken in is read again from it.
    pub fn mirror_dir(&self, url: &str) -> PathBuf {
        self.dir
            .join("git")
            .join(format!("{}.git", tauto_syntax::sha256_hex(url.as_bytes())))
    }

    /// Takes the lock and reads the state; an empty state when there is none.
    pub fn hold(&self) -> Result<Held, String> {
        std::fs::create_dir_all(&self.dir).map_err(|e| {
            say!(
                "totebag-at",
                place = self.dir.display().to_string(),
                error = e.to_string()
            )
        })?;
        let lock_path = self.dir.join("state.lock");
        let lock = File::options()
            .create(true)
            .truncate(false)
            .write(true)
            .open(&lock_path)
            .map_err(|e| {
                say!(
                    "totebag-at",
                    place = lock_path.display().to_string(),
                    error = e.to_string()
                )
            })?;
        lock.lock().map_err(|e| {
            say!(
                "totebag-at",
                place = lock_path.display().to_string(),
                error = e.to_string()
            )
        })?;
        let file = self.dir.join(FILE);
        let state = match std::fs::read(&file) {
            Ok(bytes) => parse(&bytes)?,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => State::default(),
            Err(e) => {
                return Err(say!(
                    "totebag-at",
                    place = file.display().to_string(),
                    error = e.to_string()
                ));
            }
        };
        Ok(Held {
            _lock: lock,
            file,
            state,
        })
    }
}

impl Held {
    /// Replaces the file whole with the state as it is now.
    pub fn save(&self) -> Result<(), String> {
        let tmp = self
            .file
            .with_file_name(format!(".{FILE}.{}.tmp", std::process::id()));
        let text = self.state.render();
        let write = || -> std::io::Result<()> {
            use std::io::Write;
            let mut f = File::create(&tmp)?;
            f.write_all(text.as_bytes())?;
            f.sync_all()?;
            std::fs::rename(&tmp, &self.file)
        };
        write().map_err(|e| {
            let _ = std::fs::remove_file(&tmp);
            say!(
                "totebag-at",
                place = self.file.display().to_string(),
                error = e.to_string()
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn point(c: char) -> Point {
        Point {
            rev: Rev::from_git(&c.to_string().repeat(40)).unwrap(),
            digest: [c as u8; 32],
        }
    }

    fn sample() -> State {
        State {
            evaluated_at: 1_790_856_000,
            ledgers: vec![
                Ledger {
                    index: [1; 32],
                    url: "https://example.org/alice/index".into(),
                    reference: "refs/heads/main".into(),
                    pin: point('a'),
                    prefix: point('b'),
                    frozen: None,
                    checked: Some(Check {
                        head: point('b'),
                        at: 1_790_855_940,
                    }),
                },
                Ledger {
                    index: [2; 32],
                    url: "https://example.org/bob/index".into(),
                    reference: "refs/heads/main".into(),
                    pin: point('c'),
                    prefix: point('c'),
                    frozen: Some("the history at dddddddd is not \"an extension\"".into()),
                    checked: None,
                },
            ],
            receipts: vec![Receipt {
                index: [1; 32],
                url: "https://example.org/alice/index".into(),
                reference: "refs/heads/main".into(),
                point: point('b'),
                first_seen_at: 1_790_852_400,
            }],
        }
    }

    #[test]
    fn a_state_reads_back_as_written() {
        let s = sample();
        assert_eq!(parse(s.render().as_bytes()).unwrap(), s);
        let empty = State::default();
        assert_eq!(parse(empty.render().as_bytes()).unwrap(), empty);
    }

    #[test]
    fn a_bad_state_is_refused() {
        let text = sample().render();
        for (from, to) in [
            ("format = 1", "format = 2"),
            ("kind = \"index-state\"", "kind = \"index\""),
            ("  pin_digest", "  extra = \"x\"\n  pin_digest"),
            (
                &format!("index = \"sha256:{}", "02".repeat(32)),
                &format!("index = \"sha256:{}", "01".repeat(32)),
            ),
            ("ref = \"refs/heads/main\"", "ref = \"refs/tags/v1\""),
        ] {
            let bad = text.replacen(from, to, 1);
            assert_ne!(bad, text, "{from}");
            assert!(parse(bad.as_bytes()).is_err(), "{from} -> {to}");
        }
    }

    #[test]
    fn the_first_receipt_stays() {
        let mut s = sample();
        s.receive(
            [1; 32],
            "https://example.org/alice/index",
            "refs/heads/main",
            point('b'),
            9,
        );
        assert_eq!(s.receipts.len(), 1);
        assert_eq!(s.receipts[0].first_seen_at, 1_790_852_400);
        s.receive(
            [1; 32],
            "https://example.org/alice/index",
            "refs/heads/main",
            point('e'),
            9,
        );
        assert_eq!(s.receipts.len(), 2);
    }

    #[test]
    fn a_held_state_is_saved_whole() {
        let dir = std::env::temp_dir().join(format!("totebag-state-{}", std::process::id()));
        let store = Store::at(dir.clone());
        let mut held = store.hold().unwrap();
        assert_eq!(held.state, State::default());
        held.state = sample();
        held.save().unwrap();
        drop(held);
        assert_eq!(store.hold().unwrap().state, sample());
        let _ = std::fs::remove_dir_all(dir);
    }
}
