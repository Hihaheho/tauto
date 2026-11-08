//! The two files at the root of an index repository: `Index.eure`, how it is
//! published, the same bytes in every commit; and `observations.eure`, the
//! batch of events a commit adds.
//!
//! ```eure
//! format = 1
//! kind = "batch"
//! sequence = 1
//! issued_at = "2026-10-01T12:00:00Z"
//! valid_until = "2026-10-02T12:00:00Z"
//!
//! @ events[] {
//!   kind = "observation"
//!   project = "sha256:…"
//!   rev = "0123…"
//!   source_sha256 = "sha256:…"
//!   first_seen_at = "2026-10-01T11:59:00Z"
//! }
//! ```

use super::strict::{self, Doc};
use crate::spec::Rev;
use tauto_message::{Message, msg};

pub const CONFIG_FILE: &str = "Index.eure";
pub const BATCH_FILE: &str = "observations.eure";
pub const MAX_CONFIG: usize = 64 << 10;
pub const MAX_BATCH: usize = 1 << 20;
pub const MAX_EVENTS: usize = 4096;

pub type Sha256 = [u8; 32];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    /// Shown to people; never an identity or an authority.
    pub name: String,
    /// `sha1` or `sha256`.
    pub git_object_format: String,
}

pub fn config(bytes: &[u8]) -> Result<Config, String> {
    config_message(bytes).map_err(|e| e.to_string())
}

pub(crate) fn config_message(bytes: &[u8]) -> Result<Config, Message> {
    let doc = Doc::parse(bytes, CONFIG_FILE, MAX_CONFIG)?;
    let mut f = doc.fields(doc.root(), CONFIG_FILE)?;
    expect_format(&mut f, "index")?;
    let name = f.text_as("name", |s| {
        if (1..=128).contains(&s.len()) {
            Ok(s.to_string())
        } else {
            Err(msg!("totebag-name-length"))
        }
    })?;
    f.text_as("history", |s| {
        (s == "commit-batches")
            .then_some(())
            .ok_or_else(|| msg!("totebag-only-history", value = format!("{s:?}")))
    })?;
    let git_object_format = f.text_as("git_object_format", |s| match s {
        "sha1" | "sha256" => Ok(s.to_string()),
        _ => Err(msg!("totebag-not-object-format", value = format!("{s:?}"))),
    })?;
    f.finish()?;
    Ok(Config {
        name,
        git_object_format,
    })
}

fn expect_format(f: &mut strict::Fields<'_>, kind: &str) -> Result<(), Message> {
    let format = f.integer("format")?;
    if format != 1 {
        return Err(msg!("totebag-unknown-format", format = format));
    }
    f.text_as("kind", |s| {
        (s == kind).then_some(()).ok_or_else(|| {
            msg!(
                "totebag-expected-value",
                value = format!("{s:?}"),
                want = format!("{kind:?}")
            )
        })
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Batch {
    pub sequence: u64,
    pub issued_at: u64,
    pub valid_until: u64,
    pub events: Vec<Event>,
}

/// A package revision of a project: `(project, rev)`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Key {
    pub project: Sha256,
    pub rev: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    Observation {
        key: Key,
        source: Sha256,
        first_seen_at: u64,
    },
    IndexObservation {
        index: Sha256,
        repository: String,
        reference: String,
        rev: Rev,
        sha256: Sha256,
        first_seen_at: u64,
    },
    Decision {
        key: Key,
        accept: bool,
        reason: String,
    },
    Withdrawal {
        key: Key,
        reason: String,
    },
    Retirement {
        reason: String,
    },
}

impl Batch {
    /// The batch as `observations.eure`, in the form [`batch`] reads.
    pub fn render(&self) -> String {
        use super::strict::{hex_of, time_text};
        let mut out = format!(
            "format = 1\nkind = \"batch\"\nsequence = {}\nissued_at = \"{}\"\nvalid_until = \"{}\"\n",
            self.sequence,
            time_text(self.issued_at),
            time_text(self.valid_until)
        );
        if self.events.is_empty() {
            out.push_str("events = []\n");
        }
        let key = |k: &Key| {
            format!(
                "  project = \"sha256:{}\"\n  rev = \"{}\"\n",
                hex_of(&k.project),
                k.rev
            )
        };
        for e in &self.events {
            out.push_str("\n@ events[] {\n");
            match e {
                Event::Observation {
                    key: k,
                    source,
                    first_seen_at,
                } => out.push_str(&format!(
                    "  kind = \"observation\"\n{}  source_sha256 = \"sha256:{}\"\n  first_seen_at = \"{}\"\n",
                    key(k),
                    hex_of(source),
                    time_text(*first_seen_at)
                )),
                Event::IndexObservation {
                    index,
                    repository,
                    reference,
                    rev,
                    sha256,
                    first_seen_at,
                } => out.push_str(&format!(
                    "  kind = \"index-observation\"\n  index = \"sha256:{}\"\n  repository = {}\n  ref = {}\n  rev = \"{rev}\"\n  sha256 = \"sha256:{}\"\n  first_seen_at = \"{}\"\n",
                    hex_of(index),
                    quote(repository),
                    quote(reference),
                    hex_of(sha256),
                    time_text(*first_seen_at)
                )),
                Event::Decision {
                    key: k,
                    accept,
                    reason,
                } => out.push_str(&format!(
                    "  kind = \"decision\"\n{}  verdict = \"{}\"\n  reason = {}\n",
                    key(k),
                    if *accept { "accept" } else { "reject" },
                    quote(reason)
                )),
                Event::Withdrawal { key: k, reason } => out.push_str(&format!(
                    "  kind = \"withdrawal\"\n{}  reason = {}\n",
                    key(k),
                    quote(reason)
                )),
                Event::Retirement { reason } => out.push_str(&format!(
                    "  kind = \"retirement\"\n  reason = {}\n",
                    quote(reason)
                )),
            }
            out.push_str("}\n");
        }
        out
    }
}

pub fn quote(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push_str(&format!("\\u{{{:x}}}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

pub fn batch(bytes: &[u8], object_format: &str) -> Result<Batch, String> {
    batch_message(bytes, object_format).map_err(|e| e.to_string())
}

pub(crate) fn batch_message(bytes: &[u8], object_format: &str) -> Result<Batch, Message> {
    let doc = Doc::parse(bytes, BATCH_FILE, MAX_BATCH)?;
    let mut f = doc.fields(doc.root(), BATCH_FILE)?;
    expect_format(&mut f, "batch")?;
    let sequence = f.integer("sequence")?;
    let issued_at = f.text_as("issued_at", strict::time)?;
    let valid_until = f.text_as("valid_until", strict::time)?;
    if valid_until <= issued_at {
        return Err(msg!("totebag-valid-until-early", file = BATCH_FILE));
    }
    let items = f.read("events", |d, id| d.list(id, MAX_EVENTS))?;
    f.finish()?;
    let mut events = Vec::with_capacity(items.len());
    for (i, id) in items.into_iter().enumerate() {
        let what = format!("{BATCH_FILE}: events[{i}]");
        // An error that already names the event is not named again.
        let event = event(&doc, id, &what, object_format).map_err(|e| {
            if names_place(&e, &what) {
                e
            } else {
                msg!("totebag-at", place = &what, error = e)
            }
        })?;
        if matches!(events.last(), Some(Event::Retirement { .. })) {
            return Err(msg!("totebag-after-retirement", what = &what));
        }
        events.push(event);
    }
    Ok(Batch {
        sequence,
        issued_at,
        valid_until,
        events,
    })
}

fn event(
    doc: &Doc,
    id: eure_document::document::NodeId,
    what: &str,
    object_format: &str,
) -> Result<Event, Message> {
    let mut f = doc.fields(id, what)?;
    let kind = f.read("kind", |d, id| d.text(id))?;
    let key = |f: &mut strict::Fields<'_>| -> Result<Key, Message> {
        Ok(Key {
            project: f.text_as("project", strict::sha256)?,
            rev: f.text_as("rev", strict::package_rev)?,
        })
    };
    let event = match kind.as_str() {
        "observation" => Event::Observation {
            key: key(&mut f)?,
            source: f.text_as("source_sha256", strict::sha256)?,
            first_seen_at: f.text_as("first_seen_at", strict::time)?,
        },
        "index-observation" => Event::IndexObservation {
            index: f.text_as("index", strict::sha256)?,
            repository: f.text_as("repository", strict::https_url)?,
            reference: f.text_as("ref", strict::branch)?,
            rev: f.text_as("rev", |s| {
                let rev = Rev::parse(s)?;
                if rev.format() == object_format {
                    Ok(rev)
                } else {
                    Err(msg!(
                        "totebag-not-commit-of-format",
                        value = format!("{s:?}"),
                        format = object_format
                    ))
                }
            })?,
            sha256: f.text_as("sha256", strict::sha256)?,
            first_seen_at: f.text_as("first_seen_at", strict::time)?,
        },
        "decision" => Event::Decision {
            key: key(&mut f)?,
            accept: f.text_as("verdict", |s| match s {
                "accept" => Ok(true),
                "reject" => Ok(false),
                _ => Err(msg!("totebag-not-verdict", value = format!("{s:?}"))),
            })?,
            reason: f.text_as("reason", strict::reason)?,
        },
        "withdrawal" => Event::Withdrawal {
            key: key(&mut f)?,
            reason: f.text_as("reason", strict::reason)?,
        },
        "retirement" => Event::Retirement {
            reason: f.text_as("reason", strict::reason)?,
        },
        other => return Err(msg!("totebag-not-event-kind", value = format!("{other:?}"))),
    };
    f.finish()?;
    Ok(event)
}

#[cfg(test)]
mod tests {
    use super::*;

    const H2: &str = "sha256:2222222222222222222222222222222222222222222222222222222222222222";
    const H3: &str = "sha256:3333333333333333333333333333333333333333333333333333333333333333";

    fn sample() -> String {
        format!(
            "format = 1\nkind = \"batch\"\nsequence = 1\nissued_at = \"2026-10-01T12:00:00Z\"\nvalid_until = \"2026-10-02T12:00:00Z\"\n\n\
             @ events[] {{\n  kind = \"observation\"\n  project = \"{H2}\"\n  rev = \"0123456789abcdef0123456789abcdef01234567\"\n  source_sha256 = \"{H3}\"\n  first_seen_at = \"2026-10-01T11:59:00Z\"\n}}\n\
             @ events[] {{\n  kind = \"decision\"\n  project = \"{H2}\"\n  rev = \"0123456789abcdef0123456789abcdef01234567\"\n  verdict = \"accept\"\n  reason = \"この内容を依存として採用する。\"\n}}\n"
        )
    }

    #[test]
    fn the_design_example_reads() {
        let b = batch(sample().as_bytes(), "sha1").unwrap();
        assert_eq!(b.sequence, 1);
        assert_eq!(b.valid_until - b.issued_at, 86_400);
        assert_eq!(b.events.len(), 2);
        assert!(matches!(&b.events[1], Event::Decision { accept: true, .. }));
        let empty = "format = 1\nkind = \"batch\"\nsequence = 0\nissued_at = \"2026-10-01T12:00:00Z\"\nvalid_until = \"2026-10-02T12:00:00Z\"\nevents = []\n";
        assert!(batch(empty.as_bytes(), "sha1").unwrap().events.is_empty());
    }

    #[test]
    fn a_bad_batch_is_refused_whole() {
        let text = sample();
        for (from, to) in [
            ("format = 1", "format = 2"),
            ("kind = \"batch\"", "kind = \"index\""),
            ("sequence = 1", "sequence = -1"),
            (
                "valid_until = \"2026-10-02T12:00:00Z\"",
                "valid_until = \"2026-10-01T12:00:00Z\"",
            ),
            ("verdict = \"accept\"", "verdict = \"maybe\""),
            ("kind = \"observation\"", "kind = \"guess\""),
            ("  first_seen_at", "  extra = \"x\"\n  first_seen_at"),
            ("rev = \"0123", "rev = \"01 23"),
            ("source_sha256 = \"sha256:33", "source_sha256 = \"sha256:3"),
            (
                "first_seen_at = \"2026-10-01T11:59:00Z\"",
                "first_seen_at = \"2026-10-01T11:59:00+09:00\"",
            ),
        ] {
            let bad = text.replacen(from, to, 1);
            assert_ne!(bad, text, "{from}");
            assert!(batch(bad.as_bytes(), "sha1").is_err(), "{from} -> {to}");
        }
        let no_events = text.split("\n\n@").next().unwrap().to_string();
        assert!(
            batch(no_events.as_bytes(), "sha1").is_err(),
            "events must be written"
        );
        let after_retirement = format!(
            "{}@ events[] {{\n  kind = \"retirement\"\n  reason = \"closed\"\n}}\n@ events[] {{\n  kind = \"retirement\"\n  reason = \"again\"\n}}\n",
            text
        );
        assert!(batch(after_retirement.as_bytes(), "sha1").is_err());
    }

    #[test]
    fn a_batch_reads_back_as_rendered() {
        let mut b = batch(sample().as_bytes(), "sha1").unwrap();
        b.events.push(Event::Withdrawal {
            key: Key {
                project: [2; 32],
                rev: "v1.0".into(),
            },
            reason: "a \"bad\" one\nsecond line".into(),
        });
        b.events.push(Event::IndexObservation {
            index: [4; 32],
            repository: "https://example.org/bob/index".into(),
            reference: "refs/heads/main".into(),
            rev: Rev::from_git(&"5".repeat(40)).unwrap(),
            sha256: [6; 32],
            first_seen_at: 1_790_856_000,
        });
        b.events.push(Event::Retirement {
            reason: "closed".into(),
        });
        assert_eq!(batch(b.render().as_bytes(), "sha1").unwrap(), b);
        let empty = Batch {
            sequence: 0,
            issued_at: 0,
            valid_until: 1,
            events: Vec::new(),
        };
        assert_eq!(batch(empty.render().as_bytes(), "sha1").unwrap(), empty);
    }

    #[test]
    fn configs() {
        let good = "format = 1\nkind = \"index\"\nname = \"alice\"\nhistory = \"commit-batches\"\ngit_object_format = \"sha1\"\n";
        assert_eq!(config(good.as_bytes()).unwrap().name, "alice");
        assert!(config(good.replace("sha1", "md5").as_bytes()).is_err());
        assert!(config(format!("{good}pin = \"x\"\n").as_bytes()).is_err());
        assert!(config(good.replace("name = \"alice\"\n", "").as_bytes()).is_err());
    }
}

/// Whether `e` is a `totebag-at` that already says it happened at a place
/// starting with `what`.
fn names_place(e: &Message, what: &str) -> bool {
    e.id == "totebag-at"
        && matches!(e.get("place"), Some(tauto_message::Value::Text(p)) if p.starts_with(what))
}
