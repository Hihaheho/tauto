//! The user's trust policy: which indexes are trusted, read from where and
//! pinned where, and what adopting a package revision requires of them. It
//! is the user's own document; nothing an index publishes changes it.
//!
//! ```eure
//! format = 1
//! kind = "policy"
//! track = "dependency-closure"
//!
//! @ indexes[] {
//!   alias = "alice"
//!   id = "sha256:…"
//!   transport = "https"
//!   repository = "https://example.org/alice/index"
//!   ref = "refs/heads/main"
//!   pin_rev = "sha1:…"
//!   pin_sha256 = "sha256:…"
//! }
//!
//! @ defaults {
//!   require = "all"
//!   observers = ["alice", "bob"]
//!   age_witnesses = ["carol"]
//!   min_age_seconds = 604800
//!   max_checkpoint_lifetime_seconds = 86400
//!   max_source_check_age_seconds = 3600
//! }
//!
//! @ rules[] {
//!   project = "sha256:…"
//!   require = "all"
//!   …every field of `defaults`
//! }
//! ```
//!
//! An index is read from `(transport, repository, ref)` exactly: `https`, or
//! `local-owned` for the user's own index in a `file:///` repository. A
//! remote age witness is read over `https` and is neither an observer's
//! index nor read from an observer's repository. A rule for a project is
//! complete; nothing in it falls back to the defaults.

use super::ledger::Sha256;
use super::state::Point;
use eure_document::document::NodeId;

use super::strict::{self, Doc, Fields, hex_of};
use crate::spec::Rev;

pub const MAX_POLICY: usize = 1 << 20;
const MAX_ITEMS: usize = 4096;

/// An index the policy trusts: where it is read from, its ID, and the
/// checkpoint its history is trusted through at first.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trusted {
    pub alias: String,
    pub url: String,
    pub reference: String,
    pub index: Sha256,
    pub pin: Point,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Witness {
    /// This machine: it has had the checkpoint for long enough.
    Local,
    /// Another index has recorded the checkpoint for long enough.
    Remote(Trusted),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Limits {
    pub min_age: u64,
    pub max_checkpoint_lifetime: u64,
    pub max_source_check_age: u64,
}

/// What adopting one project's revisions requires.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pub observers: Vec<Trusted>,
    pub witnesses: Vec<Witness>,
    pub limits: Limits,
}

impl Rule {
    /// Every index the rule names, each once.
    pub fn indexes(&self) -> Vec<&Trusted> {
        let mut out: Vec<&Trusted> = Vec::new();
        let remote = self.witnesses.iter().filter_map(|w| match w {
            Witness::Remote(t) => Some(t),
            Witness::Local => None,
        });
        for t in self.observers.iter().chain(remote) {
            if !out.iter().any(|o| o.index == t.index) {
                out.push(t);
            }
        }
        out
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Policy {
    pub indexes: Vec<Trusted>,
    pub defaults: Rule,
    pub rules: Vec<(Sha256, Rule)>,
}

impl Policy {
    /// The rule for revisions of `project`.
    pub fn rule(&self, project: &Sha256) -> &Rule {
        self.rules
            .iter()
            .find(|(p, _)| p == project)
            .map_or(&self.defaults, |(_, r)| r)
    }
}

pub fn parse(bytes: &[u8], name: &str) -> Result<Policy, String> {
    let doc = Doc::parse(bytes, name, MAX_POLICY)?;
    let mut f = doc.fields(doc.root(), name)?;
    let format = f.integer("format")?;
    if format != 1 {
        return Err(say!(
            "totebag-at",
            place = name,
            error = tauto_message::msg!("totebag-unknown-format", format = format)
        ));
    }
    f.text_as("kind", |s| expect(s, "policy"))?;
    f.text_as("track", |s| expect(s, "dependency-closure"))?;
    let index_items = f.read("indexes", |d, id| d.list(id, MAX_ITEMS))?;
    let defaults = f.required("defaults")?;
    let rule_items = match f.optional("rules") {
        Some(id) => doc
            .list(id, MAX_ITEMS)
            .map_err(|e| say!("totebag-at", place = format!("{name}.rules"), error = e))?,
        None => Vec::new(),
    };
    f.finish()?;

    let indexes = read_indexes(&doc, index_items, name)?;

    let defaults = rule(
        doc.fields(defaults, &format!("{name}: defaults"))?,
        &indexes,
    )?;
    let mut rules: Vec<(Sha256, Rule)> = Vec::new();
    for (i, id) in rule_items.into_iter().enumerate() {
        let what = format!("{name}: rules[{i}]");
        let mut f = doc.fields(id, &what)?;
        let project = f.text_as("project", strict::sha256)?;
        if rules.iter().any(|(p, _)| *p == project) {
            return Err(say!("totebag-one-rule", what = &what));
        }
        rules.push((project, rule(f, &indexes)?));
    }
    Ok(Policy {
        indexes: indexes.into_iter().map(|(t, _)| t).collect(),
        defaults,
        rules,
    })
}

/// The `indexes` of a policy, each with whether it is read over https.
pub(super) fn read_indexes(
    doc: &Doc,
    items: Vec<NodeId>,
    name: &str,
) -> Result<Vec<(Trusted, bool)>, String> {
    let mut indexes: Vec<(Trusted, bool)> = Vec::new();
    for (i, id) in items.into_iter().enumerate() {
        let what = format!("{name}: indexes[{i}]");
        let mut f = doc.fields(id, &what)?;
        let alias = f.text_as("alias", strict::alias)?;
        if alias == "local" {
            return Err(say!("totebag-local-not-index", what = &what));
        }
        let index = f.text_as("id", strict::sha256)?;
        let https = f.text_as("transport", |s| match s {
            "https" => Ok(true),
            "local-owned" => Ok(false),
            _ => Err(say!("totebag-not-transport", value = format!("{s:?}"))),
        })?;
        let url = f.text_as("repository", |s| {
            if https {
                strict::https_url(s)
            } else {
                crate::spec::check_url(s)?;
                if s.starts_with("file:///") {
                    Ok(s.to_string())
                } else {
                    Err(say!("totebag-local-owned-file", value = format!("{s:?}")))
                }
            }
        })?;
        let reference = f.text_as("ref", strict::branch)?;
        let pin = Point {
            rev: f.text_as("pin_rev", Rev::parse)?,
            digest: f.text_as("pin_sha256", strict::sha256)?,
        };
        f.finish()?;
        if let Some((t, _)) = indexes.iter().find(|(t, _)| t.alias == alias) {
            return Err(say!("totebag-alias-twice", what = &what, alias = &t.alias));
        }
        if let Some((t, _)) = indexes.iter().find(|(t, _)| t.index == index) {
            return Err(say!(
                "totebag-index-twice",
                what = &what,
                index = hex_of(&index),
                alias = &t.alias
            ));
        }
        indexes.push((
            Trusted {
                alias,
                url,
                reference,
                index,
                pin,
            },
            https,
        ));
    }
    Ok(indexes)
}

pub(super) fn expect(s: &str, want: &str) -> Result<(), String> {
    (s == want).then_some(()).ok_or_else(|| {
        say!(
            "totebag-expected-value",
            value = format!("{s:?}"),
            want = format!("{want:?}")
        )
    })
}

pub(super) fn aliases(f: &mut Fields<'_>, key: &str) -> Result<Vec<String>, String> {
    let names = f.read(key, |d, id| {
        d.list(id, MAX_ITEMS)?
            .into_iter()
            .map(|id| d.text(id))
            .collect::<Result<Vec<_>, _>>()
    })?;
    if names.is_empty() {
        return Err(say!("totebag-names-no-index", key = key));
    }
    let listed = crate::list(names.iter().map(|n| tauto_rt::Text::from(n.as_str())));
    if let Some(n) = crate::core::generated::api::tb_twice(listed) {
        return Err(say!("totebag-names-twice", key = key, name = &*n));
    }
    Ok(names)
}

fn rule(mut f: Fields<'_>, indexes: &[(Trusted, bool)]) -> Result<Rule, String> {
    f.text_as("require", |s| expect(s, "all"))?;
    let observers = observers(&aliases(&mut f, "observers")?, indexes)?;
    let witnesses = witnesses(&aliases(&mut f, "age_witnesses")?, indexes)?;
    independent(&observers, &witnesses)?;
    let seconds =
        |f: &mut Fields<'_>, key: &str| f.read(key, |d, id| strict::seconds(d.integer(id)?));
    let limits = Limits {
        min_age: seconds(&mut f, "min_age_seconds")?,
        max_checkpoint_lifetime: seconds(&mut f, "max_checkpoint_lifetime_seconds")?,
        max_source_check_age: seconds(&mut f, "max_source_check_age_seconds")?,
    };
    if limits.max_checkpoint_lifetime == 0 || limits.max_source_check_age == 0 {
        return Err(say!("totebag-limits-positive"));
    }
    f.finish()?;
    Ok(Rule {
        observers,
        witnesses,
        limits,
    })
}

fn find<'a>(alias: &str, indexes: &'a [(Trusted, bool)]) -> Result<&'a (Trusted, bool), String> {
    indexes
        .iter()
        .find(|(t, _)| t.alias == alias)
        .ok_or_else(|| say!("totebag-no-such-index", alias = alias))
}

/// The observers named `names`.
pub(super) fn observers(
    names: &[String],
    indexes: &[(Trusted, bool)],
) -> Result<Vec<Trusted>, String> {
    names
        .iter()
        .map(|a| {
            if a == "local" {
                Err(say!("totebag-local-does-not-observe"))
            } else {
                find(a, indexes).map(|(t, _)| t.clone())
            }
        })
        .collect()
}

/// The age witnesses named `names`: `local`, or an index read over https.
pub(super) fn witnesses(
    names: &[String],
    indexes: &[(Trusted, bool)],
) -> Result<Vec<Witness>, String> {
    let mut witnesses = Vec::new();
    for a in names {
        if a == "local" {
            witnesses.push(Witness::Local);
            continue;
        }
        let (t, https) = find(a, indexes)?;
        if !https {
            return Err(say!("totebag-witness-local-owned", alias = a));
        }
        witnesses.push(Witness::Remote(t.clone()));
    }
    Ok(witnesses)
}

/// Fails when a remote witness is an observer's index, or is read from an
/// observer's repository.
pub(super) fn independent(observers: &[Trusted], witnesses: &[Witness]) -> Result<(), String> {
    use crate::core::generated::api::{TbIndex, TbNotIndependent, tb_independent};
    let index = |t: &Trusted| TbIndex {
        alias: tauto_rt::Text::from(t.alias.as_str()),
        id: tauto_rt::Text::from(hex_of(&t.index)),
        repository: tauto_rt::Text::from(t.url.as_str()),
        reference: tauto_rt::Text::from(t.reference.as_str()),
    };
    let remote = witnesses.iter().filter_map(|w| match w {
        Witness::Remote(t) => Some(index(t)),
        Witness::Local => None,
    });
    match tb_independent(
        crate::list(observers.iter().map(index)),
        crate::list(remote),
    ) {
        None => Ok(()),
        Some(TbNotIndependent { witness, observer }) => Err(say!(
            "totebag-witness-not-independent",
            witness = &*witness,
            observer = &*observer
        )),
    }
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;

    pub(in crate::index) fn index(alias: &str, n: u8, transport: &str, repository: &str) -> String {
        format!(
            "@ indexes[] {{\n  alias = \"{alias}\"\n  id = \"sha256:{}\"\n  transport = \"{transport}\"\n  repository = \"{repository}\"\n  ref = \"refs/heads/main\"\n  pin_rev = \"sha1:{}\"\n  pin_sha256 = \"sha256:{}\"\n}}\n",
            format!("{n:02x}").repeat(32),
            "a".repeat(40),
            format!("{n:02x}").repeat(32),
        )
    }

    const RULE: &str = "  require = \"all\"\n  observers = [\"alice\", \"bob\"]\n  age_witnesses = [\"carol\"]\n  min_age_seconds = 604800\n  max_checkpoint_lifetime_seconds = 86400\n  max_source_check_age_seconds = 3600\n";

    pub(in crate::index) fn sample() -> String {
        format!(
            "format = 1\nkind = \"policy\"\ntrack = \"dependency-closure\"\n\n{}{}{}{}\n@ defaults {{\n{RULE}}}\n\n@ rules[] {{\n  project = \"sha256:{}\"\n{}}}\n",
            index("alice", 1, "https", "https://example.org/alice/index"),
            index("bob", 2, "https", "https://example.org/bob/index"),
            index("carol", 3, "https", "https://example.org/carol/index"),
            index("me", 4, "local-owned", "file:///home/me/index"),
            "77".repeat(32),
            RULE.replace("[\"alice\", \"bob\"]", "[\"me\"]")
                .replace("[\"carol\"]", "[\"local\", \"carol\"]"),
        )
    }

    #[test]
    fn the_design_example_reads() {
        let p = parse(sample().as_bytes(), "Trust.eure").unwrap();
        assert_eq!(p.indexes.len(), 4);
        assert_eq!(p.defaults.observers.len(), 2);
        assert_eq!(p.defaults.limits.min_age, 604_800);
        let mine = p.rule(&[0x77; 32]);
        assert_eq!(mine.observers[0].alias, "me");
        assert_eq!(mine.witnesses[0], Witness::Local);
        assert_eq!(p.rule(&[0x78; 32]), &p.defaults);
        assert_eq!(mine.indexes().len(), 2);
    }

    #[test]
    fn a_bad_policy_is_refused() {
        let text = sample();
        for (from, to) in [
            ("kind = \"policy\"", "kind = \"index\""),
            ("track = \"dependency-closure\"", "track = \"all\""),
            ("require = \"all\"", "require = \"any\""),
            ("[\"carol\"]", "[\"alice\"]"),
            ("[\"carol\"]", "[\"me\"]"),
            ("[\"carol\"]", "[]"),
            ("[\"alice\", \"bob\"]", "[\"alice\", \"alice\"]"),
            ("[\"alice\", \"bob\"]", "[\"dave\"]"),
            ("[\"alice\", \"bob\"]", "[\"local\"]"),
            ("alias = \"bob\"", "alias = \"alice\""),
            ("alias = \"bob\"", "alias = \"local\""),
            ("transport = \"https\"", "transport = \"ssh\""),
            (
                "https://example.org/alice/index",
                "http://example.org/alice/index",
            ),
            ("file:///home/me/index", "https://example.org/me"),
            (
                "max_source_check_age_seconds = 3600",
                "max_source_check_age_seconds = 0",
            ),
            ("min_age_seconds = 604800", "min_age_seconds = 999999999999"),
            ("  min_age_seconds", "  extra = 1\n  min_age_seconds"),
        ] {
            let bad = text.replacen(from, to, 1);
            assert_ne!(bad, text, "{from}");
            assert!(
                parse(bad.as_bytes(), "Trust.eure").is_err(),
                "{from} -> {to}"
            );
        }
        // A rule for a project is complete.
        let last = text
            .rfind("  max_source_check_age_seconds = 3600\n")
            .unwrap();
        let mut partial = text.clone();
        partial.replace_range(
            last..last + "  max_source_check_age_seconds = 3600\n".len(),
            "",
        );
        assert!(parse(partial.as_bytes(), "Trust.eure").is_err());
        // The same carol, read through a mirror of alice's repository, is not
        // independent.
        let mirror = text.replace(
            "https://example.org/carol/index",
            "https://example.org/alice/index",
        );
        assert!(parse(mirror.as_bytes(), "Trust.eure").is_err());
    }
}
