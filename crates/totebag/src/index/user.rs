//! The user's own policy: what this machine requires of every project's
//! `Trust.eure` on top of what the project requires. It can only add to a
//! project's policy: more observers and age witnesses, a longer wait, and
//! shorter limits. Every rule of the project's policy is strengthened by it
//! alike.
//!
//! ```eure
//! format = 1
//! kind = "user-policy"
//! track = "dependency-closure"
//!
//! @ indexes[] {
//!   …as in Trust.eure
//! }
//!
//! @ require {
//!   observers = ["dave"]
//!   age_witnesses = ["local"]
//!   min_age_seconds = 1209600
//!   max_checkpoint_lifetime_seconds = 86400
//!   max_source_check_age_seconds = 3600
//! }
//! ```
//!
//! Every field of `require`, and `require` itself, may be left out. A wait
//! left out is the safe default of 14 days, so that nothing published just
//! now is adopted; `min_age_seconds = 0` waits only as long as the project
//! says. With no user policy at all, the safe default is all there is.
//!
//! An index the user's policy names that the project's names too is the
//! same index read from the same place and pinned at the same checkpoint, so
//! that what the project's policy trusts is not changed, only added to.

use super::policy::{
    self, Limits, MAX_POLICY, Policy, Rule, Trusted, Witness, expect, read_indexes,
};
use super::strict::{self, Doc, Fields, hex_of};

/// The wait of the safe default: 14 days.
pub const SAFE_MIN_AGE: u64 = 14 * 24 * 60 * 60;

const MAX_ITEMS: usize = 4096;

/// What the user's policy adds to every rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UserPolicy {
    pub indexes: Vec<Trusted>,
    pub observers: Vec<Trusted>,
    pub witnesses: Vec<Witness>,
    pub min_age: u64,
    pub max_checkpoint_lifetime: Option<u64>,
    pub max_source_check_age: Option<u64>,
}

impl Default for UserPolicy {
    /// The safe default: nothing more than a wait of 14 days.
    fn default() -> UserPolicy {
        UserPolicy {
            indexes: Vec::new(),
            observers: Vec::new(),
            witnesses: Vec::new(),
            min_age: SAFE_MIN_AGE,
            max_checkpoint_lifetime: None,
            max_source_check_age: None,
        }
    }
}

pub fn parse(bytes: &[u8], name: &str) -> Result<UserPolicy, String> {
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
    f.text_as("kind", |s| expect(s, "user-policy"))?;
    f.text_as("track", |s| expect(s, "dependency-closure"))?;
    let index_items = match f.optional("indexes") {
        Some(id) => doc
            .list(id, MAX_ITEMS)
            .map_err(|e| say!("totebag-at", place = format!("{name}.indexes"), error = e))?,
        None => Vec::new(),
    };
    let require = f.optional("require");
    f.finish()?;

    let indexes = read_indexes(&doc, index_items, name)?;
    let mut user = UserPolicy {
        indexes: indexes.iter().map(|(t, _)| t.clone()).collect(),
        ..UserPolicy::default()
    };
    let Some(require) = require else {
        return Ok(user);
    };
    let what = format!("{name}: require");
    let mut f = doc.fields(require, &what)?;
    let names = |f: &mut Fields<'_>, key: &str| {
        if f.has(key) {
            policy::aliases(f, key).map_err(|e| say!("totebag-at", place = &what, error = e))
        } else {
            Ok(Vec::new())
        }
    };
    let observers = names(&mut f, "observers")?;
    let witnesses = names(&mut f, "age_witnesses")?;
    let at = |e: String| say!("totebag-at", place = &what, error = e);
    user.observers = policy::observers(&observers, &indexes).map_err(at)?;
    user.witnesses = policy::witnesses(&witnesses, &indexes).map_err(at)?;
    policy::independent(&user.observers, &user.witnesses).map_err(at)?;
    let mut seconds = |key: &str| -> Result<Option<u64>, String> {
        if f.has(key) {
            f.read(key, |d, id| strict::seconds(d.integer(id)?))
                .map(Some)
        } else {
            Ok(None)
        }
    };
    if let Some(age) = seconds("min_age_seconds")? {
        user.min_age = age;
    }
    user.max_checkpoint_lifetime = seconds("max_checkpoint_lifetime_seconds")?;
    user.max_source_check_age = seconds("max_source_check_age_seconds")?;
    if user.max_checkpoint_lifetime == Some(0) || user.max_source_check_age == Some(0) {
        return Err(say!(
            "totebag-at",
            place = &what,
            error = tauto_message::msg!("totebag-limits-positive")
        ));
    }
    f.finish()?;
    Ok(user)
}

impl UserPolicy {
    /// `project` with every rule strengthened by this policy.
    pub fn strengthen(&self, project: &Policy) -> Result<Policy, String> {
        let mut indexes = project.indexes.clone();
        for u in &self.indexes {
            if let Some(t) = indexes.iter().find(|t| t.index == u.index) {
                if (&t.url, &t.reference, &t.pin) != (&u.url, &u.reference, &u.pin) {
                    return Err(say!(
                        "totebag-user-changes-index",
                        alias = &u.alias,
                        index = hex_of(&u.index),
                        url = &u.url,
                        reference = &u.reference,
                        pin = u.pin.rev.short(),
                        project_url = &t.url,
                        project_reference = &t.reference,
                        project_pin = t.pin.rev.short(),
                        project_alias = &t.alias
                    ));
                }
                continue;
            }
            if let Some(t) = indexes.iter().find(|t| t.alias == u.alias) {
                return Err(say!(
                    "totebag-user-alias-taken",
                    alias = &u.alias,
                    index = hex_of(&t.index),
                    other = hex_of(&u.index)
                ));
            }
            indexes.push(u.clone());
        }
        // An index both policies name is called as the project calls it.
        let same = |t: &Trusted| {
            indexes
                .iter()
                .find(|i| i.index == t.index)
                .cloned()
                .unwrap_or_else(|| t.clone())
        };
        let strengthen = |rule: &Rule| -> Result<Rule, String> {
            let mut out = rule.clone();
            for o in &self.observers {
                if !out.observers.iter().any(|t| t.index == o.index) {
                    out.observers.push(same(o));
                }
            }
            for w in &self.witnesses {
                let has = out.witnesses.iter().any(|v| match (v, w) {
                    (Witness::Local, Witness::Local) => true,
                    (Witness::Remote(a), Witness::Remote(b)) => a.index == b.index,
                    _ => false,
                });
                if !has {
                    out.witnesses.push(match w {
                        Witness::Local => Witness::Local,
                        Witness::Remote(t) => Witness::Remote(same(t)),
                    });
                }
            }
            policy::independent(&out.observers, &out.witnesses)?;
            let Limits {
                min_age,
                max_checkpoint_lifetime,
                max_source_check_age,
            } = rule.limits;
            out.limits = Limits {
                min_age: min_age.max(self.min_age),
                max_checkpoint_lifetime: self
                    .max_checkpoint_lifetime
                    .map_or(max_checkpoint_lifetime, |m| m.min(max_checkpoint_lifetime)),
                max_source_check_age: self
                    .max_source_check_age
                    .map_or(max_source_check_age, |m| m.min(max_source_check_age)),
            };
            Ok(out)
        };
        let defaults = strengthen(&project.defaults)?;
        let rules = project
            .rules
            .iter()
            .map(|(p, r)| {
                strengthen(r)
                    .map(|r| (*p, r))
                    .map_err(|e| say!("totebag-rule-for", project = hex_of(p), error = e))
            })
            .collect::<Result<_, _>>()?;
        Ok(Policy {
            indexes,
            defaults,
            rules,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::index::policy::tests::{index, sample};

    fn project() -> Policy {
        policy::parse(sample().as_bytes(), "Trust.eure").unwrap()
    }

    const HEAD: &str = "format = 1\nkind = \"user-policy\"\ntrack = \"dependency-closure\"\n\n";

    fn user(rest: &str) -> Result<UserPolicy, String> {
        parse(format!("{HEAD}{rest}").as_bytes(), "trust.eure")
    }

    /// Every rule of `strong` requires at least what `weak`'s does.
    fn stronger(strong: &Policy, weak: &Policy) {
        let pairs = std::iter::once((&strong.defaults, &weak.defaults)).chain(
            strong
                .rules
                .iter()
                .zip(&weak.rules)
                .map(|((p, s), (q, w))| {
                    assert_eq!(p, q);
                    (s, w)
                }),
        );
        for (s, w) in pairs {
            for o in &w.observers {
                assert!(s.observers.iter().any(|t| t == o));
            }
            for v in &w.witnesses {
                assert!(s.witnesses.contains(v));
            }
            assert!(s.limits.min_age >= w.limits.min_age);
            assert!(s.limits.max_checkpoint_lifetime <= w.limits.max_checkpoint_lifetime);
            assert!(s.limits.max_source_check_age <= w.limits.max_source_check_age);
        }
        assert_eq!(strong.rules.len(), weak.rules.len());
    }

    #[test]
    fn the_safe_default_waits_14_days() {
        let p = project();
        let none = UserPolicy::default().strengthen(&p).unwrap();
        stronger(&none, &p);
        assert_eq!(none.defaults.limits.min_age, SAFE_MIN_AGE);
        assert_eq!(none.rule(&[0x77; 32]).limits.min_age, SAFE_MIN_AGE);
        assert_eq!(none.defaults.observers, p.defaults.observers);
        // A file without a wait keeps the safe default's; a wait of 0 keeps
        // the project's.
        assert_eq!(user("").unwrap(), UserPolicy::default());
        let zero = user("@ require {\n  min_age_seconds = 0\n}\n").unwrap();
        assert_eq!(zero.strengthen(&p).unwrap(), p);
        let longer = user("@ require {\n  min_age_seconds = 9999999\n}\n").unwrap();
        assert_eq!(
            longer.strengthen(&p).unwrap().defaults.limits.min_age,
            9_999_999
        );
    }

    #[test]
    fn a_user_policy_adds_requirements() {
        let p = project();
        let u = user(&format!(
            "{}{}@ require {{\n  observers = [\"dave\", \"al\"]\n  age_witnesses = [\"local\"]\n  min_age_seconds = 0\n  max_checkpoint_lifetime_seconds = 60\n  max_source_check_age_seconds = 999999\n}}\n",
            index("dave", 5, "https", "https://example.org/dave/index"),
            // alice, under another alias, as the project reads it.
            index("al", 1, "https", "https://example.org/alice/index"),
        ))
        .unwrap();
        let s = u.strengthen(&p).unwrap();
        stronger(&s, &p);
        assert_eq!(s.indexes.len(), 5);
        let aliases: Vec<&str> = s
            .defaults
            .observers
            .iter()
            .map(|t| t.alias.as_str())
            .collect();
        assert_eq!(aliases, ["alice", "bob", "dave"]);
        assert!(s.defaults.witnesses.contains(&Witness::Local));
        // The project's rule for its own index has local already.
        let mine = s.rule(&[0x77; 32]);
        assert_eq!(
            mine.witnesses
                .iter()
                .filter(|w| **w == Witness::Local)
                .count(),
            1
        );
        assert_eq!(s.defaults.limits.max_checkpoint_lifetime, 60);
        assert_eq!(s.defaults.limits.max_source_check_age, 3600);
    }

    #[test]
    fn a_user_policy_changes_nothing_it_does_not_add() {
        let p = project();
        // alice pinned elsewhere.
        let moved = index("alice", 1, "https", "https://example.org/alice/index")
            .replace(&"a".repeat(40), &"b".repeat(40));
        let read_elsewhere = index("alice", 1, "https", "https://example.org/alice/fork");
        let other_alice = index("alice", 9, "https", "https://example.org/alice2/index");
        for text in [moved, read_elsewhere, other_alice] {
            let u = user(&text).unwrap();
            assert!(u.strengthen(&p).is_err(), "{text}");
        }
        // carol witnesses for the project; she cannot also observe.
        let u = user(&format!(
            "{}@ require {{\n  observers = [\"c\"]\n}}\n",
            index("c", 3, "https", "https://example.org/carol/index")
        ))
        .unwrap();
        assert!(u.strengthen(&p).is_err());
        // Nor can a witness be read from an observer's repository.
        let u = user(&format!(
            "{}@ require {{\n  age_witnesses = [\"b2\"]\n}}\n",
            index("b2", 6, "https", "https://example.org/bob/index")
        ))
        .unwrap();
        assert!(u.strengthen(&p).is_err());
    }

    #[test]
    fn a_bad_user_policy_is_refused() {
        let me = index("me", 4, "local-owned", "file:///home/me/index");
        for text in [
            "format = 1\nkind = \"policy\"\ntrack = \"dependency-closure\"\n".to_string(),
            format!("{HEAD}@ require {{\n  observers = []\n}}\n"),
            format!("{HEAD}@ require {{\n  observers = [\"local\"]\n}}\n"),
            format!("{HEAD}@ require {{\n  observers = [\"nobody\"]\n}}\n"),
            format!("{HEAD}{me}@ require {{\n  age_witnesses = [\"me\"]\n}}\n"),
            format!("{HEAD}@ require {{\n  max_source_check_age_seconds = 0\n}}\n"),
            format!("{HEAD}@ require {{\n  min_age_seconds = 999999999999\n}}\n"),
            format!("{HEAD}@ require {{\n  require = \"all\"\n}}\n"),
            format!("{HEAD}@ defaults {{\n  min_age_seconds = 0\n}}\n"),
        ] {
            assert!(parse(text.as_bytes(), "trust.eure").is_err(), "{text}");
        }
        // The user's own index may observe.
        let ok = format!("{HEAD}{me}@ require {{\n  observers = [\"me\"]\n}}\n");
        assert_eq!(
            parse(ok.as_bytes(), "trust.eure").unwrap().observers.len(),
            1
        );
    }
}
