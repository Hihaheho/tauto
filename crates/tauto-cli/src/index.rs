//! `tauto index`: the indexes a project's `Trust.eure` trusts, taken into
//! this machine's protected state; and the gate `add`, `update` and `lock`
//! pass a new commit through when the project has a policy. The project's
//! policy is strengthened by the user's own, or by the safe default when the
//! user has none.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use totebag::index::ledger::{Key, Sha256};
use totebag::index::policy::{self, Policy, Rule};
use totebag::index::state::{Held, Store};
use totebag::index::strict::{hex_bytes, hex_of, time_text};
use totebag::index::user::{self, UserPolicy};
use totebag::lock::Locked;
use totebag_index::engine::{self, Synced};
use totebag_index::explain::{explain, span};

/// The trust policy beside a project's `Tauto.eure`.
pub const POLICY_FILE: &str = "Trust.eure";

const USER_POLICY_VAR: &str = "TAUTO_USER_TRUST";

fn help() -> String {
    crate::i18n::t!("index-help")
}

pub fn command(args: &[String]) -> ExitCode {
    if args.is_empty() || args.iter().any(|a| a == "--help" || a == "-h") {
        println!("{}", help());
        return if args.is_empty() {
            ExitCode::FAILURE
        } else {
            ExitCode::SUCCESS
        };
    }
    let mut args = args.to_vec();
    let sub = args.remove(0);
    let tote = match take_tote(&mut args) {
        Ok(t) => t,
        Err(e) => return usage(&e),
    };
    let result = match sub.as_str() {
        "sync" if args.is_empty() => sync(&tote),
        "status" if args.is_empty() => status(&tote),
        "check" => check(&tote, &args),
        "new" | "observe" | "decide" | "withdraw" | "publish" => {
            crate::publish::command(&sub, &tote, args)
        }
        "sync" | "status" => {
            return usage(&crate::i18n::t!("index-takes-no-argument", command = &sub));
        }
        _ => return usage(&crate::i18n::t!("index-unknown-command", command = &sub)),
    };
    match result {
        Ok(code) => code,
        Err(e) => {
            eprintln!(
                "{}",
                crate::i18n::t!("index-command-error", command = &sub, error = e)
            );
            ExitCode::FAILURE
        }
    }
}

fn usage(error: &str) -> ExitCode {
    eprintln!(
        "{}\n\n{}",
        crate::i18n::t!("index-usage-error", error = error),
        help()
    );
    ExitCode::from(2)
}

fn take_tote(args: &mut Vec<String>) -> Result<PathBuf, String> {
    match args.iter().position(|a| a == "--tote") {
        Some(i) if i + 1 < args.len() => {
            let dir = args.remove(i + 1);
            args.remove(i);
            Ok(PathBuf::from(dir))
        }
        Some(_) => Err(crate::i18n::t!("index-tote-needs-dir")),
        None => Ok(PathBuf::from(".")),
    }
}

pub enum UserSource {
    File(PathBuf),
    /// There is none, at this path if one could be there.
    Default(Option<PathBuf>),
}

impl UserSource {
    fn describe(&self) -> String {
        match self {
            UserSource::File(f) => f.display().to_string(),
            UserSource::Default(Some(f)) => {
                crate::i18n::t!("index-user-default-no-file", path = f.display().to_string())
            }
            UserSource::Default(None) => crate::i18n::t!("index-user-default"),
        }
    }
}

/// A project's policy and what the user's strengthens it to.
pub struct Trust {
    /// The project's policy strengthened: what adopting requires here.
    pub policy: Policy,
    pub project: Policy,
    pub user: UserSource,
}

/// The user policy file: $TAUTO_USER_TRUST, else
/// $XDG_CONFIG_HOME/tauto/trust.eure, else ~/.config/tauto/trust.eure; and
/// whether it was named by the variable.
fn user_policy_file() -> (Option<PathBuf>, bool) {
    let var = |k: &str| {
        std::env::var_os(k)
            .filter(|v| !v.is_empty())
            .map(PathBuf::from)
    };
    if let Some(f) = var(USER_POLICY_VAR) {
        return (Some(f), true);
    }
    let dir = var("XDG_CONFIG_HOME").or_else(|| var("HOME").map(|h| h.join(".config")));
    (dir.map(|d| d.join("tauto/trust.eure")), false)
}

fn read_user() -> Result<(UserPolicy, UserSource), String> {
    let (file, named) = user_policy_file();
    let Some(file) = file else {
        return Ok((UserPolicy::default(), UserSource::Default(None)));
    };
    match std::fs::read(&file) {
        Ok(bytes) => Ok((
            user::parse(&bytes, &file.display().to_string())?,
            UserSource::File(file),
        )),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound && !named => {
            Ok((UserPolicy::default(), UserSource::Default(Some(file))))
        }
        Err(e) => Err(crate::i18n::t!(
            "index-file-error",
            path = file.display().to_string(),
            error = e.to_string()
        )),
    }
}

/// The policy of the project in `tote`, if it has one, strengthened by the
/// user's.
pub fn read_policy(tote: &Path) -> Result<Option<Trust>, String> {
    let file = tote.join(POLICY_FILE);
    let project = match std::fs::read(&file) {
        Ok(bytes) => policy::parse(&bytes, &file.display().to_string())?,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => {
            return Err(crate::i18n::t!(
                "index-file-error",
                path = file.display().to_string(),
                error = e.to_string()
            ));
        }
    };
    let (user, source) = read_user()?;
    let policy = user.strengthen(&project).map_err(|e| {
        crate::i18n::t!(
            "index-strengthen-error",
            path = file.display().to_string(),
            user = source.describe(),
            error = e.to_string()
        )
    })?;
    Ok(Some(Trust {
        policy,
        project,
        user: source,
    }))
}

fn need_policy(tote: &Path) -> Result<Trust, String> {
    read_policy(tote)?.ok_or_else(|| {
        crate::i18n::t!(
            "index-trusts-no-index",
            dir = tote.display().to_string(),
            file = POLICY_FILE
        )
    })
}

/// Syncs `t`, saying how it went: on stdout as a line of `tauto index sync`,
/// or, `quiet`, on stderr and only when it went wrong.
fn sync_one(store: &Store, held: &mut Held, t: &policy::Trusted, now: u64, quiet: bool) -> bool {
    if quiet {
        eprintln!("{}", crate::i18n::t!("index-syncing", alias = &t.alias));
    } else {
        eprintln!(
            "{}",
            crate::i18n::t!(
                "index-syncing-from",
                alias = &t.alias,
                url = t.url.to_string(),
                reference = t.reference.to_string()
            )
        );
    }
    let (ok, line) = match engine::sync(store, held, t, now) {
        Ok(Synced::Open { head, taken }) => {
            let what = match taken {
                0 => crate::i18n::t!("index-sync-nothing-new"),
                n => crate::i18n::t!("index-sync-new-batches", n = n as u64),
            };
            (true, format!("{}  {what}", head.rev.short()))
        }
        Ok(Synced::Frozen { prefix, why }) => (
            false,
            format!(
                "{}  {}",
                prefix.rev.short(),
                crate::i18n::t!("index-stopped", why = why.to_string())
            ),
        ),
        Err(e) => (false, e),
    };
    if !quiet {
        println!("{:<12} {line}", t.alias);
    } else if !ok {
        eprintln!(
            "{}",
            crate::i18n::t!("index-sync-failed", alias = &t.alias, line = line)
        );
    }
    ok
}

fn sync(tote: &Path) -> Result<ExitCode, String> {
    let policy = need_policy(tote)?.policy;
    let store = Store::from_env()?;
    let mut held = store.hold()?;
    let now = engine::now();
    let mut all = true;
    for t in policy_indexes(&policy) {
        all &= sync_one(&store, &mut held, t, now, false);
    }
    held.save()?;
    Ok(if all {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    })
}

fn policy_indexes(policy: &Policy) -> Vec<&policy::Trusted> {
    let mut used: Vec<&policy::Trusted> = Vec::new();
    for rule in std::iter::once(&policy.defaults).chain(policy.rules.iter().map(|(_, r)| r)) {
        for t in rule.indexes() {
            if !used.iter().any(|u| u.index == t.index) {
                used.push(t);
            }
        }
    }
    used
}

fn requires(rule: &Rule) -> String {
    let names = |ts: Vec<&str>| ts.join(", ");
    let witnesses = rule
        .witnesses
        .iter()
        .map(|w| match w {
            policy::Witness::Local => "local",
            policy::Witness::Remote(t) => t.alias.as_str(),
        })
        .collect();
    crate::i18n::t!(
        "index-requires",
        observers = names(rule.observers.iter().map(|t| t.alias.as_str()).collect()),
        witnesses = names(witnesses),
        wait = span(rule.limits.min_age),
        lifetime = span(rule.limits.max_checkpoint_lifetime),
        check = span(rule.limits.max_source_check_age),
    )
}

fn status(tote: &Path) -> Result<ExitCode, String> {
    let trust = need_policy(tote)?;
    let policy = &trust.policy;
    println!(
        "{}",
        crate::i18n::t!("index-status-user", policy = trust.user.describe())
    );
    println!(
        "{}",
        crate::i18n::t!("index-status-every", requires = requires(&policy.defaults))
    );
    for (p, rule) in &policy.rules {
        println!(
            "{}",
            crate::i18n::t!(
                "index-status-project",
                project = &hex_of(p)[..12],
                requires = requires(rule)
            )
        );
    }
    println!();
    let store = Store::from_env()?;
    let held = store.hold()?;
    let now = engine::now();
    for t in policy_indexes(policy) {
        println!("{} ({} {})", t.alias, t.url, t.reference);
        let Some(l) = held.state.ledger(&t.index) else {
            println!("  {}", crate::i18n::t!("index-status-not-taken"));
            continue;
        };
        println!(
            "  {}",
            crate::i18n::t!("index-status-taken", rev = l.prefix.rev.short().to_string())
        );
        println!(
            "  {}",
            crate::i18n::t!("index-status-pinned", rev = l.pin.rev.short().to_string())
        );
        match &l.checked {
            Some(c) if c.at <= now => println!(
                "  {}",
                crate::i18n::t!(
                    "index-status-checked-ago",
                    ago = span(now - c.at),
                    rev = c.head.rev.short().to_string()
                )
            ),
            Some(c) => println!(
                "  {}",
                crate::i18n::t!(
                    "index-status-checked-future",
                    time = time_text(c.at).to_string()
                )
            ),
            None => println!("  {}", crate::i18n::t!("index-status-checked-never")),
        }
        if let Some(why) = &l.frozen {
            println!(
                "  {}",
                crate::i18n::t!("index-stopped", why = why.to_string())
            );
        }
    }
    Ok(ExitCode::SUCCESS)
}

fn check(tote: &Path, names: &[String]) -> Result<ExitCode, String> {
    let lock = totebag::lock::read(tote)?.unwrap_or_default();
    let Some(mut gate) = Gate::open(tote, false)? else {
        return Err(crate::i18n::t!(
            "index-no-policy",
            dir = tote.display().to_string(),
            file = POLICY_FILE
        ));
    };
    let mut all = true;
    for l in &lock.totes {
        if !names.is_empty() && !names.contains(&l.name) {
            continue;
        }
        match gate.admit(l)? {
            Ok(()) => println!(
                "{:<12} {}  {}",
                l.name,
                l.rev.short(),
                crate::i18n::t!("index-may-adopt")
            ),
            Err(why) => {
                all = false;
                println!(
                    "{:<12} {}  {}",
                    l.name,
                    l.rev.short(),
                    crate::i18n::t!("index-may-not-adopt")
                );
                for w in why {
                    println!("  {w}");
                }
            }
        }
    }
    for n in names {
        if lock.get(n).is_none() {
            return Err(crate::i18n::t!("index-not-locked", name = n));
        }
    }
    Ok(if all {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    })
}

/// What `add`, `update` and `lock` ask before writing a new commit into
/// `Tauto.lock`, when the project has a policy.
pub struct Gate {
    trust: Trust,
    store: Store,
    held: Held,
    /// Whether to sync the indexes a rule names before its first answer.
    sync: bool,
    synced: BTreeSet<Sha256>,
}

impl Gate {
    /// The gate of the project in `tote`; `None` when it has no policy.
    pub fn open(tote: &Path, sync: bool) -> Result<Option<Gate>, String> {
        let Some(trust) = read_policy(tote)? else {
            return Ok(None);
        };
        let store = Store::from_env()?;
        let held = store.hold()?;
        Ok(Some(Gate {
            trust,
            store,
            held,
            sync,
            synced: BTreeSet::new(),
        }))
    }

    /// Whether `locked` may be adopted now; if not, why. The time of the
    /// answer is kept, whatever the answer.
    pub fn admit(&mut self, locked: &Locked) -> Result<Result<(), Vec<String>>, String> {
        let Some(project) = locked.source.project_id() else {
            return Err(crate::i18n::t!(
                "index-needs-project",
                name = &locked.name,
                file = POLICY_FILE
            ));
        };
        let rule: Rule = self.trust.policy.rule(&project).clone();
        let now = engine::now();
        if self.sync {
            for t in rule.indexes() {
                if self.synced.insert(t.index) {
                    sync_one(&self.store, &mut self.held, t, now, true);
                }
            }
        }
        let key = Key {
            project,
            rev: locked.rev.hex().to_string(),
        };
        let source: Sha256 = hex_bytes(locked.id.hex());
        let yes = engine::evaluate(&self.store, &mut self.held, &rule, now, &key, &source);
        self.held.save()?;
        if yes? {
            Ok(Ok(()))
        } else {
            let mut why = explain(&self.store, &self.held.state, &rule, now, &key, &source);
            if why.is_empty() {
                why.push(crate::i18n::t!("index-not-allowed"));
            }
            let own = self.trust.project.rule(&project).limits.min_age;
            if rule.limits.min_age > own {
                why.push(crate::i18n::t!(
                    "index-wait-from",
                    wait = span(rule.limits.min_age),
                    user = self.trust.user.describe(),
                    file = POLICY_FILE,
                    own = span(own)
                ));
            }
            Ok(Err(why))
        }
    }
}
