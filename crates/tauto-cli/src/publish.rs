//! `tauto index new / observe / decide / withdraw / publish`: keeping one's
//! own index, a Git repository on this machine that `Trust.eure` names as
//! `local-owned`.
//!
//! The batch being written is `observations.eure` in the repository's
//! working tree: `observe`, `decide` and `withdraw` add an event to it, each
//! checked by the core against the history so far, and `publish` commits it
//! with the two files only. Until then `git diff` shows it, and
//! `git checkout observations.eure` drops it.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use crate::i18n;
use tauto::manifest::Dependency;
use totebag::cache::Cache;
use totebag::git::Mirror;
use totebag::index::checkpoint::{self, History};
use totebag::index::ledger::{self, Batch, Event, Key, Sha256};
use totebag::index::policy::Trusted;
use totebag::index::strict::{self, hex_bytes, hex_of};
use totebag::spec::{GitSource, Rev};
use totebag_index::engine;

/// How long a batch is valid when `--valid-for` does not say: a day.
const VALID_FOR: u64 = 86_400;

pub fn command(sub: &str, tote: &Path, args: Vec<String>) -> Result<ExitCode, String> {
    let mut args = args;
    match sub {
        "new" => new(args),
        "observe" => {
            let locked = take_flag(&mut args, "--locked");
            let alias = take_value(&mut args, "--index")?;
            let target = target(tote, &mut args, true)?;
            if !args.is_empty() {
                return Err(i18n::t!(
                    "publish-not-understood",
                    command = "observe",
                    args = args.join(" ")
                ));
            }
            observe(tote, alias, target, locked)
        }
        "decide" => {
            let alias = take_value(&mut args, "--index")?;
            let rev = take_value(&mut args, "--rev")?;
            let reason = take_value(&mut args, "--reason")?
                .ok_or_else(|| i18n::t!("publish-needs-reason", command = "decide"))?;
            let target = target(tote, &mut args, false)?;
            let accept = match <[String; 1]>::try_from(args).as_ref().map(|[v]| v.as_str()) {
                Ok("accept") => true,
                Ok("reject") => false,
                _ => return Err(i18n::t!("publish-decide-takes")),
            };
            judge(tote, alias, target, rev, |key| Event::Decision {
                key,
                accept,
                reason: reason.clone(),
            })
        }
        "withdraw" => {
            let alias = take_value(&mut args, "--index")?;
            let rev = take_value(&mut args, "--rev")?;
            let reason = take_value(&mut args, "--reason")?
                .ok_or_else(|| i18n::t!("publish-needs-reason", command = "withdraw"))?;
            let target = target(tote, &mut args, false)?;
            if !args.is_empty() {
                return Err(i18n::t!(
                    "publish-not-understood",
                    command = "withdraw",
                    args = args.join(" ")
                ));
            }
            judge(tote, alias, target, rev, |key| Event::Withdrawal {
                key,
                reason: reason.clone(),
            })
        }
        "publish" => {
            let alias = take_value(&mut args, "--index")?;
            let valid_for = match take_value(&mut args, "--valid-for")? {
                Some(s) => s
                    .parse::<u64>()
                    .ok()
                    .filter(|n| *n > 0)
                    .and_then(|n| strict::seconds(n).ok())
                    .ok_or_else(|| i18n::t!("publish-valid-for", value = &s))?,
                None => VALID_FOR,
            };
            if !args.is_empty() {
                return Err(i18n::t!("publish-no-name"));
            }
            publish(tote, alias, valid_for)
        }
        _ => unreachable!("dispatched by index::command"),
    }
}

/// What an event is about: a Git dependency of the tote by NAME, or a
/// project by `--project ID` (with `--git URL` and a branch or tag, for a
/// commit not yet a dependency).
struct Target {
    label: String,
    project: Sha256,
    source: Option<GitSource>,
}

fn target(tote: &Path, args: &mut Vec<String>, with_git: bool) -> Result<Target, String> {
    let project = take_value(args, "--project")?;
    let (git, branch, tag) = if with_git {
        (
            take_value(args, "--git")?,
            take_value(args, "--branch")?,
            take_value(args, "--tag")?,
        )
    } else {
        (None, None, None)
    };
    let Some(project) = project else {
        if git.is_some() || branch.is_some() || tag.is_some() {
            return Err(i18n::t!("publish-git-needs-project"));
        }
        if args.is_empty() {
            return Err(i18n::t!("publish-name-target"));
        }
        let name = args.remove(0);
        let (project, source) = project_of(tote, &name)?;
        return Ok(Target {
            label: name,
            project,
            source: Some(source),
        });
    };
    let id = strict::sha256(&project).map_err(|e| format!("--project: {e}"))?;
    let source = match git {
        Some(url) => {
            let reference = match (branch, tag) {
                (Some(_), Some(_)) => return Err(i18n::t!("publish-branch-or-tag")),
                (Some(b), _) => format!("refs/heads/{b}"),
                (_, Some(t)) => format!("refs/tags/{t}"),
                _ => totebag::git::default_branch(&url)?,
            };
            let source = GitSource {
                url,
                reference,
                dir: String::new(),
                project: Some(project.clone()),
            };
            source.check()?;
            Some(source)
        }
        None if branch.is_some() || tag.is_some() => {
            return Err(i18n::t!("publish-branch-tag-need-git"));
        }
        None => None,
    };
    Ok(Target {
        label: format!("project {}", &project[..project.len().min(19)]),
        project: id,
        source,
    })
}

fn take_value(args: &mut Vec<String>, flag: &str) -> Result<Option<String>, String> {
    match args.iter().position(|a| a == flag) {
        Some(i) if i + 1 < args.len() => {
            let v = args.remove(i + 1);
            args.remove(i);
            Ok(Some(v))
        }
        Some(_) => Err(i18n::t!("publish-needs-value", flag = flag)),
        None => Ok(None),
    }
}

fn take_flag(args: &mut Vec<String>, flag: &str) -> bool {
    let before = args.len();
    args.retain(|a| a != flag);
    args.len() != before
}

fn one(args: Vec<String>, what: &str) -> Result<String, String> {
    <[String; 1]>::try_from(args)
        .map(|[a]| a)
        .map_err(|_| i18n::t!("publish-usage", what = what))
}

fn git(dir: &Path, args: &[&str]) -> Result<String, String> {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .map_err(|e| i18n::t!("publish-git-not-run", error = e.to_string()))?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
    } else {
        Err(format!(
            "git {}: {}",
            args.join(" "),
            String::from_utf8_lossy(&out.stderr).trim()
        ))
    }
}

/// `tauto index new DIR [--name NAME]`: a new index with its empty root.
fn new(mut args: Vec<String>) -> Result<ExitCode, String> {
    let name = take_value(&mut args, "--name")?;
    let dir = PathBuf::from(one(args, "new DIR [--name NAME]")?);
    if dir.exists()
        && std::fs::read_dir(&dir)
            .map_err(|e| format!("{}: {e}", dir.display()))?
            .next()
            .is_some()
    {
        return Err(i18n::t!(
            "publish-not-empty",
            path = dir.display().to_string()
        ));
    }
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let dir = dir
        .canonicalize()
        .map_err(|e| format!("{}: {e}", dir.display()))?;
    let name = match name {
        Some(n) => n,
        None => dir
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "index".into()),
    };
    let config = format!(
        "format = 1\nkind = \"index\"\nname = {}\nhistory = \"commit-batches\"\ngit_object_format = \"sha1\"\n",
        ledger::quote(&name)
    );
    ledger::config(config.as_bytes())?;
    let now = engine::now();
    let root = Batch {
        sequence: 0,
        issued_at: now,
        valid_until: now + VALID_FOR,
        events: Vec::new(),
    };
    git(&dir, &["init", "--quiet", "--initial-branch=main"])?;
    write(&dir.join(ledger::CONFIG_FILE), &config)?;
    write(&dir.join(ledger::BATCH_FILE), &root.render())?;
    commit(&dir, "Start the index")?;
    let own = read_own(&dir)?;
    let root = &own.history.checkpoints[0];
    let url = format!("file://{}", dir.display());
    println!(
        "{}",
        i18n::t!(
            "publish-started",
            name = &name,
            path = dir.display().to_string()
        )
    );
    println!(
        "\n{}\n\n\
         @ indexes[] {{\n  alias = \"{}\"\n  id = \"sha256:{}\"\n  transport = \"local-owned\"\n  repository = {}\n  ref = \"refs/heads/main\"\n  pin_rev = \"{}\"\n  pin_sha256 = \"sha256:{}\"\n}}",
        i18n::t!("publish-trust-hint"),
        alias_of(&name),
        hex_of(&own.history.id()),
        ledger::quote(&url),
        root.rev,
        hex_of(&root.digest)
    );
    Ok(ExitCode::SUCCESS)
}

/// An alias made from a name: lowercase letters, digits and `-`.
fn alias_of(name: &str) -> String {
    let mut a: String = name
        .to_lowercase()
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '-' })
        .collect();
    a = a.trim_matches('-').to_string();
    if !a.starts_with(|c: char| c.is_ascii_lowercase()) {
        a.insert_str(0, "index-");
    }
    a.truncate(64);
    a
}

fn write(path: &Path, text: &str) -> Result<(), String> {
    std::fs::write(path, text).map_err(|e| format!("{}: {e}", path.display()))
}

/// Commits the two files of the index in `dir`, and nothing else.
fn commit(dir: &Path, message: &str) -> Result<(), String> {
    git(dir, &["add", "--", ledger::CONFIG_FILE, ledger::BATCH_FILE])?;
    git(
        dir,
        &[
            "commit",
            "--quiet",
            "-m",
            message,
            "--",
            ledger::CONFIG_FILE,
            ledger::BATCH_FILE,
        ],
    )
    .map(|_| ())
}

/// One's own index: its repository, its history, and the batch being written.
struct Own {
    alias: String,
    dir: PathBuf,
    history: History,
    draft: Batch,
}

fn read_own(dir: &Path) -> Result<Own, String> {
    let mirror = Mirror::open(dir.join(".git"), "sha1")?;
    let head = mirror.resolve("HEAD")?;
    let history = checkpoint::history(&mirror, &head)?;
    let last = &history.checkpoints[history.checkpoints.len() - 1];
    let committed = git(dir, &["show", &format!("HEAD:{}", ledger::BATCH_FILE)])?;
    let file = dir.join(ledger::BATCH_FILE);
    let text = std::fs::read(&file).map_err(|e| format!("{}: {e}", file.display()))?;
    let draft = if String::from_utf8_lossy(&text).trim() == committed {
        let now = engine::now();
        Batch {
            sequence: last.batch.sequence + 1,
            issued_at: now.max(last.batch.issued_at),
            valid_until: now.max(last.batch.issued_at) + VALID_FOR,
            events: Vec::new(),
        }
    } else {
        let draft = ledger::batch(&text, &history.config.git_object_format)
            .map_err(|e| i18n::t!("publish-draft-invalid", error = e.to_string()))?;
        if draft.sequence != last.batch.sequence + 1 {
            return Err(i18n::t!(
                "publish-draft-sequence",
                path = file.display().to_string(),
                found = draft.sequence,
                next = last.batch.sequence + 1
            ));
        }
        draft
    };
    Ok(Own {
        alias: String::new(),
        dir: dir.to_path_buf(),
        history,
        draft,
    })
}

/// The index of `Trust.eure` this machine keeps: the one named, or the only
/// `local-owned` one.
fn own(tote: &Path, alias: Option<String>) -> Result<Own, String> {
    let policy = crate::index::read_policy(tote)?
        .ok_or_else(|| {
            i18n::t!(
                "publish-no-policy",
                path = tote.display().to_string(),
                file = crate::index::POLICY_FILE
            )
        })?
        .policy;
    let local: Vec<&Trusted> = policy
        .indexes
        .iter()
        .filter(|t| t.url.starts_with("file:///"))
        .collect();
    let t = match alias {
        Some(a) => local.iter().find(|t| t.alias == a).ok_or_else(|| {
            i18n::t!(
                "publish-not-local-owned",
                alias = &a,
                file = crate::index::POLICY_FILE
            )
        })?,
        None => match local.as_slice() {
            [t] => t,
            [] => {
                return Err(i18n::t!(
                    "publish-no-local-owned",
                    file = crate::index::POLICY_FILE
                ));
            }
            _ => {
                return Err(i18n::t!(
                    "publish-several-local-owned",
                    file = crate::index::POLICY_FILE,
                    aliases = local
                        .iter()
                        .map(|t| t.alias.as_str())
                        .collect::<Vec<_>>()
                        .join("|")
                ));
            }
        },
    };
    let mut own = read_own(Path::new(&t.url["file://".len()..]))?;
    if own.history.id() != t.index {
        return Err(i18n::t!(
            "publish-wrong-index",
            path = own.dir.display().to_string(),
            id = hex_of(&own.history.id()),
            alias = &t.alias
        ));
    }
    own.alias = t.alias.clone();
    Ok(own)
}

impl Own {
    /// Adds `event` to the batch being written, when the core allows it.
    fn add(&mut self, event: Event) -> Result<(), String> {
        // The batch is issued no earlier than what it records was seen.
        let now = engine::now();
        if now > self.draft.issued_at {
            self.draft.valid_until += now - self.draft.issued_at;
            self.draft.issued_at = now;
        }
        self.draft.events.push(event);
        engine::check_next(&self.history, &self.draft)?;
        write(&self.dir.join(ledger::BATCH_FILE), &self.draft.render())
    }

    /// Every event of the index, oldest first, the batch being written last.
    fn events(&self) -> impl Iterator<Item = &Event> {
        self.history
            .checkpoints
            .iter()
            .flat_map(|c| &c.batch.events)
            .chain(&self.draft.events)
    }
}

/// The project of the Git dependency `name` of the tote.
fn project_of(tote: &Path, name: &str) -> Result<(Sha256, GitSource), String> {
    let manifest = tauto::manifest::read(tote)?;
    match manifest.dependencies.iter().find(|(n, _)| n == name) {
        Some((_, Dependency::Git(source))) => match source.project_id() {
            Some(p) => Ok((p, source.clone())),
            None => Err(i18n::t!("publish-no-project", name = name)),
        },
        Some(_) => Err(i18n::t!("publish-not-git", name = name)),
        None => Err(i18n::t!(
            "publish-not-dependency",
            name = name,
            package = &manifest.package.name
        )),
    }
}

fn observe(
    tote: &Path,
    alias: Option<String>,
    target: Target,
    locked: bool,
) -> Result<ExitCode, String> {
    let mut own = own(tote, alias)?;
    let label = &target.label;
    let (rev, id) = if locked {
        let lock = totebag::lock::read(tote)?.unwrap_or_default();
        let l = lock
            .get(label)
            .ok_or_else(|| i18n::t!("publish-not-locked", name = label))?;
        (l.rev.clone(), l.id.clone())
    } else {
        let source = target
            .source
            .as_ref()
            .ok_or_else(|| i18n::t!("publish-observe-what"))?;
        let cache = Cache::from_env()?;
        eprintln!(
            "{}",
            i18n::t!(
                "publish-fetching",
                url = &source.url,
                reference = &source.reference
            )
        );
        let f = totebag::fetch_head(&cache, source)?;
        (f.rev, f.id)
    };
    own.add(Event::Observation {
        key: Key {
            project: target.project,
            rev: rev.hex().to_string(),
        },
        source: hex_bytes(id.hex()),
        first_seen_at: engine::now(),
    })?;
    println!(
        "{}",
        i18n::t!(
            "publish-observed",
            name = label,
            rev = rev.short().to_string(),
            source = id.short().to_string(),
            alias = &own.alias
        )
    );
    Ok(ExitCode::SUCCESS)
}

/// Adds a decision or a withdrawal on a revision of the target: `rev`, or the one
/// the index observed last.
fn judge(
    tote: &Path,
    alias: Option<String>,
    target: Target,
    rev: Option<String>,
    event: impl FnOnce(Key) -> Event,
) -> Result<ExitCode, String> {
    let (project, name) = (target.project, target.label.as_str());
    let mut own = own(tote, alias)?;
    let rev = match rev {
        Some(r) => Rev::parse(&r)
            .or_else(|_| Rev::from_git(&r))
            .map(|r| r.hex().to_string())
            .unwrap_or(r),
        None => own
            .events()
            .filter_map(|e| match e {
                Event::Observation { key, .. } if key.project == project => Some(key.rev.clone()),
                _ => None,
            })
            .last()
            .ok_or_else(|| i18n::t!("publish-not-observed", alias = &own.alias, name = name))?,
    };
    let event = event(Key { project, rev });
    let what = match &event {
        Event::Decision { accept: true, .. } => "accepted",
        Event::Decision { .. } => "rejected",
        _ => "withdrew",
    };
    let shown = match &event {
        Event::Decision { key, .. } | Event::Withdrawal { key, .. } => key.rev.clone(),
        _ => unreachable!(),
    };
    own.add(event)?;
    println!(
        "{}",
        i18n::t!(
            "publish-judged",
            what = what,
            name = name,
            rev = &shown[..shown.len().min(12)],
            alias = &own.alias
        )
    );
    Ok(ExitCode::SUCCESS)
}

fn publish(tote: &Path, alias: Option<String>, valid_for: u64) -> Result<ExitCode, String> {
    let mut own = own(tote, alias)?;
    let last = &own.history.checkpoints[own.history.checkpoints.len() - 1];
    let now = engine::now();
    own.draft.issued_at = now.max(last.batch.issued_at);
    own.draft.valid_until = own.draft.issued_at + valid_for;
    engine::check_next(&own.history, &own.draft)?;
    write(&own.dir.join(ledger::BATCH_FILE), &own.draft.render())?;
    let n = own.draft.events.len();
    commit(&own.dir, &format!("Batch {}", own.draft.sequence))?;
    let head = Mirror::open(own.dir.join(".git"), "sha1")?.resolve("HEAD")?;
    println!(
        "{}",
        i18n::t!(
            "publish-published",
            sequence = own.draft.sequence,
            alias = &own.alias,
            rev = head.short().to_string(),
            n = n,
            until = strict::time_text(own.draft.valid_until)
        )
    );
    Ok(ExitCode::SUCCESS)
}
