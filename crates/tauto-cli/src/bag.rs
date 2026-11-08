//! Totebag's commands: the totes a tote depends on, fetched from Git and
//! fixed in `Tauto.lock`.
//!
//! `add` and `remove` change `Tauto.eure` and the lock together; `update` and
//! `lock` change only the lock; `fetch` and `deps` change neither. A new commit
//! is taken only by `add`, `update` or `lock`, never by `check`, `run` or
//! `build`, which read the lock and fetch only what it fixes.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use tauto::manifest::Dependency;
use totebag::cache::Cache;
use totebag::lock::{Lock, Locked};
use totebag::spec::GitSource;

use crate::i18n;

pub fn command(name: &str, args: &[String]) -> ExitCode {
    if args.iter().any(|a| a == "--help" || a == "-h") {
        println!("{}", i18n::t!("bag-help"));
        return ExitCode::SUCCESS;
    }
    let mut args = args.to_vec();
    let tote = match take_value(&mut args, "--tote") {
        Ok(t) => PathBuf::from(t.unwrap_or_else(|| ".".into())),
        Err(e) => return usage(&e),
    };
    let result = match name {
        "add" => add(&tote, args),
        "remove" => remove(&tote, args),
        "update" => update(&tote, args),
        "lock" => lock(&tote, args),
        "fetch" => fetch(&tote, args),
        "deps" => deps(&tote, args),
        "audit" => totes(&tote).and_then(|t| crate::audit::audit(args, &t)),
        _ => return usage(&i18n::t!("bag-unknown-command", name = name)),
    };
    match result {
        Ok(code) => code,
        Err(Problem::Usage(e)) => usage(&e),
        Err(Problem::Failed(e)) => {
            eprintln!("{}", i18n::t!("bag-failed", name = name, error = e));
            ExitCode::FAILURE
        }
    }
}

pub(crate) enum Problem {
    Usage(String),
    Failed(String),
}

impl From<String> for Problem {
    fn from(e: String) -> Problem {
        Problem::Failed(e)
    }
}

impl From<tauto_message::Message> for Problem {
    fn from(e: tauto_message::Message) -> Problem {
        Problem::Failed(e.to_string())
    }
}

fn usage(error: &str) -> ExitCode {
    eprintln!("{error}\n{}", i18n::t!("bag-help"));
    ExitCode::from(2)
}

/// Removes `flag VALUE` from `args`, and gives the value.
fn take_value(args: &mut Vec<String>, flag: &str) -> Result<Option<String>, String> {
    let Some(at) = args.iter().position(|a| a == flag) else {
        return Ok(None);
    };
    match args.get(at + 1) {
        Some(v) if !v.starts_with("--") => {
            let v = v.clone();
            args.drain(at..at + 2);
            Ok(Some(v))
        }
        _ => Err(i18n::t!("bag-needs-value", flag = flag)),
    }
}

fn take_flag(args: &mut Vec<String>, flag: &str) -> bool {
    match args.iter().position(|a| a == flag) {
        Some(at) => {
            args.remove(at);
            true
        }
        None => false,
    }
}

/// What is left: names, and no unknown flag.
fn names(args: Vec<String>) -> Result<Vec<String>, Problem> {
    if let Some(flag) = args.iter().find(|a| a.starts_with('-')) {
        return Err(Problem::Usage(i18n::t!("bag-unknown-option", flag = flag)));
    }
    Ok(args)
}

fn manifest_of(tote: &Path) -> Result<(PathBuf, String), String> {
    let file = tote.join("Tauto.eure");
    let text = std::fs::read_to_string(&file)
        .map_err(|_| i18n::t!("bag-no-manifest", dir = tote.display().to_string()))?;
    Ok((file, text))
}

fn short_url(url: &str) -> &str {
    url.strip_prefix("https://").unwrap_or(url)
}

fn add(tote: &Path, mut args: Vec<String>) -> Result<ExitCode, Problem> {
    let git = take_value(&mut args, "--git").map_err(Problem::Usage)?;
    let path = take_value(&mut args, "--path").map_err(Problem::Usage)?;
    let branch = take_value(&mut args, "--branch").map_err(Problem::Usage)?;
    let tag = take_value(&mut args, "--tag").map_err(Problem::Usage)?;
    let dir = take_value(&mut args, "--dir").map_err(Problem::Usage)?;
    let project = take_value(&mut args, "--project").map_err(Problem::Usage)?;
    let mut rest = names(args)?;
    if rest.len() > 1 {
        return Err(Problem::Usage(i18n::t!("bag-add-one-name")));
    }
    let name = rest.pop();
    if let Some(n) = &name
        && !totebag::valid_name(n)
    {
        return Err(Problem::Failed(i18n::t!("bag-bad-name", name = n)));
    }
    let (file, text) = manifest_of(tote)?;
    let manifest = tauto::manifest::read(tote)?;
    let already = |name: &str| Problem::Failed(i18n::t!("bag-already", name = name));
    if let Some(n) = &name
        && manifest.dependencies.iter().any(|(d, _)| d == n)
    {
        return Err(already(n));
    }
    let mut seed = None;
    let (name, dependency) = match (git, path) {
        (Some(url), None) => {
            if branch.is_some() && tag.is_some() {
                return Err(Problem::Usage(i18n::t!("bag-branch-and-tag")));
            }
            totebag::spec::check_url(&url)?;
            let reference = match (branch, tag) {
                (Some(b), _) => format!("refs/heads/{b}"),
                (_, Some(t)) => format!("refs/tags/{t}"),
                _ => totebag::git::default_branch(&url)?,
            };
            totebag::spec::check_ref(&reference)?;
            let cache = Cache::from_env()?;
            let whole = GitSource {
                url: url.clone(),
                reference,
                dir: String::new(),
                project,
            };
            whole.check()?;
            eprintln!(
                "{}",
                i18n::t!(
                    "bag-fetching-ref",
                    what = short_url(&url),
                    reference = &whole.reference
                )
            );
            let fetched = totebag::fetch_head(&cache, &whole)?;
            let root = cache.source_dir(&fetched.id);
            let dir = choose_dir(&root, &url, dir, name.as_deref())?;
            let found = tauto::manifest::read(&root.join(&dir))?;
            let name = name.unwrap_or(found.package.name);
            let source = GitSource { dir, ..whole };
            seed = Some(Locked {
                name: name.clone(),
                source: source.clone(),
                rev: fetched.rev,
                id: fetched.id,
            });
            (name, Dependency::Git(source))
        }
        (None, Some(path)) => {
            if branch.is_some() || tag.is_some() || dir.is_some() || project.is_some() {
                return Err(Problem::Usage(i18n::t!("bag-git-only-flags")));
            }
            let found = tauto::manifest::read(&tote.join(&path)).map_err(|_| {
                i18n::t!(
                    "bag-path-no-manifest",
                    path = &path,
                    from = tote.display().to_string()
                )
            })?;
            (name.unwrap_or(found.package.name), Dependency::Path(path))
        }
        _ => return Err(Problem::Usage(i18n::t!("bag-add-needs-source"))),
    };
    if name == manifest.package.name {
        return Err(Problem::Failed(i18n::t!("bag-self", name = &name)));
    }
    if manifest.dependencies.iter().any(|(n, _)| *n == name) {
        return Err(already(&name));
    }
    let edited = edit::insert(&text, &entry(&name, &dependency))?;
    tauto::manifest::parse(&edited, &file)
        .map_err(|e| i18n::t!("bag-edit-unreadable", error = e.to_string()))?;
    std::fs::write(&file, &edited).map_err(|e| format!("{}: {e}", file.display()))?;
    let resolved = resolve(tote, &Update::Missing, seed).and_then(|r| {
        r.write(tote)?;
        Ok(r)
    });
    match resolved {
        Ok(r) => {
            println!(
                "{}",
                i18n::t!("bag-added", name = &name, file = file.display().to_string())
            );
            r.report(false);
            // What the new dependency adds to `tauto`: its commands, which
            // the host denies everything until trust.commands grants it.
            let given = tauto::manifest::dependency_dir(tote, &name, &dependency)
                .map(|dir| crate::commands::given(&dir))
                .unwrap_or_default();
            if !given.is_empty() {
                println!(
                    "{}\n{}",
                    i18n::t!("bag-gives-commands", name = &name),
                    given.join("\n")
                );
            }
            Ok(ExitCode::SUCCESS)
        }
        Err(e) => {
            // The manifest is as it was when the dependency cannot be locked.
            let _ = std::fs::write(&file, &text);
            Err(Problem::Failed(e))
        }
    }
}

/// The directory of the tote in a repository: the one asked for, the root,
/// the directory named after the tote, or the only tote there is.
fn choose_dir(
    root: &Path,
    url: &str,
    dir: Option<String>,
    name: Option<&str>,
) -> Result<String, String> {
    if let Some(dir) = dir {
        let dir = dir.trim_matches('/').to_string();
        totebag::spec::check_dir(&dir)?;
        if !root.join(&dir).join("Tauto.eure").is_file() {
            return Err(i18n::t!("bag-url-no-manifest-in", url = url, dir = &dir));
        }
        return Ok(dir);
    }
    if root.join("Tauto.eure").is_file() {
        return Ok(String::new());
    }
    if let Some(name) = name
        && root.join(name).join("Tauto.eure").is_file()
    {
        return Ok(name.to_string());
    }
    let mut totes = Vec::new();
    find_totes(root, root, &mut totes);
    match totes.len() {
        0 => Err(i18n::t!("bag-url-no-tote", url = url)),
        1 => Ok(totes.pop().unwrap()),
        _ => Err(i18n::t!(
            "bag-url-many-totes",
            url = url,
            n = totes.len(),
            totes = totes.join(", ")
        )),
    }
}

fn find_totes(root: &Path, dir: &Path, out: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        if !path.is_dir() {
            continue;
        }
        if path.join("Tauto.eure").is_file() {
            if let Ok(rel) = path.strip_prefix(root) {
                out.push(rel.to_string_lossy().into_owned());
            }
            // A tote's own subdirectories (its tests, its examples) are not offered.
            continue;
        }
        find_totes(root, &path, out);
    }
}

/// The entry of `dependencies` for a dependency: one line for a path, a
/// block for a Git repository (Eure has no `,` between bindings).
fn entry(name: &str, dependency: &Dependency) -> String {
    match dependency {
        Dependency::Path(path) => format!("{name} {{ path = {path:?} }}"),
        Dependency::Git(s) => {
            let mut out = format!(
                "{name} {{\n  git = \"{}\"\n  ref = \"{}\"\n",
                s.url, s.reference
            );
            if !s.dir.is_empty() {
                out.push_str(&format!("  dir = \"{}\"\n", s.dir));
            }
            if let Some(p) = &s.project {
                out.push_str(&format!("  project = \"{p}\"\n"));
            }
            out.push('}');
            out
        }
    }
}

fn remove(tote: &Path, args: Vec<String>) -> Result<ExitCode, Problem> {
    let [name] = names(args)?
        .try_into()
        .map_err(|_| Problem::Usage(i18n::t!("bag-remove-one-name")))?;
    let (file, text) = manifest_of(tote)?;
    let manifest = tauto::manifest::read(tote)?;
    if !manifest.dependencies.iter().any(|(n, _)| *n == name) {
        return Err(Problem::Failed(i18n::t!(
            "bag-not-dependency",
            name = &name,
            tote = &manifest.package.name
        )));
    }
    let edited = edit::remove(&text, &name)?;
    let reread = tauto::manifest::parse(&edited, &file)
        .map_err(|e| i18n::t!("bag-edit-unreadable", error = e.to_string()))?;
    if reread.dependencies.iter().any(|(n, _)| *n == name) {
        return Err(Problem::Failed(i18n::t!(
            "bag-could-not-remove",
            name = &name,
            file = file.display().to_string()
        )));
    }
    std::fs::write(&file, &edited).map_err(|e| format!("{}: {e}", file.display()))?;
    let resolved = resolve(tote, &Update::Missing, None).and_then(|r| {
        r.write(tote)?;
        Ok(r)
    });
    match resolved {
        Ok(r) => {
            println!(
                "{}",
                i18n::t!(
                    "bag-removed",
                    name = &name,
                    file = file.display().to_string()
                )
            );
            r.report(false);
            Ok(ExitCode::SUCCESS)
        }
        Err(e) => {
            let _ = std::fs::write(&file, &text);
            Err(Problem::Failed(e))
        }
    }
}

fn update(tote: &Path, mut args: Vec<String>) -> Result<ExitCode, Problem> {
    let dry_run = take_flag(&mut args, "--dry-run");
    let names = names(args)?;
    let update = if names.is_empty() {
        Update::All
    } else {
        Update::Names(names.into_iter().collect())
    };
    manifest_of(tote)?;
    let r = resolve(tote, &update, None)?;
    if let Update::Names(asked) = &update {
        let known: BTreeSet<&str> = r.lock.totes.iter().map(|t| t.name.as_str()).collect();
        if let Some(missing) = asked.iter().find(|n| !known.contains(n.as_str())) {
            return Err(Problem::Failed(i18n::t!(
                "bag-not-git-dependency",
                name = missing
            )));
        }
    }
    if !dry_run {
        r.write(tote)?;
    }
    r.report(dry_run);
    Ok(ExitCode::SUCCESS)
}

fn lock(tote: &Path, mut args: Vec<String>) -> Result<ExitCode, Problem> {
    let check = take_flag(&mut args, "--check");
    names(args)?
        .is_empty()
        .then_some(())
        .ok_or_else(|| Problem::Usage(i18n::t!("bag-lock-no-name")))?;
    manifest_of(tote)?;
    if check {
        let r = resolve(tote, &Update::Offline, None)?;
        if r.changes.is_empty() {
            println!("{}", i18n::t!("bag-lock-up-to-date"));
            return Ok(ExitCode::SUCCESS);
        }
        r.report(true);
        eprintln!("{}", i18n::t!("bag-lock-not-up-to-date"));
        return Ok(ExitCode::FAILURE);
    }
    let r = resolve(tote, &Update::Missing, None)?;
    r.write(tote)?;
    r.report(false);
    Ok(ExitCode::SUCCESS)
}

fn fetch(tote: &Path, mut args: Vec<String>) -> Result<ExitCode, Problem> {
    let verify = take_flag(&mut args, "--verify");
    names(args)?
        .is_empty()
        .then_some(())
        .ok_or_else(|| Problem::Usage(i18n::t!("bag-fetch-no-name")))?;
    manifest_of(tote)?;
    let Some(lock) = totebag::lock::read(tote)? else {
        println!("{}", i18n::t!("bag-nothing-to-fetch"));
        return Ok(ExitCode::SUCCESS);
    };
    let cache = Cache::from_env()?;
    let mut code = ExitCode::SUCCESS;
    for t in &lock.totes {
        if !cache.has(&t.id) {
            if tauto::project::offline() {
                return Err(Problem::Failed(i18n::t!("bag-offline")));
            }
            eprintln!(
                "{}",
                i18n::t!(
                    "bag-fetching-rev",
                    name = &t.name,
                    rev = t.rev.short().to_string(),
                    url = short_url(&t.source.url)
                )
            );
            totebag::fetch_locked(&cache, t)?;
        }
        if verify {
            match cache.verify(&t.id) {
                Ok(()) => println!(
                    "{}",
                    i18n::t!(
                        "bag-verified",
                        name = &t.name,
                        id = t.id.short().to_string()
                    )
                ),
                Err(e) => {
                    println!("{}: {e}", t.name);
                    code = ExitCode::FAILURE;
                }
            }
        }
    }
    if !verify {
        let n = lock.totes.len();
        println!("{}", i18n::t!("bag-fetched", n = n));
    }
    Ok(code)
}

fn deps(tote: &Path, args: Vec<String>) -> Result<ExitCode, Problem> {
    names(args)?
        .is_empty()
        .then_some(())
        .ok_or_else(|| Problem::Usage(i18n::t!("bag-deps-no-name")))?;
    let manifest = tauto::manifest::read(tote)?;
    let lock = totebag::lock::read(tote)?.unwrap_or_default();
    let cache = Cache::from_env()?;
    println!("{} {}", manifest.package.name, manifest.package.version);
    let mut seen = HashSet::new();
    show(tote, &manifest, &lock, &cache, "", &mut seen);
    Ok(ExitCode::SUCCESS)
}

fn show(
    dir: &Path,
    manifest: &tauto::manifest::Manifest,
    lock: &Lock,
    cache: &Cache,
    indent: &str,
    seen: &mut HashSet<String>,
) {
    let mut dependencies = manifest.dependencies.clone();
    dependencies.sort();
    let count = dependencies.len();
    for (i, (name, dependency)) in dependencies.iter().enumerate() {
        let last = i + 1 == count;
        let (branch, more) = if last {
            ("└── ", "    ")
        } else {
            ("├── ", "│   ")
        };
        let (what, target) = match dependency {
            Dependency::Path(p) => (i18n::t!("bag-deps-path", path = p), Some(dir.join(p))),
            Dependency::Git(s) => match lock.get(name) {
                Some(l) if l.source == *s => {
                    let fetched = cache.has(&l.id);
                    (
                        if fetched {
                            i18n::t!(
                                "bag-deps-locked",
                                url = short_url(&s.url),
                                reference = &s.reference,
                                rev = l.rev.short().to_string()
                            )
                        } else {
                            i18n::t!(
                                "bag-deps-not-fetched",
                                url = short_url(&s.url),
                                reference = &s.reference,
                                rev = l.rev.short().to_string()
                            )
                        },
                        fetched.then(|| totebag::tote_dir(cache, l)),
                    )
                }
                _ => (
                    i18n::t!(
                        "bag-deps-not-locked",
                        url = short_url(&s.url),
                        reference = &s.reference
                    ),
                    None,
                ),
            },
        };
        let again = !seen.insert(name.clone());
        println!(
            "{indent}{branch}{}",
            if again {
                i18n::t!("bag-deps-entry-again", name = name, what = what)
            } else {
                i18n::t!("bag-deps-entry", name = name, what = what)
            }
        );
        if again {
            continue;
        }
        if let Some(target) = target
            && let Ok(m) = tauto::manifest::read(&target)
        {
            show(&target, &m, lock, cache, &format!("{indent}{more}"), seen);
        }
    }
}

/// The tote and every tote it depends on whose files are here, each once,
/// the tote first: name, directory and manifest.
pub(crate) fn totes(
    tote: &Path,
) -> Result<Vec<(String, PathBuf, tauto::manifest::Manifest)>, Problem> {
    let manifest = tauto::manifest::read(tote)?;
    let lock = totebag::lock::read(tote)?.unwrap_or_default();
    let cache = Cache::from_env()?;
    let mut out = vec![(manifest.package.name.clone(), tote.to_path_buf(), manifest)];
    let mut at = 0;
    while at < out.len() {
        let (dir, deps) = (out[at].1.clone(), out[at].2.dependencies.clone());
        at += 1;
        for (name, dependency) in deps {
            let target = match &dependency {
                Dependency::Path(p) => Some(dir.join(p)),
                Dependency::Git(s) => lock
                    .get(&name)
                    .filter(|l| l.source == *s && cache.has(&l.id))
                    .map(|l| totebag::tote_dir(&cache, l)),
            };
            if out.iter().any(|(n, ..)| *n == name) {
                continue;
            }
            match target.and_then(|t| tauto::manifest::read(&t).ok().map(|m| (t, m))) {
                Some((t, m)) => out.push((name, t, m)),
                None => {
                    return Err(Problem::Failed(i18n::t!("bag-not-fetched", name = &name)));
                }
            }
        }
    }
    Ok(out)
}

/// Which Git dependencies are moved to the newest commit of their ref.
enum Update {
    /// Only the ones the lock does not have, or has for another source.
    Missing,
    All,
    Names(BTreeSet<String>),
    /// None, and nothing is fetched: what is not locked is reported.
    Offline,
}

impl Update {
    fn moves(&self, name: &str) -> bool {
        match self {
            Update::All => true,
            Update::Names(names) => names.contains(name),
            Update::Missing | Update::Offline => false,
        }
    }
}

enum Change {
    Added(Locked),
    Moved(Locked, Locked),
    Removed(Locked),
    /// Not locked, found without the network.
    Unlocked(String, GitSource),
    /// Kept at the locked commit: the newer one may not be adopted yet.
    Held(Locked, Locked, Vec<String>),
}

struct Resolved {
    lock: Lock,
    changes: Vec<Change>,
    /// Whether the lock file is there and says the same.
    unchanged_file: bool,
}

impl Resolved {
    fn write(&self, tote: &Path) -> Result<(), String> {
        if self.unchanged_file {
            return Ok(());
        }
        // A tote with no Git dependency has no lock.
        if self.lock.totes.is_empty() {
            let file = tote.join(totebag::lock::FILE);
            return match std::fs::remove_file(&file) {
                Err(e) if e.kind() != std::io::ErrorKind::NotFound => {
                    Err(format!("{}: {e}", file.display()))
                }
                _ => Ok(()),
            };
        }
        totebag::lock::write(tote, &self.lock)
    }

    fn report(&self, dry_run: bool) {
        // The word that starts a line: what is done, or what would be.
        let word = |done: &str, would: &str| i18n::t!(if dry_run { would } else { done });
        if self.changes.is_empty() {
            let n = self.lock.totes.len();
            println!("{}", i18n::t!("bag-report-up-to-date", n = n));
            return;
        }
        for c in &self.changes {
            match c {
                Change::Added(l) => println!(
                    "{:<9} {} {} ({} {})",
                    word("bag-word-locked", "bag-word-lock"),
                    l.name,
                    l.rev.short(),
                    short_url(&l.source.url),
                    l.source.reference
                ),
                Change::Moved(old, new) if old.source != new.source => println!(
                    "{:<9} {} {} -> {} ({} {} -> {} {})",
                    word("bag-word-moved", "bag-word-move"),
                    new.name,
                    old.rev.short(),
                    new.rev.short(),
                    short_url(&old.source.url),
                    old.source.reference,
                    short_url(&new.source.url),
                    new.source.reference
                ),
                Change::Moved(old, new) => println!(
                    "{:<9} {} {} -> {} ({})",
                    word("bag-word-updated", "bag-word-update"),
                    new.name,
                    old.rev.short(),
                    new.rev.short(),
                    i18n::t!(
                        "bag-report-source",
                        old = old.id.short().to_string(),
                        new = new.id.short().to_string()
                    )
                ),
                Change::Removed(l) => println!(
                    "{:<9} {} {}",
                    word("bag-word-unlocked", "bag-word-unlock"),
                    l.name,
                    l.rev.short()
                ),
                Change::Held(old, new, why) => {
                    println!(
                        "{:<9} {} {} ({})",
                        word("bag-word-held", "bag-word-hold"),
                        old.name,
                        old.rev.short(),
                        i18n::t!("bag-report-held", rev = new.rev.short().to_string())
                    );
                    for w in why {
                        println!("          {w}");
                    }
                }
                Change::Unlocked(name, s) => {
                    println!(
                        "{:<9} {name} ({} {})",
                        i18n::t!("bag-word-to-lock"),
                        short_url(&s.url),
                        s.reference
                    )
                }
            }
        }
        if dry_run {
            let n = self.changes.len();
            println!("{}", i18n::t!("bag-report-dry-run", n = n));
        }
    }
}

/// The lock the manifests of the tote in `project` and of everything it
/// depends on call for, starting from the lock there is.
///
/// `seed` is a commit just fetched for a new dependency, taken as if locked,
/// so that the commit `add` looked at is the one locked.
fn resolve(project: &Path, update: &Update, seed: Option<Locked>) -> Result<Resolved, String> {
    let old = totebag::lock::read(project)?;
    let cache = Cache::from_env()?;
    let mut start = old.clone().unwrap_or_default();
    if let Some(seed) = seed {
        start.put(seed);
    }
    // A policy is asked about every new commit; `lock --check` takes none.
    let gate = match update {
        Update::Offline => None,
        _ => crate::index::Gate::open(project, !tauto::project::offline())?,
    };
    let mut r = Resolver {
        cache,
        before: old.clone().unwrap_or_default(),
        old: start,
        gate,
        held: Vec::new(),
        new: Lock::default(),
        update,
        asked: BTreeMap::new(),
        done: HashSet::new(),
        unlocked: Vec::new(),
    };
    let root = project
        .canonicalize()
        .map_err(|e| format!("{}: {e}", project.display()))?;
    r.visit(&root)?;
    let before = old.clone().unwrap_or_default();
    let unlocked: Vec<String> = r.unlocked.iter().map(|(n, _)| n.clone()).collect();
    let mut changes: Vec<Change> = totebag::lock::changes(&before, &r.new, &unlocked)
        .into_iter()
        .map(|c| match c {
            totebag::lock::Change::Added(l) => Change::Added(l),
            totebag::lock::Change::Moved(o, l) => Change::Moved(o, l),
            totebag::lock::Change::Removed(o) => Change::Removed(o),
        })
        .collect();
    for (name, s) in r.unlocked.drain(..) {
        changes.push(Change::Unlocked(name, s));
    }
    for (old, new, why) in r.held.drain(..) {
        changes.push(Change::Held(old, new, why));
    }
    let unchanged_file = changes.is_empty() && old.is_some_and(|o| o == r.new);
    // A tote with no Git dependency needs no lock file.
    let unchanged_file =
        unchanged_file || (r.new.totes.is_empty() && !project.join(totebag::lock::FILE).exists());
    Ok(Resolved {
        lock: r.new,
        changes,
        unchanged_file,
    })
}

struct Resolver<'a> {
    cache: Cache,
    before: Lock,
    /// The lock as it was, with the commit `add` fetched.
    old: Lock,
    gate: Option<crate::index::Gate>,
    /// Kept at the commit locked before, with the newer one and why.
    held: Vec<(Locked, Locked, Vec<String>)>,
    new: Lock,
    update: &'a Update,
    /// How each name was asked for, and by which tote, for a conflict's message.
    asked: BTreeMap<String, (Dependency, PathBuf, String)>,
    done: HashSet<PathBuf>,
    unlocked: Vec<(String, GitSource)>,
}

impl Resolver<'_> {
    fn visit(&mut self, dir: &Path) -> Result<(), String> {
        if !self.done.insert(dir.to_path_buf()) {
            return Ok(());
        }
        let manifest = tauto::manifest::read(dir)?;
        let fetched_tree = self.cache.tree_of(dir);
        let mut dependencies = manifest.dependencies.clone();
        dependencies.sort();
        for (name, dependency) in &dependencies {
            let target = match dependency {
                Dependency::Path(path) => {
                    let target = dir.join(path);
                    if let Some(tree) = &fetched_tree
                        && !target.canonicalize().is_ok_and(|t| t.starts_with(tree))
                    {
                        return Err(i18n::t!(
                            "bag-path-leads-out",
                            tote = &manifest.package.name,
                            name = name,
                            path = path
                        ));
                    }
                    target.canonicalize().map_err(|e| {
                        i18n::t!(
                            "bag-path-error",
                            tote = &manifest.package.name,
                            name = name,
                            path = path,
                            error = e.to_string()
                        )
                    })?
                }
                Dependency::Git(source) => {
                    if fetched_tree.is_some() && source.is_local() {
                        return Err(i18n::t!(
                            "bag-fetched-local",
                            tote = &manifest.package.name,
                            name = name
                        ));
                    }
                    match self.locked(name, source)? {
                        Some(dir) => dir,
                        None => continue,
                    }
                }
            };
            self.ask(name, dependency, &target, &manifest.package.name)?;
            let found = tauto::manifest::read(&target).map_err(|e| {
                i18n::t!(
                    "bag-dependency-of-error",
                    name = name,
                    tote = &manifest.package.name,
                    error = e
                )
            })?;
            if found.package.name != *name {
                return Err(i18n::t!(
                    "bag-wrong-name",
                    tote = &manifest.package.name,
                    name = name,
                    found = &found.package.name
                ));
            }
            self.visit(&target)?;
        }
        Ok(())
    }

    /// A project has one tote of each name: every tote that asks for a
    /// name asks for the same directory, or the same Git source.
    fn ask(
        &mut self,
        name: &str,
        dependency: &Dependency,
        target: &Path,
        by: &str,
    ) -> Result<(), String> {
        match self.asked.get(name) {
            None => {
                self.asked.insert(
                    name.to_string(),
                    (dependency.clone(), target.to_path_buf(), by.to_string()),
                );
                Ok(())
            }
            Some((first, first_target, first_by)) => {
                let same = match (first, dependency) {
                    (Dependency::Git(a), Dependency::Git(b)) => a == b,
                    (Dependency::Path(_), Dependency::Path(_)) => first_target == target,
                    _ => false,
                };
                if same {
                    return Ok(());
                }
                let shown = |d: &Dependency, t: &Path| match d {
                    Dependency::Path(_) => {
                        i18n::t!("bag-the-directory", path = t.display().to_string())
                    }
                    Dependency::Git(s) => s.to_string(),
                };
                Err(i18n::t!(
                    "bag-asked-twice",
                    name = name,
                    first_by = first_by,
                    first = shown(first, first_target),
                    by = by,
                    second = shown(dependency, target)
                ))
            }
        }
    }

    /// The directory of the Git dependency `name`, locked as the update asks;
    /// `None` when it is not locked and the network is not used.
    fn locked(&mut self, name: &str, source: &GitSource) -> Result<Option<PathBuf>, String> {
        // Locked already; asked for differently, it is reported by `ask`.
        if let Some(l) = self.new.get(name) {
            return Ok(Some(totebag::tote_dir(&self.cache, l)));
        }
        let old = self.old.get(name).filter(|l| l.source == *source).cloned();
        let report_only = matches!(self.update, Update::Offline);
        let plan = totebag::lock::plan(
            self.update.moves(name),
            report_only,
            tauto::project::offline(),
            old.is_some(),
            old.as_ref().is_some_and(|l| self.cache.has(&l.id)),
        );
        use totebag::lock::Plan;
        let locked = match (plan, old) {
            (Plan::KeepLocked, Some(l)) => l,
            (Plan::FetchLocked, Some(l)) => {
                eprintln!(
                    "{}",
                    i18n::t!(
                        "bag-fetching-rev",
                        name = name,
                        rev = l.rev.short().to_string(),
                        url = short_url(&l.source.url)
                    )
                );
                totebag::fetch_locked(&self.cache, &l)?;
                l
            }
            (Plan::KeepUnread, Some(l)) => {
                // The lock has it; what it depends on cannot be read.
                self.new.put(l);
                return Ok(None);
            }
            (Plan::LockedNotFetched, _) => {
                return Err(i18n::t!("bag-locked-not-fetched", name = name));
            }
            (Plan::ReportUnlocked, _) => {
                self.unlocked.push((name.to_string(), source.clone()));
                return Ok(None);
            }
            (Plan::NeedsNetwork, _) => return Err(i18n::t!("bag-needs-network", name = name)),
            (Plan::FetchHead, _) => {
                eprintln!(
                    "{}",
                    i18n::t!(
                        "bag-fetching-ref",
                        what = format!("{name} {}", short_url(&source.url)),
                        reference = &source.reference
                    )
                );
                let fetched = totebag::fetch_head(&self.cache, source)
                    .map_err(|e| i18n::t!("bag-dependency-error", name = name, error = e))?;
                Locked {
                    name: name.to_string(),
                    source: source.clone(),
                    rev: fetched.rev,
                    id: fetched.id,
                }
            }
            (Plan::KeepLocked | Plan::FetchLocked | Plan::KeepUnread, None) => {
                unreachable!("planned from a locked commit")
            }
        };
        let locked = self.admit(name, locked)?;
        let dir = totebag::tote_dir(&self.cache, &locked);
        self.new.put(locked);
        Ok(Some(dir))
    }

    /// `locked`, when it was locked before or the policy allows it; else the
    /// commit locked before for the same source, held; else an error.
    fn admit(&mut self, name: &str, locked: Locked) -> Result<Locked, String> {
        let Some(gate) = &mut self.gate else {
            return Ok(locked);
        };
        if self.before.get(name) == Some(&locked) {
            return Ok(locked);
        }
        let why = match gate.admit(&locked)? {
            Ok(()) => return Ok(locked),
            Err(why) => why,
        };
        let held = self
            .before
            .get(name)
            .filter(|l| l.source == locked.source)
            .cloned();
        match held {
            Some(old) => {
                if !self.cache.has(&old.id) {
                    totebag::fetch_locked(&self.cache, &old)?;
                }
                self.held.push((old.clone(), locked, why));
                Ok(old)
            }
            None => Err(i18n::t!(
                "bag-not-adopted",
                name = name,
                rev = locked.rev.short().to_string(),
                policy = crate::index::POLICY_FILE,
                why = why.join("\n  ")
            )),
        }
    }
}

/// Edits of the text of `Tauto.eure` that keep everything else as written.
mod edit {
    /// The byte ranges of the blocks `{ … }` at the top level, with the key before each.
    fn top_blocks(text: &str) -> Vec<(String, usize, usize)> {
        let bytes = text.as_bytes();
        let (mut depth, mut i) = (0usize, 0usize);
        let mut out = Vec::new();
        let mut open = None;
        while i < bytes.len() {
            match bytes[i] {
                b'"' => {
                    i += 1;
                    while i < bytes.len() && bytes[i] != b'"' {
                        if bytes[i] == b'\\' {
                            i += 1;
                        }
                        i += 1;
                    }
                }
                b'/' if bytes.get(i + 1) == Some(&b'/') => {
                    while i < bytes.len() && bytes[i] != b'\n' {
                        i += 1;
                    }
                    continue;
                }
                b'{' => {
                    if depth == 0 {
                        open = Some(i);
                    }
                    depth += 1;
                }
                b'}' => {
                    depth = depth.saturating_sub(1);
                    if depth == 0
                        && let Some(start) = open.take()
                    {
                        let key = text[..start]
                            .trim_end()
                            .rsplit(|c: char| c.is_whitespace() || c == '}')
                            .next()
                            .unwrap_or("")
                            .to_string();
                        out.push((key, start, i));
                    }
                }
                _ => {}
            }
            i += 1;
        }
        out
    }

    /// Adds `entry` as the last line of `dependencies`, making the block when
    /// there is none.
    pub fn insert(text: &str, entry: &str) -> Result<String, String> {
        let Some((_, open, close)) = top_blocks(text)
            .into_iter()
            .find(|(k, _, _)| k == "dependencies")
        else {
            let sep = if text.is_empty() || text.ends_with("\n\n") {
                ""
            } else if text.ends_with('\n') {
                "\n"
            } else {
                "\n\n"
            };
            return Ok(format!(
                "{text}{sep}dependencies {{\n{}}}\n",
                indented(entry)
            ));
        };
        let inner = &text[open + 1..close];
        let line_start = text[..close].rfind('\n').map_or(0, |n| n + 1);
        if text[line_start..close].trim().is_empty() && inner.contains('\n') {
            return Ok(format!(
                "{}{}{}",
                &text[..line_start],
                indented(entry),
                &text[line_start..]
            ));
        }
        // A block on one line is laid out again, one entry a line.
        let kept = inner.trim();
        let mut body = String::new();
        if !kept.is_empty() {
            body.push_str(&indented(kept));
        }
        body.push_str(&indented(entry));
        Ok(format!(
            "{}{{\n{body}}}{}",
            &text[..open],
            &text[close + 1..]
        ))
    }

    fn indented(lines: &str) -> String {
        lines.lines().map(|l| format!("  {l}\n")).collect()
    }

    /// Takes the entry `name { … }` out of `dependencies`, with its line.
    pub fn remove(text: &str, name: &str) -> Result<String, String> {
        let Some((_, open, close)) = top_blocks(text)
            .into_iter()
            .find(|(k, _, _)| k == "dependencies")
        else {
            return Err(crate::i18n::t!("bag-no-dependencies-block"));
        };
        let inner = &text[open + 1..close];
        for (key, start, end) in top_blocks(inner) {
            if key != name && key.trim_matches('"') != name {
                continue;
            }
            let (start, end) = (open + 1 + start, open + 1 + end);
            let key_at = text[..start].trim_end().len() - key.len();
            let line_start = text[..key_at].rfind('\n').map_or(0, |n| n + 1);
            let after = &text[end + 1..];
            let line_end = after.find('\n').map_or(text.len(), |n| end + 1 + n + 1);
            let own_line = text[line_start..key_at].trim().is_empty()
                && text[end + 1..line_end]
                    .trim()
                    .trim_start_matches(',')
                    .trim()
                    .is_empty();
            let out = if own_line {
                format!("{}{}", &text[..line_start], &text[line_end..])
            } else {
                let end = if text[end + 1..].trim_start().starts_with(',') {
                    end + 1 + text[end + 1..].find(',').unwrap() + 1
                } else {
                    end + 1
                };
                format!("{}{}", &text[..key_at], text[end..].trim_start_matches(' '))
            };
            return Ok(drop_empty_block(out));
        }
        Err(crate::i18n::t!("bag-not-in-block", name = name))
    }

    fn drop_empty_block(text: String) -> String {
        let Some((key, open, close)) = top_blocks(&text)
            .into_iter()
            .find(|(k, _, _)| k == "dependencies")
        else {
            return text;
        };
        let inner = &text[open + 1..close];
        if inner.lines().any(|l| !l.trim().is_empty()) {
            return text;
        }
        let key_at = text[..open].trim_end().len() - key.len();
        let start = text[..key_at].trim_end_matches(['\n', ' ']).len();
        let start = if start == 0 { 0 } else { start + 1 };
        let end = text[close + 1..]
            .find('\n')
            .map_or(text.len(), |n| close + 1 + n + 1);
        format!("{}{}", &text[..start], &text[end..])
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        const BASE: &str =
            "// A tote.\npackage {\n  name = \"app\" // the name\n  version = \"0.1.0\"\n}\n";

        #[test]
        fn a_block_is_made_when_there_is_none() {
            let out = insert(BASE, "text { path = \"../text\" }").unwrap();
            assert_eq!(
                out,
                format!("{BASE}\ndependencies {{\n  text {{ path = \"../text\" }}\n}}\n")
            );
        }

        #[test]
        fn an_entry_goes_last_in_the_block() {
            let text = format!(
                "{BASE}\ndependencies {{\n  // first\n  a {{ path = \"../a\" }}\n}}\n// after\n"
            );
            let out = insert(&text, "b { path = \"../b\" }").unwrap();
            assert_eq!(
                out,
                format!(
                    "{BASE}\ndependencies {{\n  // first\n  a {{ path = \"../a\" }}\n  b {{ path = \"../b\" }}\n}}\n// after\n"
                )
            );
            assert_eq!(remove(&out, "b").unwrap(), text);
            assert_eq!(
                remove(&out, "a").unwrap(),
                format!(
                    "{BASE}\ndependencies {{\n  // first\n  b {{ path = \"../b\" }}\n}}\n// after\n"
                )
            );
        }

        #[test]
        fn a_one_line_block_is_laid_out_again() {
            let text = format!("{BASE}dependencies {{ a {{ path = \"../a\" }} }}\n");
            let out = insert(&text, "b { path = \"../b\" }").unwrap();
            assert_eq!(
                out,
                format!(
                    "{BASE}dependencies {{\n  a {{ path = \"../a\" }}\n  b {{ path = \"../b\" }}\n}}\n"
                )
            );
        }

        #[test]
        fn braces_in_strings_and_comments_are_not_blocks() {
            let text = "package { name = \"a{\" } // }\ndependencies {\n  x { git = \"https://h/x}\", ref = \"refs/heads/main\" }\n  y { path = \"../y\" }\n}\n";
            assert_eq!(
                remove(text, "x").unwrap(),
                "package { name = \"a{\" } // }\ndependencies {\n  y { path = \"../y\" }\n}\n"
            );
            assert!(remove(text, "z").is_err());
        }

        #[test]
        fn a_block_entry_is_indented() {
            let out = insert(BASE, "x {\n  git = \"https://h/x\"\n}").unwrap();
            assert_eq!(
                out,
                format!("{BASE}\ndependencies {{\n  x {{\n    git = \"https://h/x\"\n  }}\n}}\n")
            );
            assert_eq!(remove(&out, "x").unwrap(), BASE);
        }

        #[test]
        fn a_multi_line_entry_is_removed_whole() {
            let text =
                "dependencies {\n  x {\n    path = \"../x\"\n  }\n  y { path = \"../y\" }\n}\n";
            assert_eq!(
                remove(text, "x").unwrap(),
                "dependencies {\n  y { path = \"../y\" }\n}\n"
            );
        }
    }
}
