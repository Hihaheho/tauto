//! `tauto NAME ARGS…`: a command a tote gives (`docs/design/commands.md`).
//!
//! A command is a program's entry with a name: the project's own, or one of
//! a tote the project depends on directly. It is checked as `tauto run`
//! checks a program and runs on the evaluator with no step limit, its output
//! written as it happens. Every argument after its name is the program's.
//! The host denies it everything but what the project's `Tauto.eure` grants
//! it in `trust.commands`; no flag widens that.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use tauto::eval::RunOptions;
use tauto::manifest::{Command, CommandTrust, Manifest};

use crate::i18n;
use crate::locate_in;

/// The commands of `tauto` itself. A tote's command of one of these names is
/// never run: the built-in one is.
pub(crate) const BUILT_IN: &[&str] = &[
    "add",
    "assumptions",
    "audit",
    "bench",
    "bind",
    "build",
    "check",
    "deps",
    "dev",
    "doc",
    "elaborate",
    "eval",
    "expand",
    "extract",
    "fetch",
    "fill",
    "fmt",
    "goals",
    "help",
    "highlight",
    "index",
    "init",
    "library",
    "lint",
    "lock",
    "lsp",
    "macro",
    "proof",
    "proof-status",
    "publish-crates",
    "remove",
    "run",
    "suggest",
    "syntax",
    "test",
    "trust",
    "try",
    "update",
];

/// Whether `tauto WORD` may be a project's command: a command name that is
/// not one of tauto's own.
pub(crate) fn is_name(word: &str) -> bool {
    word.chars().next().is_some_and(|c| c.is_ascii_lowercase())
        && word
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
        && !BUILT_IN.contains(&word)
}

struct Offer {
    name: String,
    tote: String,
    dir: PathBuf,
    command: Command,
}

/// The project: the nearest directory holding a `Tauto.eure`, from the
/// working directory up.
fn project() -> Option<PathBuf> {
    let here = std::env::current_dir().ok()?;
    here.ancestors()
        .find(|d| d.join("Tauto.eure").is_file())
        .map(Path::to_path_buf)
}

/// The commands of the project and of its direct dependencies, and the
/// dependencies that could not be read.
fn offers(project: &Path, manifest: &Manifest) -> (Vec<Offer>, Vec<String>) {
    let mut out: Vec<Offer> = manifest
        .commands
        .iter()
        .map(|(name, command)| Offer {
            name: name.clone(),
            tote: manifest.package.name.clone(),
            dir: project.to_path_buf(),
            command: command.clone(),
        })
        .collect();
    let mut unread = Vec::new();
    for (name, dependency) in &manifest.dependencies {
        let read = tauto::manifest::dependency_dir(project, name, dependency)
            .and_then(|dir| Ok((tauto::manifest::read(&dir)?, dir)));
        match read {
            Ok((found, dir)) => out.extend(found.commands.into_iter().map(|(n, command)| Offer {
                name: n,
                tote: found.package.name.clone(),
                dir: dir.clone(),
                command,
            })),
            Err(e) => unread.push(format!("{name}: {e}")),
        }
    }
    (out, unread)
}

/// Which offer `tauto NAME` runs: the one `trust.commands.NAME.tote`
/// chooses, else the project's own, else the only direct dependency's.
/// `Ok(None)` when nothing offers it.
fn choose<'o>(
    name: &str,
    manifest: &Manifest,
    offers: &'o [Offer],
) -> Result<Option<&'o Offer>, String> {
    let named: Vec<&Offer> = offers.iter().filter(|o| o.name == name).collect();
    if let Some(trust) = manifest.trust_commands.get(name) {
        return match named.iter().find(|o| o.tote == trust.tote) {
            Some(o) => Ok(Some(o)),
            None => Err(i18n::t!(
                "commands-trust-wrong-tote",
                name = name,
                tote = &trust.tote,
                givers = givers(&named)
            )),
        };
    }
    if let Some(own) = named.iter().find(|o| o.tote == manifest.package.name) {
        return Ok(Some(own));
    }
    match named.as_slice() {
        [] => Ok(None),
        [one] => Ok(Some(one)),
        _ => Err(i18n::t!(
            "commands-ambiguous",
            totes = named
                .iter()
                .map(|o| o.tote.as_str())
                .collect::<Vec<_>>()
                .join(&i18n::t!("commands-and")),
            name = name,
            snippet = format!(
                "trust {{ commands {{ {name} {{ tote = \"{}\" }} }} }}",
                named[0].tote
            )
        )),
    }
}

fn givers(named: &[&Offer]) -> String {
    if named.is_empty() {
        return String::new();
    }
    let totes: Vec<&str> = named.iter().map(|o| o.tote.as_str()).collect();
    i18n::t!("commands-givers", totes = totes.join(", "))
}

/// The `--allow-*` flags a grant stands for; relative paths are the
/// project's.
fn flags(trust: &CommandTrust, project: &Path) -> Vec<String> {
    trust
        .allow
        .iter()
        .map(|(kind, granted)| match granted {
            None => format!("--allow-{kind}"),
            Some(names) => {
                let names: Vec<String> = names
                    .iter()
                    .map(|n| match kind.as_str() {
                        "read" | "write" if Path::new(n).is_relative() => {
                            project.join(n).to_string_lossy().into_owned()
                        }
                        _ => n.clone(),
                    })
                    .collect();
                format!("--allow-{kind}={}", names.join(","))
            }
        })
        .collect()
}

/// `tauto NAME ARGS…`. `None` when no command has the name, which is then
/// an unknown command of `tauto` itself.
pub(crate) fn run(name: &str, args: &[String]) -> Option<ExitCode> {
    let project = project()?;
    let manifest = match tauto::manifest::read(&project) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("{e}");
            return Some(ExitCode::from(2));
        }
    };
    let (offers, unread) = offers(&project, &manifest);
    let offer = match choose(name, &manifest, &offers) {
        Ok(Some(offer)) => offer,
        Ok(None) if unread.is_empty() => return None,
        Ok(None) => {
            eprintln!(
                "{}",
                i18n::t!(
                    "commands-unread-dependencies",
                    name = name,
                    unread = unread.join("\n  ")
                )
            );
            return Some(ExitCode::from(2));
        }
        Err(e) => {
            eprintln!("{e}");
            return Some(ExitCode::from(2));
        }
    };
    Some(crate::with_deep_stack(|| {
        run_offer(&project, &manifest, offer, args)
    }))
}

fn run_offer(project: &Path, manifest: &Manifest, offer: &Offer, args: &[String]) -> ExitCode {
    let entry = offer.dir.join(&offer.command.main).display().to_string();
    let loaded = match tauto::program::load_command(project, &offer.dir, &offer.name) {
        Ok(loaded) => loaded,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    let rows = loaded.check_rows(false);
    if !rows.errors.is_empty() {
        for e in &rows.errors {
            eprintln!("{}", locate_in(&loaded, &entry, &e.to_string()));
        }
        return ExitCode::FAILURE;
    }
    let trust = manifest
        .trust_commands
        .get(&offer.name)
        .filter(|t| t.tote == offer.tote);
    let flags = trust.map(|t| flags(t, project)).unwrap_or_default();
    let permissions = match tauto_rt::permissions::Permissions::from_args(&flags) {
        Ok((permissions, _)) => permissions,
        Err(e) => {
            eprintln!(
                "{}",
                i18n::t!(
                    "commands-bad-trust",
                    name = &offer.name,
                    error = e.to_string()
                )
            );
            return ExitCode::from(2);
        }
    };
    let needed: BTreeSet<&str> = tauto::host::permissions(rows.host_effects.iter());
    let missing = permissions.missing(needed);
    if !missing.is_empty() {
        eprintln!(
            "{}",
            denied(
                offer,
                trust.is_some(),
                &missing,
                &project.join("Tauto.eure")
            )
        );
        return ExitCode::FAILURE;
    }
    let options = RunOptions {
        args: args.to_vec(),
        permissions,
        live: true,
        ..RunOptions::default()
    };
    match tauto::eval::run_loaded_with(&loaded, u64::MAX, options) {
        Ok(outcome) => {
            print!("{}", outcome.stdout);
            eprint!("{}", outcome.stderr);
            ExitCode::from(outcome.exit.map_or(0, |code| code as u8))
        }
        Err(error) => {
            eprintln!("{}", locate_in(&loaded, &entry, &error.to_string()));
            ExitCode::FAILURE
        }
    }
}

/// What a command that needs `missing` and is not granted them is told: the
/// kinds, and the lines that grant them.
fn denied(offer: &Offer, granted: bool, missing: &[&str], file: &Path) -> String {
    let kinds = missing.join(&i18n::t!("commands-and"));
    let lines: Vec<String> = missing
        .iter()
        .map(|k| match *k {
            "clipboard" => "clipboard = true".to_string(),
            "env" => "env = [\"NAME\"]".to_string(),
            "net" => "net = [\"HOST\"]".to_string(),
            "run" => "run = [\"PROGRAM\"]".to_string(),
            _ => format!("{k} = [\"PATH\"]"),
        })
        .collect();
    let head = i18n::t!(
        "commands-denied",
        name = &offer.name,
        tote = &offer.tote,
        kinds = kinds
    );
    if granted {
        format!(
            "{head}\n{}\n  {}",
            i18n::t!(
                "commands-denied-add",
                name = &offer.name,
                file = file.display().to_string()
            ),
            lines.join("\n  ")
        )
    } else {
        format!(
            "{head}\n{}\n  trust {{\n    commands {{\n      {} {{\n        tote = \"{}\"\n        {}\n      }}\n    }}\n  }}",
            i18n::t!("commands-denied-grant", file = file.display().to_string()),
            offer.name,
            offer.tote,
            lines.join("\n        ")
        )
    }
}

/// The lines `tauto --help` ends with in a project: its commands, each with
/// its tote, what it does and what the project grants it. Nothing is
/// fetched: a Git dependency not in the cache is named as not fetched.
pub(crate) fn help() -> Option<String> {
    let project = project()?;
    let manifest = tauto::manifest::read(&project).ok()?;
    let (offers, unread) = offers(&project, &manifest);
    if offers.is_empty() && unread.is_empty() {
        return None;
    }
    let mut lines = vec![i18n::t!(
        "commands-help-head",
        path = project.display().to_string()
    )];
    let mut names: Vec<&str> = offers.iter().map(|o| o.name.as_str()).collect();
    names.sort();
    names.dedup();
    for name in names {
        let chosen = choose(name, &manifest, &offers);
        for o in offers.iter().filter(|o| o.name == name) {
            let state = if BUILT_IN.contains(&name) {
                i18n::t!("commands-state-built-in")
            } else {
                match &chosen {
                    Ok(Some(c)) if std::ptr::eq(*c, o) => {
                        match manifest
                            .trust_commands
                            .get(name)
                            .filter(|t| t.tote == o.tote)
                        {
                            Some(t) if !t.allow.is_empty() => i18n::t!(
                                "commands-state-granted",
                                kinds = t
                                    .allow
                                    .iter()
                                    .map(|(k, _)| k.as_str())
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ),
                            _ => i18n::t!("commands-state-granted-nothing"),
                        }
                    }
                    Ok(_) => i18n::t!("commands-state-other-tote"),
                    Err(_) => i18n::t!("commands-state-ambiguous"),
                }
            };
            lines.push(format!(
                "  tauto {name}  ({}) {}  [{state}]",
                o.tote, o.command.about
            ));
        }
    }
    for u in unread {
        lines.push(i18n::t!("commands-help-not-read", item = u));
    }
    Some(lines.join("\n"))
}

pub(crate) fn given(dir: &Path) -> Vec<String> {
    let Ok(manifest) = tauto::manifest::read(dir) else {
        return Vec::new();
    };
    manifest
        .commands
        .iter()
        .map(|(name, c)| {
            let state = if BUILT_IN.contains(&name.as_str()) {
                i18n::t!("commands-given-built-in")
            } else {
                String::new()
            };
            format!("  tauto {name}  {}{state}", c.about)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::BUILT_IN;

    #[test]
    fn every_command_of_the_usage_is_built_in() {
        let usage = crate::USAGE;
        for word in usage.split("tauto ").skip(1) {
            let name: String = word
                .chars()
                .take_while(|c| c.is_ascii_lowercase() || *c == '-')
                .collect();
            if name.is_empty() || name.starts_with('-') {
                continue;
            }
            assert!(BUILT_IN.contains(&name.as_str()), "{name}");
        }
        let mut sorted = BUILT_IN.to_vec();
        sorted.sort();
        assert_eq!(sorted, BUILT_IN);
    }
}
