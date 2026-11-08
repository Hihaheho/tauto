//! `tauto audit`: what a tote and the totes it depends on ask to be trusted
//! with, read from their files before anything of theirs is checked or run.
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use tauto::manifest::{CommandTrust, Manifest};
use tauto::report::Json;
use tauto::surface::{Stmt, parse_program};

use crate::bag::Problem;
use crate::i18n;

#[derive(Default)]
struct Tote {
    name: String,
    version: String,
    externs: BTreeSet<String>,
    axioms: BTreeSet<String>,
    /// The effects its functions' rows name.
    effects: BTreeSet<String>,
    rust_bridge: Option<String>,
    rust_crates: Vec<String>,
    javascript: Vec<String>,
    /// The commands it gives: name, main, about, and the kinds the project
    /// grants it in `trust.commands`.
    commands: Vec<(String, String, String, Vec<String>)>,
    /// Files that did not parse: what they declare is not counted.
    unread: Vec<String>,
}

pub fn audit(
    args: Vec<String>,
    totes: &[(String, PathBuf, Manifest)],
) -> Result<ExitCode, Problem> {
    let json = match args.as_slice() {
        [] => false,
        [flag] if flag == "--json" => true,
        _ => return Err(Problem::Usage(i18n::t!("audit-usage"))),
    };
    // Only the project's own `trust` grants anything.
    let trust = totes
        .first()
        .map(|(_, _, m)| m.trust_commands.clone())
        .unwrap_or_default();
    let rows: Vec<Tote> = totes
        .iter()
        .map(|(name, dir, m)| read(name, dir, m, &trust))
        .collect();
    if json {
        println!(
            "{}",
            Json::Arr(rows.iter().map(Tote::json).collect()).render()
        );
    } else {
        for r in &rows {
            print!("{}", r.text());
        }
    }
    Ok(ExitCode::SUCCESS)
}

fn read(
    name: &str,
    dir: &Path,
    manifest: &Manifest,
    trust: &BTreeMap<String, CommandTrust>,
) -> Tote {
    let commands = manifest
        .commands
        .iter()
        .map(|(command, c)| {
            let granted = trust
                .get(command)
                .filter(|t| t.tote == manifest.package.name)
                .map(|t| t.allow.iter().map(|(k, _)| k.clone()).collect())
                .unwrap_or_default();
            (command.clone(), c.main.clone(), c.about.clone(), granted)
        })
        .collect();
    let mut tote = Tote {
        commands,
        name: name.into(),
        version: manifest.package.version.clone(),
        rust_bridge: manifest.rust.bridge.clone(),
        rust_crates: manifest.rust.dependencies.keys().cloned().collect(),
        javascript: manifest.javascript.sources.clone(),
        ..Tote::default()
    };
    let mut files = Vec::new();
    for source in manifest.package.source_paths() {
        taut_files(&dir.join(source), &mut files);
    }
    // A command's program runs too, though no dependent reads it.
    for c in manifest.commands.values() {
        taut_files(&dir.join(&c.main), &mut files);
    }
    files.sort();
    files.dedup();
    for file in files {
        let parsed = std::fs::read_to_string(&file)
            .map_err(|e| e.to_string())
            .and_then(|text| parse_program(&text).map_err(|e| e.to_string()));
        match parsed {
            Ok(program) => program.stmts.iter().for_each(|s| tote.add(s)),
            Err(_) => tote.unread.push(
                file.strip_prefix(dir)
                    .unwrap_or(&file)
                    .display()
                    .to_string(),
            ),
        }
    }
    tote
}

/// `path` itself if it is a `.taut` file, else every `.taut` file under it,
/// hidden directories and `target` included, without following symbolic links.
fn taut_files(path: &Path, out: &mut Vec<PathBuf>) {
    if path.is_file() {
        if path.extension().is_some_and(|e| e == "taut") {
            out.push(path.to_path_buf());
        }
    } else {
        crate::walk_taut_files(path, true, out);
    }
}

impl Tote {
    fn add(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                items.iter().for_each(|s| self.add(s));
            }
            Stmt::Extern { fns, .. } => {
                for f in fns {
                    self.externs.insert(f.name.to_string());
                    self.effects
                        .extend(f.effects.iter().flatten().map(ToString::to_string));
                }
            }
            Stmt::Theorem(t) if t.body.is_none() => {
                self.axioms.insert(t.name.to_string());
            }
            Stmt::Fn(f) => self
                .effects
                .extend(f.effects.iter().flatten().map(ToString::to_string)),
            Stmt::Attributed { stmt, .. } => self.add(stmt),
            _ => {}
        }
    }

    fn text(&self) -> String {
        let list = |v: &mut dyn Iterator<Item = &String>| {
            let v: Vec<_> = v.map(String::as_str).collect();
            if v.is_empty() {
                i18n::t!("audit-none")
            } else {
                v.join(", ")
            }
        };
        let mut out = format!("{} {}\n", self.name, self.version);
        out.push_str(&i18n::t!(
            "audit-externs",
            list = list(&mut self.externs.iter())
        ));
        out.push('\n');
        out.push_str(&i18n::t!(
            "audit-axioms",
            list = list(&mut self.axioms.iter())
        ));
        out.push('\n');
        out.push_str(&i18n::t!(
            "audit-effects",
            list = list(&mut self.effects.iter())
        ));
        out.push('\n');
        if let Some(bridge) = &self.rust_bridge {
            out.push_str(&i18n::t!(
                "audit-rust",
                bridge = bridge,
                crates = list(&mut self.rust_crates.iter())
            ));
            out.push('\n');
        }
        if !self.javascript.is_empty() {
            out.push_str(&i18n::t!(
                "audit-javascript",
                list = list(&mut self.javascript.iter())
            ));
            out.push('\n');
        }
        for (name, main, about, granted) in &self.commands {
            let granted = if granted.is_empty() {
                i18n::t!("audit-granted-nothing")
            } else {
                i18n::t!("audit-granted", kinds = granted.join(", "))
            };
            out.push_str(&i18n::t!(
                "audit-command",
                name = name,
                main = main,
                granted = granted,
                about = about
            ));
            out.push('\n');
        }
        if !self.unread.is_empty() {
            out.push_str(&i18n::t!(
                "audit-not-read",
                list = list(&mut self.unread.iter())
            ));
            out.push('\n');
        }
        out
    }

    fn json(&self) -> Json {
        let arr = |v: &mut dyn Iterator<Item = &String>| {
            Json::Arr(v.map(|s| Json::Str(s.clone())).collect())
        };
        Json::Obj(vec![
            ("name", Json::Str(self.name.clone())),
            ("version", Json::Str(self.version.clone())),
            ("externs", arr(&mut self.externs.iter())),
            ("axioms", arr(&mut self.axioms.iter())),
            ("effects", arr(&mut self.effects.iter())),
            ("rust_bridge", arr(&mut self.rust_bridge.iter())),
            ("rust_crates", arr(&mut self.rust_crates.iter())),
            ("javascript", arr(&mut self.javascript.iter())),
            (
                "commands",
                Json::Arr(
                    self.commands
                        .iter()
                        .map(|(name, main, about, granted)| {
                            Json::Obj(vec![
                                ("name", Json::Str(name.clone())),
                                ("main", Json::Str(main.clone())),
                                ("about", Json::Str(about.clone())),
                                ("granted", arr(&mut granted.iter())),
                            ])
                        })
                        .collect(),
                ),
            ),
            ("not_read", arr(&mut self.unread.iter())),
        ])
    }
}
