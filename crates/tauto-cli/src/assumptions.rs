//! `tauto assumptions FILE [NAME] [--json]`: what each declaration of the file
//! rests on besides the kernel. The axioms are the kernel's own record; the
//! `extern` functions are found by following the names the bodies mention.
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::ExitCode;

use tauto::check::Verdict;
use tauto::report::{self, Json, Report};
use tauto::surface::{Stmt, SurfaceTerm, TermKind, parse_program, walk};

use crate::i18n;

const USAGE: &str = "tauto assumptions FILE [NAME] [--json]";

pub fn command(args: &[String]) -> ExitCode {
    let mut json = false;
    let mut positional = Vec::new();
    for a in args {
        match a.as_str() {
            "--json" => json = true,
            a if a.starts_with('-') => return usage(),
            a => positional.push(a),
        }
    }
    let (path, only) = match positional[..] {
        [path] => (path, None),
        [path, name] => (path, Some(name)),
        _ => return usage(),
    };
    let path = Path::new(path);
    let report = match report::check_report(path, None) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::FAILURE;
        }
    };
    let own = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let graph = match Graph::of(&report, &own) {
        Ok(graph) => graph,
        Err((file, error)) => {
            eprintln!(
                "{}",
                i18n::t!(
                    "assumptions-unread",
                    path = file.display().to_string(),
                    error = error
                )
            );
            return ExitCode::FAILURE;
        }
    };
    let mut rows = Vec::new();
    for e in &report.entries {
        if e.file != own || only.is_some_and(|n| n != e.entry.name.as_str()) {
            continue;
        }
        rows.push(Row::of(&e.entry.name, Some(&e.entry.verdict), &graph));
    }
    // The functions the kernel does not check: programs, not proofs.
    for name in &graph.own {
        if only.is_none_or(|n| n == name) && !rows.iter().any(|r| &r.name == name) {
            rows.push(Row::of(name, None, &graph));
        }
    }
    if let Some(name) = only
        && rows.is_empty()
    {
        eprintln!(
            "{}",
            i18n::t!(
                "assumptions-no-declaration",
                path = path.display().to_string(),
                name = name
            )
        );
        return ExitCode::FAILURE;
    }
    if json {
        println!(
            "{}",
            Json::Arr(rows.iter().map(Row::json).collect()).render()
        );
    } else {
        for r in &rows {
            print!("{}", r.text());
        }
    }
    // As `check`: 1 when something failed, 3 when only holes are left.
    if rows.iter().any(|r| r.status == "failed") {
        ExitCode::FAILURE
    } else if rows.iter().any(|r| r.status == "incomplete") {
        ExitCode::from(3)
    } else {
        ExitCode::SUCCESS
    }
}

fn usage() -> ExitCode {
    eprintln!("{}", i18n::t!("assumptions-usage", usage = USAGE));
    ExitCode::from(2)
}

struct Row {
    name: String,
    status: &'static str,
    axioms: Vec<String>,
    externs: Vec<String>,
    holes: Vec<String>,
    /// Incomplete or failed declarations it uses.
    uses: Vec<String>,
}

impl Row {
    /// `verdict` is `None` for a function the kernel does not check.
    fn of(name: &str, verdict: Option<&Verdict>, graph: &Graph) -> Row {
        let mut row = Row {
            name: name.into(),
            status: "ok",
            axioms: Vec::new(),
            externs: graph.externs_reached(name),
            holes: Vec::new(),
            uses: Vec::new(),
        };
        let Some(verdict) = verdict else {
            row.status = "program";
            return row;
        };
        match verdict {
            Verdict::Checked { axioms } => {
                row.axioms = axioms.iter().map(ToString::to_string).collect()
            }
            Verdict::Skipped(_) => row.status = "skipped",
            Verdict::Failed(_) => row.status = "failed",
            Verdict::Incomplete { holes, uses } => {
                row.status = "incomplete";
                row.holes = holes.iter().map(|h| format!("?{}", h.name)).collect();
                row.uses = uses.iter().map(ToString::to_string).collect();
            }
        }
        row
    }

    fn text(&self) -> String {
        let list = |v: &[String]| {
            if v.is_empty() {
                i18n::t!("assumptions-none")
            } else {
                v.join(", ")
            }
        };
        let mut out = format!("{} ({})\n", self.name, self.status);
        let mut line = |id: &str, names: &[String]| {
            out.push_str("  ");
            out.push_str(&i18n::t!(id, names = list(names)));
            out.push('\n');
        };
        line("assumptions-axioms", &self.axioms);
        line("assumptions-externs", &self.externs);
        if !self.holes.is_empty() {
            line("assumptions-holes", &self.holes);
        }
        if !self.uses.is_empty() {
            line("assumptions-uses-incomplete", &self.uses);
        }
        out
    }

    fn json(&self) -> Json {
        let arr = |v: &[String]| Json::Arr(v.iter().map(|s| Json::Str(s.clone())).collect());
        Json::Obj(vec![
            ("name", Json::Str(self.name.clone())),
            ("status", Json::Str(self.status.into())),
            ("axioms", arr(&self.axioms)),
            ("externs", arr(&self.externs)),
            ("holes", arr(&self.holes)),
            ("uses_incomplete", arr(&self.uses)),
        ])
    }
}

/// The names each declaration's statement and body mention, and the
/// `extern` functions, over every file of the report.
struct Graph {
    mentions: BTreeMap<String, BTreeSet<String>>,
    externs: BTreeSet<String>,
    /// The functions the checked file itself declares, in order.
    own: Vec<String>,
}

impl Graph {
    /// A file of the report that cannot be read is an error, not a file
    /// that trusts nothing.
    fn of(report: &Report, own: &Path) -> Result<Graph, (std::path::PathBuf, String)> {
        let mut graph = Graph {
            mentions: BTreeMap::new(),
            externs: BTreeSet::new(),
            own: Vec::new(),
        };
        for (path, source) in report.files() {
            // What a macro makes is read as the check read it, expanded.
            let mut stmts = match report.expanded(path) {
                Some(stmts) => stmts.to_vec(),
                None => {
                    parse_program(source)
                        .map_err(|e| (path.to_path_buf(), e.to_string()))?
                        .stmts
                }
            };
            // The functions of this file are read by the kernel as written, and
            // the compiler replaces each by a builtin the kernel does not
            // check: the host's implementation is assumed, as an
            // `extern` function's is.
            let swapped =
                path == Path::new(tauto::stdlib::ROOT).join(tauto::extract::SWAPPED_FILE);
            for stmt in &mut stmts {
                graph.add(stmt, path == own, swapped);
            }
        }
        Ok(graph)
    }

    /// Every declaration a statement makes, wherever it is nested, with the
    /// names its terms mention. A name is anything a term may reach a
    /// declaration by: a variable, and a field or method name, since a
    /// method is called through one. Reading more names than are used only
    /// lists an extern that is not reached; reading fewer would hide one.
    fn add(&mut self, stmt: &mut Stmt, own: bool, swapped: bool) {
        let name = match stmt {
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                for s in items {
                    self.add(s, own, swapped);
                }
                return;
            }
            Stmt::Attributed { stmt, .. } => return self.add(stmt, own, swapped),
            Stmt::Extern { fns, .. } => {
                self.externs.extend(fns.iter().map(|f| f.name.to_string()));
                return;
            }
            Stmt::Instance(i) => {
                for m in &mut i.methods {
                    let name = m.name.to_string();
                    let mut f = Stmt::Fn(m.clone());
                    let names = mentioned(&mut f);
                    self.mentions
                        .entry(base(&name).to_string())
                        .or_default()
                        .extend(names);
                }
                return;
            }
            Stmt::Fn(f) => {
                if own {
                    self.own.push(f.name.to_string());
                }
                let short = base(&f.name.to_string()).to_string();
                if swapped && tauto::extract::SWAPPED_FNS.contains(&short.as_str()) {
                    self.externs.insert(short);
                }
                f.name.to_string()
            }
            Stmt::Theorem(t) | Stmt::Def(t) => t.name.to_string(),
            _ => return,
        };
        let names = mentioned(stmt);
        self.mentions
            .entry(base(&name).to_string())
            .or_default()
            .extend(names);
    }

    /// The `extern` that `n` names, written in full (`std::slots_store::Slots::new`)
    /// or not.
    fn extern_named(&self, n: &str) -> Option<&str> {
        self.externs.get(n).map(String::as_str).or_else(|| {
            self.externs
                .iter()
                .find(|e| n.strip_suffix(e.as_str()).is_some_and(|p| p.ends_with("::")))
                .map(String::as_str)
        })
    }

    /// The `extern` functions `name` reaches through the declarations it
    /// mentions. Names are matched by their last segment, so a local that
    /// shadows a global may add one that is not used.
    fn externs_reached(&self, name: &str) -> Vec<String> {
        let mut seen = BTreeSet::new();
        let mut todo = vec![base(name).to_string()];
        let mut found = BTreeSet::new();
        while let Some(n) = todo.pop() {
            if !seen.insert(n.clone()) {
                continue;
            }
            if let Some(e) = self.extern_named(&n) {
                found.insert(e.to_string());
            }
            if let Some(m) = self.mentions.get(&n) {
                todo.extend(m.iter().cloned());
            }
        }
        found.into_iter().collect()
    }
}

fn mentioned(stmt: &mut Stmt) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    walk::stmt(stmt, &mut |t: &mut SurfaceTerm| match &*t.kind {
        TermKind::Var(n) => {
            names.insert(base(n).to_string());
        }
        TermKind::Field { name, .. } => {
            names.insert(base(name).to_string());
        }
        _ => {}
    });
    names
}

fn base(name: &str) -> &str {
    tauto::surface::qualify::short(name)
}
