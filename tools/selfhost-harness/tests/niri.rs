//! `totes/niri` against `crates/tauto-niri`.
//!
//! Every case that shows something is compiled and given the passes a
//! backend runs, as `crates/tauto-niri/tests/cases.rs` does, and printed as
//! NIR text. The crate runs the package it reads back from the text; the tote
//! runs the text. Both must write the same to stdout and end the same way. Positions are
//! left out of what a run says (`first_line`), as the text keeps none.
//!
//! What the tote does not run yet says `tote: …`: such a case is only
//! counted. `NIRI_ONLY=<part of a name>` runs the cases so named;
//! `NIRI_LIST=1` prints each case and how it ended.


use selfhost_harness::{assert_same_dump, root, run_tote_native};
use tauto_niri::Outcome;


const STEPS: u64 = 2_000_000_000_000;

/// Cases the tote cannot end as the crate does, and why.
const KNOWN: &[(&str, &str)] = &[(
    "rust/programs/data-and-show",
    "`show` writes a name as the source spells it; the text keeps only the \
     qualified name (`main::Unit` for a `Unit` beside the prelude's)",
)];

fn first_line(s: &str) -> String {
    let line = s.lines().next().unwrap_or("");
    let mut out = String::new();
    let mut digits = false;
    for c in line.chars() {
        if c.is_ascii_digit() {
            if !digits {
                out.push('N');
            }
            digits = true;
        } else {
            digits = false;
            out.push(c);
        }
    }
    out.replace('\t', " ").chars().take(120).collect()
}

/// The case after the passes, as NIR text, and how the crate runs it.
fn text(case: &tauto_test_suite::RustCase) -> Option<(String, String)> {
    let pkg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| case.compile("rust")));
    let Ok(Ok(mut pkg)) = pkg else {
        return None;
    };
    tauto_nir::mono::specialize(&mut pkg).ok()?;
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    let t = tauto_nir::text::print(&pkg).ok()?;
    Some((t, rust_run(&pkg)))
}

fn ended(word: &str, what: &str) -> String {
    format!("end {word}: {}\n", first_line(what))
}

/// How the crate runs the package.
fn rust_run(pkg: &tauto_nir::Package) -> String {
    let run = tauto_niri::run(pkg);
    let mut out = String::new();
    out.push_str(&format!("{:?}\n", run.stdout));
    out.push_str(&match &run.outcome {
        Outcome::Ok => ended("ok", ""),
        Outcome::Violation(v) => ended(&format!("violation:{:?}", v.kind), &v.detail),
        Outcome::Unsupported(w) => ended("unsupported", w),
        Outcome::Error(e) => ended("error", e),
    });
    out
}

/// Takes `n` bytes from the front of `s`.
fn take<'a>(s: &mut &'a str, n: usize) -> &'a str {
    let (a, b) = s.split_at(n.min(s.len()));
    *s = b;
    a
}

fn line<'a>(s: &mut &'a str) -> &'a str {
    let n = s.find('\n').map_or(s.len(), |i| i + 1);
    take(s, n).trim_end_matches('\n')
}

/// The runs of the tote, in the order of its arguments.
fn tote_runs(mut s: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    while !s.is_empty() {
        let l = line(&mut s);
        let words: Vec<&str> = l.split(' ').collect();
        match words.as_slice() {
            ["==", ..] => out.push(String::new()),
            ["out", n] => {
                let text = take(&mut s, n.parse().unwrap()).to_string();
                take(&mut s, 1);
                if let Some(o) = out.last_mut() {
                    o.push_str(&format!("{text:?}\n"));
                }
            }
            ["end", word, n] => {
                let what = take(&mut s, n.parse().unwrap()).to_string();
                take(&mut s, 1);
                if let Some(o) = out.last_mut() {
                    o.push_str(&ended(word, &what));
                }
            }
            _ => panic!("a line `niri run` does not write: {l:?}"),
        }
    }
    out
}

#[test]
fn niri_runs_as_the_crate() {
    tauto_messages::install();
    let only = std::env::var("NIRI_ONLY").ok();
    let cases: Vec<_> = tauto_test_suite::rust_cases(&root().join("cases"))
        .unwrap()
        .into_iter()
        .filter(|c| only.as_ref().is_none_or(|o| c.name.contains(o.as_str())))
        .filter(|c| c.stdout.is_some() && c.run_error.is_none())
        .collect();
    let runs: Vec<(String, String, String)> = tauto_test_suite::parallel_map(&cases, |_| (), |_, _, c| {
        text(c).map(|(t, w)| (c.name.clone(), t, w))
    })
    .into_iter()
    .flatten()
    .collect();
    let texts: Vec<(String, String)> = runs.iter().map(|(n, t, _)| (n.clone(), t.clone())).collect();
    let want: Vec<String> = runs.into_iter().map(|(_, _, w)| w).collect();
    assert!(!texts.is_empty(), "the crate prints no package");
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-niri-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let paths: Vec<String> = texts
        .iter()
        .enumerate()
        .map(|(i, (_, t))| {
            let p = dir.join(format!("{i:05}.nir"));
            std::fs::write(&p, t).unwrap();
            p.to_string_lossy().into_owned()
        })
        .collect();

    let mut args = vec!["run".to_string()];
    args.extend(paths);
    let out = run_tote_native("niri", &args, STEPS);
    assert_eq!(out.error, None, "{}", out.stderr);
    let got = tote_runs(&out.stdout);
    assert_eq!(got.len(), texts.len(), "`niri run` answers each file (exit {:?}): {}; stopped in {:?}", out.exit, out.stderr, texts.get(got.len().saturating_sub(1)).map(|t| &t.0));

    let (mut rust, mut tauto) = (String::new(), String::new());
    let mut counts = std::collections::BTreeMap::<String, usize>::new();
    for (((name, _), w), g) in texts.iter().zip(&want).zip(&got) {
        let last = |s: &str| s.lines().last().unwrap_or("").to_string();
        if std::env::var_os("NIRI_LIST").is_some() {
            eprintln!("CASE {name}\t{}\t{}", last(w), last(g));
        }
        if KNOWN.iter().any(|(k, _)| name == k) {
            *counts.entry("known".into()).or_default() += 1;
            continue;
        }
        if last(g).starts_with("end unsupported: tote: ") {
            *counts.entry(last(g)).or_default() += 1;
            continue;
        }
        let kind = last(w).split(':').next().unwrap_or("").to_string();
        *counts.entry(kind).or_default() += 1;
        rust.push_str(&format!("== {name}\n{w}"));
        tauto.push_str(&format!("== {name}\n{g}"));
    }
    eprintln!("{} cases: {counts:?}", texts.len());
    assert_same_dump("niri", &rust, &tauto);
    if std::env::var_os("NIRI_KEEP").is_none() {
        let _ = std::fs::remove_dir_all(&dir);
    }
}
