//! Every case that shows something, run by niri.
//!
//! Each case ends one way: it passes, niri does not run it yet (with the
//! reason), it breaks a rule (a violation), or something else stops it.
//! What a case shows is compared with what the case says it shows. The test
//! fails on a case that shows something else, stops with an error the case
//! does not expect, or breaks a rule its `niri.bug` (`<kind>: why`) does not
//! name. It also fails on a case whose `niri.bug` no longer happens.
//! Cases niri does not run yet are only counted. A case with a function of
//! the tier `O` or `M` is run again with each such function run as its
//! continuations (`tauto_nir::kont`), and must end the same way, or say
//! `niri.bug = "split: why"`.

use std::path::Path;

use tauto_niri::Outcome;
use tauto_test_suite::RustCase;

fn outcome(case: &RustCase) -> String {
    let expected = case
        .stdout
        .as_deref()
        .expect("a case that writes to stdout");
    let pkg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| case.compile("rust")));
    let mut pkg = match pkg {
        Ok(Ok(p)) => p,
        // The compiler's message is not kept: some of it changes from run
        // to run (a temporary directory, the order of a row).
        Ok(Err(e)) => {
            let stage = match e {
                tauto_nibcheck::lower::CompileError::Front(_)
                | tauto_nibcheck::lower::CompileError::Package(_) => "front",
                tauto_nibcheck::lower::CompileError::Build(_) => "build",
                tauto_nibcheck::lower::CompileError::Unsupported(_) => "unsupported",
            };
            return format!("not compiled: {stage}");
        }
        Err(_) => return "not compiled: the compiler panicked".into(),
    };
    // A generic of an arm that no instance fixes is left a type parameter
    // (`mono::check` says so): niri runs it as it is.
    if let Err(e) = tauto_nir::mono::specialize(&mut pkg) {
        return format!("mono: {}", first_line(&e));
    }
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    if std::env::var_os("NIRI_TRACE").is_some() {
        eprintln!("run {}", case.name);
    }
    let whole = ended(&tauto_niri::run(&pkg), expected);
    // A function of the tier `O` or `M` run as its continuations
    // (`tauto_nir::kont`) ends the same way.
    if pkg.fns.iter().any(|f| f.tier >= tauto_nir::Tier::O) {
        let opts = tauto_niri::Options {
            split: true,
            ..Default::default()
        };
        let split = ended(&tauto_niri::run_with(&pkg, opts), expected);
        let both_unsupported = split.starts_with("unsupported") && whole.starts_with("unsupported");
        if split != whole && !both_unsupported {
            return format!("split: {split} (whole: {whole})");
        }
    }
    // The functions that run from their block form (`tauto_nir::blocks`)
    // end the same way as the trees.
    if std::env::var_os("NIRI_NO_BLOCKS").is_some() {
        return whole;
    }
    let opts = tauto_niri::Options {
        blocks: true,
        ..Default::default()
    };
    let blocks = ended(&tauto_niri::run_with(&pkg, opts), expected);
    let both_unsupported = blocks.starts_with("unsupported") && whole.starts_with("unsupported");
    // A run from blocks that gets further than the tree (a continuation
    // taken across a nested evaluation, which blocks do not nest) is no
    // mismatch.
    let further = whole.starts_with("unsupported") && !blocks.starts_with("unsupported");
    if blocks != whole && !both_unsupported && !further {
        return format!("blocks: {blocks} (whole: {whole})");
    }
    whole
}

fn ended(run: &tauto_niri::Run, expected: &str) -> String {
    match &run.outcome {
        Outcome::Ok if run.stdout == expected => "pass".into(),
        Outcome::Ok => "output: differs".into(),
        Outcome::Unsupported(what) => format!("unsupported: {what}"),
        Outcome::Violation(v) => format!("violation: {:?}: {}", v.kind, first_line(&v.detail)),
        Outcome::Error(e) => format!("error: {}", first_line(e)),
    }
}

fn first_line(s: &str) -> String {
    let line = s.lines().next().unwrap_or("");
    // Positions move with every edit of a case file; the list keeps the kind.
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

#[test]
fn every_case_ends_as_allowed() {
    tauto_messages::install();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases");
    let cases: Vec<RustCase> = tauto_test_suite::rust_cases(&root)
        .unwrap()
        .into_iter()
        .filter(|c| {
            std::env::var("NIRI_ONLY").is_ok_and(|o| c.name.contains(&o))
                || std::env::var_os("NIRI_ONLY").is_none()
        })
        .filter(|c| c.stdout.is_some() && c.run_error.is_none())
        .filter(|c| {
            std::env::var("NIRI_SKIP")
                .map(|s| !s.split(',').any(|o| !o.is_empty() && c.name.contains(o)))
                .unwrap_or(true)
        })
        .collect();
    let start = std::time::Instant::now();
    let got: Vec<String> = tauto_test_suite::parallel_map(
        &cases,
        |_| (),
        |_, _, c| format!("{}\t{}", c.name, outcome(c)),
    );
    let mut counts = std::collections::BTreeMap::<&str, usize>::new();
    for line in &got {
        let status = line.split('\t').nth(1).unwrap_or("");
        let kind = status.split(':').next().unwrap_or(status);
        *counts.entry(kind).or_default() += 1;
    }
    eprintln!("{} cases in {:?}: {counts:?}", got.len(), start.elapsed());
    if std::env::var_os("NIRI_LIST").is_some() {
        for line in &got {
            eprintln!("CASE {line}");
        }
    }
    let mut wrong = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for (c, line) in cases.iter().zip(&got) {
        let status = line.split('\t').nth(1).unwrap_or("");
        let ok = if status.starts_with("split: ") {
            let known = c.niri.as_deref().is_some_and(|w| w.starts_with("split: "));
            if known {
                seen.insert(c.name.as_str());
            }
            known
        } else if let Some(rest) = status.strip_prefix("violation: ") {
            let kind = rest.split(':').next().unwrap_or(rest);
            let known = c
                .niri
                .as_deref()
                .and_then(|w| w.split_once(": "))
                .is_some_and(|(k, _)| k == kind);
            if known {
                seen.insert(c.name.as_str());
            }
            known
        } else if let Some(msg) = status.strip_prefix("error: ") {
            c.run_error.as_ref().is_some_and(|e| e.contains(msg))
        } else {
            !status.starts_with("output:")
                && !status.starts_with("split:")
                && !status.starts_with("blocks:")
        };
        if !ok {
            wrong.push(line.as_str());
        }
    }
    if std::env::var_os("NIRI_ONLY").is_none() {
        for c in cases.iter().filter(|c| c.niri.is_some()) {
            if !seen.contains(c.name.as_str()) {
                wrong.push(c.name.as_str());
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "cases that end other than allowed (a name alone: its `niri.bug` \
         no longer happens):\n{}",
        wrong.join("\n")
    );
}
/// `NIRI_ONLY=<part of a case name> cargo test -p tauto-niri --test cases
/// -- --ignored explain --nocapture`: the whole outcome of the cases named,
/// and their NIR with `NIRI_NIR=1`.
#[test]
#[ignore]
fn explain() {
    tauto_messages::install();
    let only = std::env::var("NIRI_ONLY").expect("NIRI_ONLY");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases");
    for case in tauto_test_suite::rust_cases(&root).unwrap() {
        if !only.split(',').any(|o| case.name.ends_with(o)) {
            continue;
        }
        let Ok(mut pkg) = case.compile("rust") else {
            continue;
        };
        if let Err(e) = tauto_nir::mono::specialize(&mut pkg) {
            println!("== {}\nmono: {e}", case.name);
            continue;
        }
        tauto_nir::anf::normalize(&mut pkg);
        tauto_nir::ownership::insert(&mut pkg);
        println!("== {}\n{}", case.name, case.source);
        if std::env::var_os("NIRI_NIR").is_some() {
            for f in &pkg.fns {
                println!("-- {} {:?}\n{:?}", f.source.as_str(), f.params, f.body);
                if std::env::var_os("NIRI_SPLIT").is_some()
                    && let Ok(s) = tauto_nir::kont::split(f)
                {
                    println!("split {s:#?}");
                }
            }
        }
        let run = tauto_niri::run_with(
            &pkg,
            tauto_niri::Options {
                split: std::env::var_os("NIRI_SPLIT").is_some(),
                ..Default::default()
            },
        );
        match &run.outcome {
            Outcome::Violation(v) => println!("=> {v}"),
            o => println!("=> {o:?}"),
        }
        println!(
            "stdout {:?}\nexpected {:?}",
            run.stdout,
            case.stdout.as_ref()
        );
    }
}
