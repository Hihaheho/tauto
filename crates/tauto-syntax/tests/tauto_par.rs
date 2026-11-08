//! The bootstrap tauto.par exported from `syntax tauto` is a valid grammar, and
//! the tables made from it run this crate's scanner and parser to the same
//! tokens as the parser generated from tauto.par for the repository's
//! programs (`docs/design/macro-implementation.md`「`crates/tauto-syntax`」).

use std::path::{Path, PathBuf};

use tauto_syntax::{Event, Limits, Tables, parse, sha256_hex};

fn corpus() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut out = Vec::new();
    let mut dirs = vec![root.clone()];
    while let Some(dir) = dirs.pop() {
        let Ok(rd) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in rd.flatten() {
            let p = e.path();
            let name = e.file_name();
            if p.is_dir() {
                if name != "target"
                    && name != "node_modules"
                    && !name.as_encoded_bytes().starts_with(b".")
                {
                    dirs.push(p);
                }
            } else if p.extension().is_some_and(|x| x == "taut" || x == "tauto") {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

#[test]
fn the_tables_still_match_tauto_par() {
    let par = include_str!("data/tauto.par");
    let t = Tables::read(include_str!("data/tauto.tables")).unwrap();
    // The table is a function of the grammar's text; a changed tauto.par needs a new table.
    let current = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../tauto-parol/tauto.par"),
    )
    .unwrap();
    assert_eq!(
        par, current,
        "tests/data/tauto.par is out of date: run bash scripts/generate-tauto-grammar.sh"
    );
    assert_eq!(
        t.grammar_sha256(),
        sha256_hex(par.as_bytes()),
        "tests/data/tauto.tables is out of date: run bash scripts/generate-grammar-tables.sh"
    );
    assert_eq!(t.max_k(), 2);
}

#[test]
fn agrees_with_the_generated_parser_on_the_repository_programs() {
    let t = Tables::read(include_str!("data/tauto.tables")).unwrap();
    let files = corpus();
    assert!(files.len() > 10, "found {} programs", files.len());
    let (mut ok, mut bad) = (0, 0);
    for f in &files {
        let source = std::fs::read_to_string(f).unwrap();
        let theirs = tauto_parol::parse(&source);
        let ours = parse(
            &t,
            &source,
            0,
            &Limits {
                max_input: usize::MAX,
                max_stack: 1 << 20,
            },
        );
        match (theirs.is_ok(), &ours) {
            (true, Ok(events)) => {
                ok += 1;
                let ours: Vec<(u32, u32)> = events
                    .iter()
                    .filter_map(|e| match e {
                        Event::Token(tok) if !t.is_skipped(tok.terminal) => {
                            Some((tok.start, tok.end))
                        }
                        _ => None,
                    })
                    .collect();
                let theirs: Vec<(u32, u32)> = theirs
                    .cst
                    .terminals()
                    .into_iter()
                    .filter(|(k, _)| !tauto_parol::is_trivia(*k))
                    .map(|(_, s)| (s.start, s.end))
                    .collect();
                assert_eq!(ours, theirs, "{}", f.display());
            }
            (false, Err(_)) => bad += 1,
            (a, b) => panic!(
                "{}: generated parser ok={a}, this crate {:?}",
                f.display(),
                b.as_ref().err()
            ),
        }
    }
    eprintln!("{ok} programs parse in both, {bad} are refused by both");
    assert!(ok > 10);
}

#[test]
fn accepts_and_refuses_the_same_cut_programs() {
    let t = Tables::read(include_str!("data/tauto.tables")).unwrap();
    let limits = Limits {
        max_input: usize::MAX,
        max_stack: 1 << 20,
    };
    let files = corpus();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get());
    let checked: usize = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                std::thread::Builder::new()
                    .stack_size(256 << 20)
                    .spawn_scoped(scope, || {
                        let mut checked = 0;
                        loop {
                            let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            let Some(f) = files.get(i) else {
                                return checked;
                            };
                            checked += check_cuts(&t, &limits, f);
                        }
                    })
                    .unwrap()
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).sum()
    });
    assert!(checked > 200, "{checked}");
}

fn check_cuts(t: &Tables, limits: &Limits, f: &Path) -> usize {
    let mut checked = 0;
    {
        let source = std::fs::read_to_string(f).unwrap();
        // Cut at about 25 places, on character boundaries, and drop a line from the middle.
        let step = (source.len() / 25).max(1);
        let mut cuts: Vec<String> = (step..source.len())
            .step_by(step)
            .filter(|&i| source.is_char_boundary(i))
            .map(|i| source[..i].to_string())
            .collect();
        let lines: Vec<&str> = source.lines().collect();
        if lines.len() > 4 {
            let mid = lines.len() / 2;
            cuts.push(
                lines
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != mid)
                    .map(|(_, l)| format!("{l}\n"))
                    .collect(),
            );
        }
        for text in cuts {
            let theirs = tauto_parol::parse(&text).is_ok();
            let ours = parse(t, &text, 0, limits).is_ok();
            assert_eq!(theirs, ours, "{}: cut at {} bytes", f.display(), text.len());
            checked += 1;
        }
    }
    checked
}
