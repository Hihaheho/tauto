//! ANF (and ANF with drops) trees -> block form -> trees, over every case.
use std::path::Path;

fn check(pkg: &tauto_nir::Package) -> (usize, Vec<String>, usize, usize, usize) {
    let mut fails = Vec::new();
    let (mut n, mut opaque, mut blocks) = (0, 0, 0);
    for f in &pkg.fns {
        n += 1;
        let bf = tauto_nir::blocks::lower_body(&f.body, f.tier);
        opaque += bf.opaque;
        blocks += bf.blocks.len();
        let (back, (dn, dbad)) = tauto_nir::blocks::rebuild_checked(&bf);
        DEC.lock().unwrap().0 += dn;
        DEC.lock().unwrap().1 += dbad;
        DEC.lock().unwrap().2 += bf.refutable;
        for fd in tauto_nir::blocks::check(pkg, f, &bf) {
            let cause = fd.message.rsplit_once('[').map(|(_, c)| c.trim_end_matches(']')).unwrap_or("");
            let key = format!("{:?} {cause}", fd.rule);
            PAIRS.lock().unwrap().insert(format!("{key} @ {}", tauto_nir::display_name(&f.source)));
            let mut v = RULES.lock().unwrap();
            *v.0.entry(key.clone()).or_default() += 1;
            if v.1.len() < 40 && !v.1.iter().any(|x: &String| x.starts_with(&key)) {
                v.1.push(format!("{key} | in {}: {}", tauto_nir::display_name(&f.source), fd.message));
            }
        }
        if std::env::var("NIR_BLOCKS_PRINT").is_ok_and(|n| tauto_nir::display_name(&f.source) == n.as_str()) {
            match tauto_nir::blocks::print(pkg, f, &bf) {
                Ok(t) => println!("{}\n{t}", tauto_nir::display_name(&f.source)),
                Err(e) => println!("print failed: {e}"),
            }
        }
        let (wn, wbad) = tauto_nir::blocks::check_wf(&bf);
        WF.lock().unwrap().0 += wn;
        WF.lock().unwrap().1 += wbad;
        let mut p2 = f.clone();
        p2.body = back.clone();
        let a = tauto_nir::text::print_fn(pkg, f).unwrap_or_default();
        let b = tauto_nir::text::print_fn(pkg, &p2).unwrap_or_default();
        if a != b {
            let line = a.lines().zip(b.lines()).find(|(x, y)| x != y)
                .map(|(x, y)| format!("{x}  ||  {y}")).unwrap_or_else(|| "length".into());
            fails.push(format!("TEXT {}: {line}", f.source));
        } else if format!("{:?}", f.body) != format!("{:?}", back) {
            fails.push(format!("TREE {}: text equal, tree differs (spans/hidden)", f.source));
        }
    }
    (n, fails, opaque, blocks, 0)
}

static RULES: std::sync::Mutex<(std::collections::BTreeMap<String, usize>, Vec<String>)> = std::sync::Mutex::new((std::collections::BTreeMap::new(), Vec::new()));
static PAIRS: std::sync::Mutex<std::collections::BTreeSet<String>> = std::sync::Mutex::new(std::collections::BTreeSet::new());
static DEC: std::sync::Mutex<(usize, usize, usize)> = std::sync::Mutex::new((0, 0, 0));
static WF: std::sync::Mutex<(usize, usize)> = std::sync::Mutex::new((0, 0));
static STATS: std::sync::Mutex<Vec<(usize, usize, usize)>> = std::sync::Mutex::new(Vec::new());

fn main() -> std::process::ExitCode {
    use tauto_test_suite::{Harness, harness_tests};

    const TEST: &str = "round_trip";
    let filter = match harness_tests(|| vec![TEST.into()]) {
        Harness::Listed => return std::process::ExitCode::SUCCESS,
        Harness::Run { positional, exact } => {
            let name = positional.into_iter().next();
            if exact {
                return if name.as_deref() == Some(TEST) {
                    run(None)
                } else {
                    std::process::ExitCode::SUCCESS
                };
            }
            name
        }
    };
    run(filter.as_deref())
}

fn run(filter: Option<&str>) -> std::process::ExitCode {
    tauto_messages::install();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases");
    let all: Vec<_> = tauto_test_suite::rust_cases(&root)
        .expect("the case files are read")
        .into_iter()
        .filter(|c| filter.is_none_or(|f| c.name.contains(f)))
        .collect();
    // The same source compiles to the same packages: the first case written
    // with it stands for the others.
    let mut seen = std::collections::HashSet::new();
    let cases: Vec<_> = all
        .iter()
        .filter(|c| c.compiled_source().is_none_or(|s| seen.insert(s)))
        .collect();
    const TARGETS: [&str; 2] = ["rust", "javascript"];
    let results = tauto_test_suite::parallel_map(
        &cases,
        |_| (),
        |_, _, case| {
            let mut checked = 0;
            let mut failures = Vec::new();
            let compiled = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                case.compile_backends(&TARGETS)
            }))
            .map(|packages| packages.into_iter().map(Ok).collect::<Vec<_>>())
            // A panic in one target leaves the other to be compiled alone.
            .unwrap_or_else(|_| {
                TARGETS
                    .iter()
                    .map(|target| {
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            case.compile(target)
                        }))
                    })
                    .collect()
            });
            for (target, compiled) in TARGETS.iter().zip(compiled) {
                let Ok(Ok(mut pkg)) = compiled else { continue };
                for form in ["anf", "anf+drops"] {
                    tauto_nir::anf::normalize(&mut pkg);
                    if form == "anf+drops" {
                        tauto_nir::ownership::insert(&mut pkg);
                    }
                    let (n, fails, opaque, blocks, _) = check(&pkg);
                    checked += 1;
                    STATS.lock().unwrap().push((n, opaque, blocks));
                    if !fails.is_empty() {
                        failures.push(format!("{} ({target}, {form}): {}", case.name, fails.join("\n    ")));
                    }
                }
            }
            (checked, failures)
        },
    );
    let checked: usize = results.iter().map(|r| r.0).sum();
    let failures: Vec<&String> = results.iter().flat_map(|r| &r.1).collect();
    for f in &failures {
        println!("FAIL {f}\n");
    }
    {
        let s = STATS.lock().unwrap();
        println!("fns {} opaque-leaves {} blocks {}", s.iter().map(|x| x.0).sum::<usize>(), s.iter().map(|x| x.1).sum::<usize>(), s.iter().map(|x| x.2).sum::<usize>());
    }
    {
        for p in PAIRS.lock().unwrap().iter().take(400) {
            println!("PAIR {p}");
        }
        let r = RULES.lock().unwrap();
        println!("wf findings by rule: {:?}", r.0);
        for x in &r.1 {
            println!("  e.g. {x}");
        }
    }
    let w = *WF.lock().unwrap();
    println!("region owners checked {} mismatched {}", w.0, w.1);
    let d = *DEC.lock().unwrap();
    println!("decisions read back {} differing {} refutable handler arms {}", d.0, d.1, d.2);
    println!(
        "{checked} packages of {} cases ({} inputs), {} failed",
        all.len(),
        cases.len(),
        failures.len()
    );
    if failures.is_empty() && checked > 0 {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::FAILURE
    }
}
