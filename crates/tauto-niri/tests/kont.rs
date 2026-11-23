//! Every function of the tier `O` or `M` of every case that shows
//! something, split into its continuations (`tauto_nir::kont`): each split
//! is closed (`kont::check`). What the form refuses is only counted.

use std::path::Path;

use tauto_nir::Tier;
use tauto_test_suite::RustCase;

fn outcome(case: &RustCase) -> Option<String> {
    let pkg = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| case.compile("rust")));
    let Ok(Ok(mut pkg)) = pkg else {
        return None;
    };
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    let mut out: Vec<String> = Vec::new();
    for f in pkg.fns.iter().filter(|f| f.tier >= Tier::O) {
        match tauto_nir::kont::split(f) {
            Ok(s) => match tauto_nir::kont::check(&s) {
                Ok(()) => out.push(format!("split {}", s.fns.len())),
                Err(e) => {
                    if std::env::var_os("KONT_DEBUG").is_some() {
                        eprintln!("{:#?}\n{:#?}", f.body, s);
                    }
                    out.push(format!("BROKEN {e}"))
                }
            },
            Err(e) => out.push(format!("refused: {e}")),
        }
    }
    if out.is_empty() {
        return None;
    }
    // The number of continuations moves with the code; the list keeps how
    // each function ends.
    let mut kinds: Vec<String> = out
        .iter()
        .map(|o| {
            if o.starts_with("split") {
                "split".into()
            } else {
                o.clone()
            }
        })
        .collect();
    kinds.sort();
    kinds.dedup();
    Some(kinds.join("; "))
}

#[test]
fn every_resuming_function_splits_closed() {
    tauto_messages::install();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases");
    let cases: Vec<RustCase> = tauto_test_suite::rust_cases(&root)
        .unwrap()
        .into_iter()
        .filter(|c| c.stdout.is_some() && c.run_error.is_none())
        .filter(|c| {
            std::env::var("NIRI_ONLY").map_or(true, |o| o.split(',').any(|o| c.name.ends_with(o)))
        })
        .collect();
    let got: Vec<String> = tauto_test_suite::parallel_map(
        &cases,
        |_| (),
        |_, _, c| {
            outcome(c)
                .map(|o| format!("{}\t{o}", c.name))
                .unwrap_or_default()
        },
    )
    .into_iter()
    .filter(|l| !l.is_empty())
    .collect();
    let broken: Vec<&String> = got.iter().filter(|l| l.contains("BROKEN")).collect();
    assert!(
        broken.is_empty(),
        "splits that are not closed:\n{}",
        broken
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n")
    );
    let refused = got.iter().filter(|l| l.contains("refused")).count();
    eprintln!(
        "{} cases split, {refused} with a function the form refuses",
        got.len()
    );
}

#[test]
fn a_continuation_run_many_times_names_what_it_copies() {
    tauto_messages::install();
    let mut pkg = tauto::nir::compile(
        r#"
effect ask(): u64 resume ω
fn twice(t: Text): u64 ! {ask} {
  let n := perform ask()
  n + Text::len(t)
}
let r := handle { twice("ab") } with { ask(), k => k(1) + k(2) }
show(&r)
"#,
    )
    .unwrap_or_else(|e| panic!("{e:?}"));
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    let f = pkg
        .fns
        .iter()
        .find(|f| f.source.as_str().ends_with("twice"))
        .unwrap_or_else(|| {
            panic!(
                "{:?}",
                pkg.fns
                    .iter()
                    .map(|f| (f.source.as_str().to_string(), f.tier))
                    .collect::<Vec<_>>()
            )
        });
    let s = tauto_nir::kont::split(f).unwrap();
    tauto_nir::kont::check(&s).unwrap();
    // The body up to the point, and what follows it, taking `n` and
    // keeping `t`.
    assert_eq!(s.fns.len(), 2);
    let after = &s.fns[1];
    assert_eq!(after.kind, tauto_nir::kont::KontKind::Point);
    assert_eq!(after.arg.as_ref().map(|(l, _)| l.name.as_str()), Some("n"));
    assert!(after.env.iter().any(|(l, _)| l.name == "t"));
    // `ask` resumes many times: the text it keeps is copied each time.
    assert_eq!(s.cloned, vec![tauto_nir::Ty::Text]);
    // The locals the split binds depend only on the function: splitting it
    // again, after other splits, gives the same continuations.
    let _ = tauto_nir::kont::split(f).unwrap();
    assert_eq!(
        format!("{:?}", tauto_nir::kont::split(f).unwrap()),
        format!("{s:?}")
    );
}

#[test]
fn a_continuation_keeps_a_function_it_only_calls() {
    tauto_messages::install();
    let mut pkg = tauto::nir::compile(
        r#"
effect ask(): u64 resume ω
fn twice<!e>(body: () -> u64 ! e): u64 ! e { body() + body() }
let r := handle { twice(() => perform ask()) } with { ask(), k => k(1) + k(2) }
show(&r)
"#,
    )
    .unwrap_or_else(|e| panic!("{e:?}"));
    tauto_nir::anf::normalize(&mut pkg);
    tauto_nir::ownership::insert(&mut pkg);
    let f = pkg
        .fns
        .iter()
        .find(|f| f.source.as_str().ends_with("twice"))
        .expect("twice");
    let s = tauto_nir::kont::split(f).unwrap();
    tauto_nir::kont::check(&s).unwrap();
    // What follows the first call calls `body` again.
    let after = &s.fns[1];
    assert!(after.env.iter().any(|(l, _)| l.name == "body"));
}
