//! The incremental checker says what `tauto check` says, and does less work
//! when little changed.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use tauto::program::LoadError;
use tauto::report::{self, Report};
use tauto_analyzer::assist::suggest;
use tauto_analyzer::{Options, Stats, Workspace};

/// A directory of test files, removed afterwards.
struct Dir(PathBuf);

impl Dir {
    fn new() -> Dir {
        static N: AtomicUsize = AtomicUsize::new(0);
        let dir = std::env::temp_dir().join(format!(
            "tauto-analyzer-{}-{}",
            std::process::id(),
            N.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&dir).unwrap();
        Dir(dir.canonicalize().unwrap())
    }

    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        std::fs::write(&path, text).unwrap();
        path
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn workspace() -> Workspace {
    // A small interval, so that a replay is seen in a program this short.
    Workspace::with_options(Options {
        checkpoint_interval: 3,
        proof_cache: false,
    })
}

/// The answer of `tauto check` for the same texts.
fn batch(path: &Path, text: Option<&str>) -> Result<Report, String> {
    report::check_report(path, text).map_err(|e| e.to_string())
}

/// A fresh name (`eff'505`) carries a counter of the thread's, which differs
/// between two runs of the same kernel; the names are the same up to it.
fn unnumbered(json: &str) -> String {
    let mut out = String::new();
    let mut chars = json.chars().peekable();
    while let Some(c) = chars.next() {
        out.push(c);
        if c == '\'' {
            while chars.next_if(char::is_ascii_digit).is_some() {}
        }
    }
    out
}

/// The incremental report and the batch one agree; a program that does not
/// load fails the same way, its error shown as `tauto check` shows it.
fn same(a: &Result<Report, LoadError>, b: &Result<Report, String>) {
    match (a, b) {
        (Ok(a), Ok(b)) => {
            assert_eq!(a.text(), b.text());
            assert_eq!(a.json().render(), b.json().render());
            assert_eq!(
                unnumbered(&a.library_json().render()),
                unnumbered(&b.library_json().render())
            );
        }
        (Err(a), Err(b)) => assert_eq!(&a.to_string(), b),
        (a, b) => panic!(
            "incremental {:?}, batch {:?}",
            a.as_ref().map(|_| "ok"),
            b.as_ref().map(|_| "ok")
        ),
    }
}

fn since(now: Stats, before: Stats) -> Stats {
    Stats {
        loads: now.loads - before.loads,
        checked: now.checked - before.checked,
        replayed: now.replayed - before.replayed,
        memo_hits: now.memo_hits - before.memo_hits,
    }
}

fn lib_source() -> &'static str {
    r#"theorem and_swap(A: Prop, B: Prop, p: A ∧ B): B ∧ A {
  AndIntro(B, A, And::right(A, B, p), And::left(A, B, p))
}

theorem compose(A: Prop, B: Prop, C: Prop, f: (A) -> B, g: (B) -> C): (A) -> C {
  a => g(f(a))
}

theorem id_proof(A: Prop, a: A): A {
  a
}
"#
}

fn main_text(middle: &str) -> String {
    r#"import "lib.taut"

theorem swap_twice(A: Prop, B: Prop, p: A ∧ B): A ∧ B {
  and_swap(B, A, and_swap(A, B, p))
}

theorem uses_id(A: Prop, a: A): A {
  id_proof(A, a)
}

// nothing here

theorem last_one(A: Prop, a: A): A {
  id_proof(A, id_proof(A, a))
}
"#
    .to_string()
    .replace("// nothing here", middle)
}

#[test]
fn a_whole_program_checks_as_the_batch_checker_does() {
    let dir = Dir::new();
    dir.write("lib.taut", lib_source());
    let main = dir.write("main.taut", &main_text("// nothing here"));
    let ws = workspace();
    let inc = ws.report(&main);
    same(&inc, &batch(&main, None));
    let stats = ws.stats(&main);
    assert_eq!(stats.loads, 1);
    assert_eq!(stats.checked, 6, "{stats:?}");
}

#[test]
fn a_proof_may_use_a_lemma_written_after_it_as_in_the_batch_checker() {
    let dir = Dir::new();
    let main = dir.write(
        "main.taut",
        r#"theorem first(A: Prop, a: A): A {
  later(A, a)
}

theorem later(A: Prop, a: A): A {
  a
}
"#,
    );
    let ws = workspace();
    let inc = ws.report(&main);
    let batch = batch(&main, None);
    same(&inc, &batch);
    assert!(
        !inc.unwrap().text().contains("not defined"),
        "the lemma is checked before the proof that uses it"
    );
}

#[test]
fn asking_again_without_a_change_does_no_work() {
    let dir = Dir::new();
    dir.write("lib.taut", lib_source());
    let main = dir.write("main.taut", &main_text("// nothing here"));
    let ws = workspace();
    ws.report(&main).unwrap();
    let before = ws.stats(&main);
    ws.report(&main).unwrap();
    assert_eq!(ws.stats(&main), before);
}

#[test]
fn changing_a_proof_checks_that_declaration_only() {
    let dir = Dir::new();
    dir.write("lib.taut", lib_source());
    let text = main_text("// nothing here");
    let main = dir.write("main.taut", &text);
    let mut ws = workspace();
    ws.report(&main).unwrap();
    let before = ws.stats(&main);
    // Another proof of the same statement.
    let edited = text.replace(
        "  id_proof(A, a)\n",
        "  And::left(A, A, AndIntro(A, A, a, a))\n",
    );
    assert_ne!(edited, text);
    ws.set_text(&main, edited.clone());
    let inc = ws.report(&main);
    same(&inc, &batch(&main, Some(&edited)));
    let work = since(ws.stats(&main), before);
    assert_eq!(work.loads, 1);
    assert_eq!(work.checked, 1, "{work:?}");
    assert!(work.replayed < 3, "{work:?}");
}

#[test]
fn changing_a_statement_checks_what_uses_it_again() {
    let dir = Dir::new();
    dir.write("lib.taut", lib_source());
    let text = main_text("// nothing here");
    let main = dir.write("main.taut", &text);
    let mut ws = workspace();
    ws.report(&main).unwrap();
    // `uses_id` asks for a different theorem, so `last_one`'s proof (which
    // calls `id_proof` on its own) is untouched but `uses_id` is not.
    let edited = text.replace(
        r#"theorem uses_id(A: Prop, a: A): A {
  id_proof(A, a)
}"#,
        r#"theorem uses_id(A: Prop, a: A): B {
  id_proof(A, a)
}"#,
    );
    ws.set_text(&main, edited.clone());
    let inc = ws.report(&main);
    same(&inc, &batch(&main, Some(&edited)));
    assert!(inc.unwrap().status() == report::Status::Failed);
}

#[test]
fn an_edit_in_the_imported_file_reaches_what_imports_it() {
    let dir = Dir::new();
    let lib = dir.write("lib.taut", lib_source());
    let main = dir.write("main.taut", &main_text("// nothing here"));
    let mut ws = workspace();
    ws.report(&main).unwrap();
    let before = ws.stats(&main);
    // `id_proof` is stated differently: everything that calls it is checked
    // again, the rest of the file is not.
    let edited = lib_source().replace(
        r#"theorem id_proof(A: Prop, a: A): A {"#,
        r#"theorem id_proof(A: Prop, a: A, extra: A): A {"#,
    );
    std::fs::write(&lib, &edited).unwrap();
    ws.refresh(&lib);
    let inc = ws.report(&main);
    same(&inc, &batch(&main, None));
    assert!(inc.unwrap().status() == report::Status::Failed);
    assert!(since(ws.stats(&main), before).checked < 6);
}

#[test]
fn a_statement_that_only_moved_is_not_checked_again_and_its_places_follow() {
    let dir = Dir::new();
    dir.write("lib.taut", lib_source());
    let text = main_text(
        r#"theorem wrong(): 2 + 2 = 5 {
  Refl(Nat, 4)
}"#,
    );
    let main = dir.write("main.taut", &text);
    let mut ws = workspace();
    ws.report(&main).unwrap();
    let before = ws.stats(&main);
    let edited = format!("// a new first line\n\n{text}");
    ws.set_text(&main, edited.clone());
    let inc = ws.report(&main);
    same(&inc, &batch(&main, Some(&edited)));
    let work = since(ws.stats(&main), before);
    assert_eq!(work.checked, 0, "{work:?}");
}

/// Parentheses leave no trace in the statement, but they move the hole: the
/// hole is where the new text has it, and a fill of it lands there.
#[test]
fn parentheses_added_before_a_hole_move_it() {
    let dir = Dir::new();
    dir.write("lib.taut", lib_source());
    let text = main_text(
        r#"theorem pick(A: Prop, a: A): A {
  id_proof(A, ?h)
}"#,
    );
    let main = dir.write("main.taut", &text);
    let mut ws = workspace();
    ws.report(&main).unwrap();
    let edited = main_text(
        r#"theorem pick(A: Prop, a: A): A {
  id_proof((A), ?h)
}"#,
    );
    ws.set_text(&main, edited.clone());
    let (report, holes) = ws.goals(&main, None).unwrap();
    let span = holes[0].goal.span;
    assert_eq!(&edited[span.start as usize..span.end as usize], "?h");
    same(&Ok::<_, LoadError>(report), &batch(&main, Some(&edited)));
    assert!(ws.try_fill(&main, "h", "a").unwrap().accepted);
}

#[test]
fn a_file_that_does_not_read_is_the_error_the_batch_checker_gives() {
    let dir = Dir::new();
    dir.write("lib.taut", lib_source());
    let text = main_text("// nothing here");
    let main = dir.write("main.taut", &text);
    let mut ws = workspace();
    ws.report(&main).unwrap();
    let broken = r#"import "lib.taut"

theorem swap_twice(A: Prop, B: Prop, p: A ∧ B): A ∧ B {
  and_swap(B, A, and_swap(A, B, p))
}

theorem uses_id(A: Prop, a: A): A {
  id_proof(A, a)
}

// nothing here

theorem last_one(A: Prop, a: A): A {
  id_proof(A, id_proof(A, a))
}

theorem (((
"#
    .to_string();
    ws.set_text(&main, broken.clone());
    same(&ws.report(&main), &batch(&main, Some(&broken)));
    // And back.
    ws.set_text(&main, text.clone());
    same(&ws.report(&main), &batch(&main, Some(&text)));
}

#[test]
fn a_missing_import_is_an_error() {
    let dir = Dir::new();
    let main = dir.write(
        "main.taut",
        r#"import "nowhere.taut"
"#,
    );
    let ws = workspace();
    let inc = ws.report(&main);
    assert!(inc.is_err());
}

fn with_holes_source() -> &'static str {
    r#"theorem first(A: Prop, a: A): A {
  ?one
}

theorem second(A: Prop, B: Prop, p: A ∧ B): B ∧ A {
  AndIntro(B, A, ?right, ?left)
}

theorem third(A: Prop, a: A): A {
  a
}
"#
}

#[test]
fn holes_have_their_goals_and_a_candidate_is_tried_without_being_kept() {
    let dir = Dir::new();
    let file = dir.write("holes.taut", with_holes_source());
    let mut ws = workspace();
    let (report, holes) = ws.goals(&file, None).unwrap();
    assert_eq!(report.status(), report::Status::Incomplete);
    let names: Vec<_> = holes.iter().map(|h| h.goal.name.as_str()).collect();
    assert_eq!(names, ["one", "right", "left"]);
    same(&Ok::<_, LoadError>(report), &batch(&file, None));

    let before = ws.stats(&file);
    let wrong = ws.try_fill(&file, "right", "p").unwrap();
    assert!(!wrong.accepted);
    let right = ws.try_fill(&file, "right", "And::right(A, B, p)").unwrap();
    assert!(right.accepted);
    // Nothing was kept: the holes are all still there, the same ones.
    let (_, holes) = ws.goals(&file, None).unwrap();
    assert_eq!(holes.len(), 3);
    same(&ws.report(&file), &batch(&file, None));
    // The other declarations were not checked for any of it.
    let work = since(ws.stats(&file), before);
    assert!(work.checked <= 6, "{work:?}");
}

#[test]
fn suggest_finds_the_constants_of_the_program_as_the_batch_checker_does() {
    let dir = Dir::new();
    let file = dir.write("holes.taut", with_holes_source());
    let mut ws = workspace();
    let (report, holes) = ws.goals(&file, None).unwrap();
    let names = |report: &Report, hole: &tauto::report::Hole| -> Vec<String> {
        suggest(report, hole, 200)
            .into_iter()
            .map(|s| s.name)
            .collect()
    };
    let found = names(&report, &holes[1]);
    assert!(found.contains(&"And::left".to_string()), "{found:?}");
    let batch_report = batch(&file, None).unwrap();
    let batch_holes = batch_report.holes();
    assert_eq!(found, names(&batch_report, &batch_holes[1]));

    // An edit that adds a theorem adds a constant; an unchanged text keeps it.
    let text = r#"theorem first(A: Prop, a: A): A {
  ?one
}

theorem second(A: Prop, B: Prop, p: A ∧ B): B ∧ A {
  AndIntro(B, A, ?right, ?left)
}

theorem third(A: Prop, a: A): A {
  a
}

theorem fourth(A: Prop, a: A): A {
  a
}
"#
    .to_owned();
    ws.set_text(&file, text);
    let (report, holes) = ws.goals(&file, None).unwrap();
    assert!(names(&report, &holes[0]).contains(&"fourth".to_string()));
    ws.set_text(&file, with_holes_source().to_string());
    let (report, holes) = ws.goals(&file, None).unwrap();
    assert!(!names(&report, &holes[0]).contains(&"fourth".to_string()));
}

#[test]
fn a_fill_goes_on_and_the_names_of_the_other_holes_stay() {
    let dir = Dir::new();
    let file = dir.write("holes.taut", with_holes_source());
    let mut ws = workspace();
    let filled = ws.fill(&file, "one", "a").unwrap();
    assert!(filled.accepted);
    let (report, holes) = ws.goals(&file, None).unwrap();
    let names: Vec<_> = holes.iter().map(|h| h.goal.name.as_str()).collect();
    assert_eq!(names, ["right", "left"]);
    // The workspace's text is the candidate; the disk was not written.
    assert_eq!(report.source(&holes[0].file), filled.candidate);
    assert_eq!(std::fs::read_to_string(&file).unwrap(), with_holes_source());
    same(
        &Ok::<_, LoadError>(report),
        &batch(&file, Some(&filled.candidate)),
    );
}

#[test]
fn a_hole_the_candidate_does_not_fit_is_rejected_and_undone() {
    let dir = Dir::new();
    let file = dir.write("holes.taut", with_holes_source());
    let mut ws = workspace();
    let rejected = ws.fill(&file, "one", "a_name_that_is_nothing").unwrap();
    assert!(!rejected.accepted);
    let (_, holes) = ws.goals(&file, None).unwrap();
    assert_eq!(holes.len(), 3);
}

#[test]
fn the_checkers_and_the_batch_checker_agree_on_the_standard_library() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let ws = workspace();
    for file in ["std/List.taut", "std/Nat.taut", "meta/Typing.taut"] {
        let path = root.join(file);
        same(&ws.report(&path), &batch(&path, None));
    }
}

#[test]
fn editing_the_last_theorem_of_a_long_file_checks_one_declaration() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let path = root.join("std/Nat.taut");
    let mut ws = workspace();
    ws.report(&path).unwrap();
    let text = std::fs::read_to_string(&path).unwrap();
    let before = ws.stats(&path);
    // A comment inside the last declaration's proof changes its text, not
    // its meaning.
    let at = text.rfind("\n}").unwrap();
    let edited = format!("{}\n  // edited{}", &text[..at], &text[at..]);
    ws.set_text(&path, edited.clone());
    same(&ws.report(&path), &batch(&path, Some(&edited)));
    let work = since(ws.stats(&path), before);
    assert_eq!(work.loads, 1);
    assert!(work.checked <= 1, "{work:?}");
}

#[test]
fn universe_template_edits_invalidate_nonzero_instances() {
    tauto_messages::install();
    let dir = Dir::new();
    let original = r#"theorem uid<u: Level, A: Type(u)>(x: A): A { x }
theorem use_uid(): Type { uid(1, Type, Nat) }
"#;
    let file = dir.write("universes.taut", original);
    let mut ws = workspace();
    let initial = ws.report(&file);
    same(&initial, &batch(&file, None));
    assert!(!initial.unwrap().text().contains("FAILED"));
    let before = ws.stats(&file);
    // The checked uid@0 is unchanged, but uid@1 must no longer accept Type.
    let edited = original.replace("A: Type(u)", "A: Type(0)");
    ws.set_text(&file, edited.clone());
    let incremental = ws.report(&file);
    same(&incremental, &batch(&file, Some(&edited)));
    assert!(incremental.unwrap().text().contains("FAILED"));
    assert!(since(ws.stats(&file), before).checked >= 2);
    ws.set_text(&file, original.to_owned());
    same(&ws.report(&file), &batch(&file, Some(original)));
}

#[test]
fn inductive_template_edits_invalidate_nonzero_instances() {
    tauto_messages::install();
    let dir = Dir::new();
    let original = r#"inductive UBox(u: Level, A: Type(u)): Type(u) { Ub(value: A): UBox(u, A) }
theorem use_box(A: Type1, x: UBox(1, A)): UBox(1, A) { x }
"#;
    let file = dir.write("inductive-universes.taut", original);
    let mut ws = workspace();
    let initial = ws.report(&file);
    same(&initial, &batch(&file, None));
    assert!(!initial.unwrap().text().contains("FAILED"));
    let edited = original.replace("A: Type(u)", "A: Type(0)");
    ws.set_text(&file, edited.clone());
    let incremental = ws.report(&file);
    same(&incremental, &batch(&file, Some(&edited)));
    assert!(incremental.unwrap().text().contains("FAILED"));
}
