use std::{fs, path::PathBuf};

use tauto::report::{check_report, find_hole};
use tauto_analyzer::lemma_search::{select, verify};

struct Fixture(PathBuf);
impl Fixture {
    fn new(name: &str, source: &str) -> Self {
        let dir =
            std::env::temp_dir().join(format!("tauto-lemma-search-{name}-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("main.taut"), source).unwrap();
        Self(dir)
    }
    fn path(&self) -> PathBuf {
        self.0.join("main.taut")
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn explicit_scope_filters_before_limit_and_preserves_order() {
    let f = Fixture::new(
        "scope",
        r#"theorem t<A: Prop>(a: A, b: A): A { ?h }"#,
    );
    let report = check_report(&f.path(), None).unwrap();
    let hole = find_hole(&report, &f.path(), "h").unwrap();
    let selected = select(&report, &hole, &["b".into()], 1).unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].term, "b");
    let both = select(&report, &hole, &["b".into(), "a".into(), "b".into()], 10).unwrap();
    assert_eq!(
        both.iter().map(|s| s.term.as_str()).collect::<Vec<_>>(),
        ["a", "b"]
    );
    assert!(select(&report, &hole, &["absent".into()], 1).is_err());
}

#[test]
fn wrong_type_is_not_a_candidate_or_a_checked_term() {
    let f = Fixture::new(
        "wrong",
        r#"theorem t<A: Prop>(a: A, n: Nat): A { ?h }"#,
    );
    let report = check_report(&f.path(), None).unwrap();
    let hole = find_hole(&report, &f.path(), "h").unwrap();
    assert!(
        select(&report, &hole, &["n".into()], 10)
            .unwrap()
            .is_empty()
    );
    assert_eq!(verify(&f.path(), "h", "n").status, "rejected");
    assert_eq!(verify(&f.path(), "h", "not_declared").status, "rejected");
    let valid = verify(&f.path(), "h", "a");
    assert_eq!(valid.status, "checked");
    assert_eq!(valid.axioms, Some(vec![]));
}

#[test]
fn accepted_partial_edits_are_not_verified_proofs() {
    let f = Fixture::new(
        "partial",
        r#"theorem t<A: Prop, B: Prop>(a: A, b: B): And(A, B) { ?h }"#,
    );
    let result = verify(&f.path(), "h", "and_intro(?left, ?right)");
    assert_eq!(result.status, "incomplete");
    assert_eq!(result.remaining_holes, ["left", "right"]);
    assert_eq!(result.axioms, None);
    let report = check_report(&f.path(), None).unwrap();
    let hole = find_hole(&report, &f.path(), "h").unwrap();
    let unresolved = select(&report, &hole, &["And::left".into()], 1).unwrap();
    assert!(!unresolved[0].args[0].unresolved_metas.is_empty());
    assert_ne!(
        verify(&f.path(), "h", &unresolved[0].term).status,
        "checked"
    );
}

#[test]
fn transitively_used_axioms_remain_visible() {
    let f = Fixture::new(
        "axioms",
        r#"axiom assumed(): Zero = Zero
theorem alias(): Zero = Zero { assumed() }
theorem t(): Zero = Zero { ?h }"#,
    );
    let result = verify(&f.path(), "h", "alias()");
    assert_eq!(result.status, "checked", "{:?}", result.diagnostic);
    assert_eq!(result.axioms, Some(vec!["assumed".into()]));
}

#[test]
fn only_loaded_imports_are_searchable_and_sources_are_unchanged() {
    let source = r#"import "lemmas.taut"
theorem t(): Zero = Zero { ?h }"#;
    let f = Fixture::new("imports", source);
    fs::write(
        f.0.join("lemmas.taut"),
        r#"pub theorem identity(): Zero = Zero { Refl(Nat, Zero) }"#,
    )
    .unwrap();
    fs::write(
        f.0.join("outside.taut"),
        r#"pub theorem outside(): Zero = Zero { Refl(Nat, Zero) }"#,
    )
    .unwrap();
    let report = check_report(&f.path(), None).unwrap();
    let hole = find_hole(&report, &f.path(), "h").unwrap();
    assert!(select(&report, &hole, &["outside".into()], 10).is_err());
    let selected = select(&report, &hole, &["identity".into()], 10).unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(verify(&f.path(), "h", &selected[0].term).status, "checked");
    assert_eq!(fs::read_to_string(f.path()).unwrap(), source);
}

#[test]
fn checked_target_does_not_hide_failures_elsewhere_in_file() {
    let f = Fixture::new(
        "other-failure",
        r#"theorem t<A: Prop>(a: A): A { ?h }
theorem broken(): False { Zero }"#,
    );
    let result = verify(&f.path(), "h", "a");
    assert_eq!(result.status, "checked");
    assert_eq!(result.file_status, Some("failed"));
}

#[test]
fn checked_target_does_not_hide_other_holes() {
    let f = Fixture::new(
        "other-hole",
        r#"theorem t<A: Prop>(a: A): A { ?h }
theorem unfinished<A: Prop>(a: A): A { ?other }"#,
    );
    let result = verify(&f.path(), "h", "a");
    assert_eq!(result.status, "checked");
    assert_eq!(result.file_status, Some("incomplete"));
    assert!(result.remaining_holes.is_empty());
}

#[test]
fn imported_transitive_axioms_are_not_an_implicit_whitelist() {
    let f = Fixture::new(
        "imported-axioms",
        r#"import "lemmas.taut"
theorem t(): Zero = Zero { ?h }"#,
    );
    fs::write(
        f.0.join("lemmas.taut"),
        r#"pub axiom assumed(): Zero = Zero
pub theorem alias(): Zero = Zero { assumed() }"#,
    )
    .unwrap();
    let report = check_report(&f.path(), None).unwrap();
    let hole = find_hole(&report, &f.path(), "h").unwrap();
    let selected = select(&report, &hole, &["alias".into()], 1).unwrap();
    let result = verify(&f.path(), "h", &selected[0].term);
    assert_eq!(result.status, "checked");
    assert_eq!(result.axioms, Some(vec!["assumed".into()]));
}
