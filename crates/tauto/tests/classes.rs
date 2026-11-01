//! Proof erasure and filling instance-law holes through the Rust APIs.

const BASE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/Base.taut");

#[test]
fn a_class_is_extracted_as_a_class_with_its_laws_erased() {
    tauto_messages::install();
    let dir = std::env::temp_dir().join(format!("tauto-classes-{}-extract", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(
        &path,
        format!(
            r#"import "{}"
{}"#,
            BASE,
            r#"inductive P: Type {
  Mk: P
}
instance Ord(P) {
  fn compare(&a: P, &b: P): Ordering { Equal }
}
fn is_less<A>(a: A, b: A): Bool where Ord(A) {
  match Ord::compare(a, b): Bool {
    Less => true
    Equal => false
    Greater => false
  }
}
fn use_it(a: P, b: P): Bool { is_less(a, b) }
"#
        ),
    )
    .unwrap();
    // The laws of `Ord(P)` are not proved, and the program is extracted all
    // the same: nothing of a law is left in it. `Ord` is the prelude's class,
    // which Nib reads too, so it is not declared again, and its methods borrow.
    let nib = tauto::extract::extract_files(&[path]).unwrap();
    for wanted in [
        r#"instance Ord(P) {"#,
        r#"fn compare(&a: P, &b: P): Ordering"#,
        r#"fn is_less<A: Shared>(a: A, b: A): Bool where Ord(A) {"#,
        r#"match Ord::compare(&a, &b) {"#,
        r#"is_less(a, b)"#,
    ] {
        assert!(nib.contains(wanted), "{wanted}\n{nib}");
    }
    assert!(!nib.contains(r#"class Ord"#), "{nib}");
    assert!(!nib.contains(r#"instance Ord(nat)"#), "{nib}");
    assert!(!nib.contains(r#"law"#), "{nib}");
}

#[test]
fn a_class_of_the_program_is_extracted_as_written() {
    tauto_messages::install();
    let dir = std::env::temp_dir().join(format!("tauto-classes-{}-own", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(
        &path,
        format!(
            r#"import "{}"
{}"#,
            BASE,
            r#"class Key(A: Type) {
  fn key(a: A): Nat
  law same<a: A>(): Key::key(a) = Key::key(a)
}
instance Key(Nat) {
  fn key(a: Nat): Nat { a }
  law same<a: Nat>(): Key::key(a) = Key::key(a) { Refl }
}
fn key_of<A>(a: A): Nat where Key(A) { Key::key(a) }
"#
        ),
    )
    .unwrap();
    let nib = tauto::extract::extract_files(&[path]).unwrap();
    for wanted in [
        r#"class Key(A: Type) {
  fn key(a: A): nat
}"#,
        r#"instance Key(nat) {"#,
        r#"Key::key(a)"#,
    ] {
        assert!(nib.contains(wanted), "{wanted}\n{nib}");
    }
}

#[test]
fn a_law_not_written_is_filled_by_writing_it_into_the_instance() {
    tauto_messages::install();
    let dir = std::env::temp_dir().join(format!("tauto-classes-{}-fill", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.taut");
    std::fs::write(
        &path,
        format!(
            r#"import "{}"
{}"#,
            BASE,
            r#"
class Cmp(A: Type) {
  fn compare(a: A, b: A): Ordering
  law refl<a: A>(): Cmp::compare(a, a) = Equal
  law irrefl<a: A>(h: Cmp::compare(a, a) = Less): False
}

fn nat_cmp(a: Nat, b: Nat): Ordering {
  match a: Ordering {
    Zero => match b: Ordering {
      Zero => Equal
      Succ(b2) => Less
    }
    Succ(a2) => match b: Ordering {
      Zero => Greater
      Succ(b2) => nat_cmp(a2, b2)
    }
  }
}

theorem nat_cmp_refl(a: Nat): nat_cmp(a, a) = Equal {
  match a: nat_cmp(a, a) = Equal {
    Zero => Refl
    Succ(k) => nat_cmp_refl(k)
  }
}

instance Cmp(Nat) {
  fn compare(a: Nat, b: Nat): Ordering { nat_cmp(a, b) }
  law refl<a: Nat>(): Cmp::compare(a, a) = Equal { nat_cmp_refl(a) }
  law irrefl<a: Nat>(h: Cmp::compare(a, a) = Less): False {
    less_ne_equal(Eq::trans(Eq::sym(h), nat_cmp_refl(a)))
  }
}

inductive P: Type {
  Mk: P
}
instance Cmp(P) {
  fn compare(a: P, b: P): Ordering { Equal }
  law refl<a: P>(): Cmp::compare(a, a) = Equal { Refl }
}
theorem uses_the_missing_law(a: P, h: Cmp::compare(a, a) = Less): False {
  Cmp::irrefl(h)
}
theorem uses_a_law_it_has(a: P): Cmp::compare(a, a) = Equal { Cmp::refl() }
fn still_compares(a: P, b: P): Ordering { Cmp::compare(a, b) }
"#
        ),
    )
    .unwrap();
    let attempt = tauto::report::try_fill(
        &path,
        "law:Cmp(P)::irrefl",
        r#"False::elim(equal_ne_less(h))"#,
    )
    .unwrap();
    assert!(attempt.accepted);
    assert!(
        attempt.candidate.contains(r#"law irrefl<a: P>(h: Cmp::compare(a, a) = Less): False { False::elim(equal_ne_less(h)) }"#),
        "{}",
        attempt.candidate
    );
    // The laws are no longer incomplete.
    let closed: Vec<_> = attempt
        .report
        .holes()
        .into_iter()
        .filter(|h| h.goal.name.starts_with("law:"))
        .collect();
    assert!(closed.is_empty(), "{}", closed.len());
}
