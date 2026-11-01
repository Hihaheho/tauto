//! Array pattern inspection preserves the owned source and public API contract.
use std::path::Path;
use std::process::Command;

use tauto_rustgen::{Bindings, Options, Sources, workspace};

fn source_source() -> &'static str {
    r#"
enum Tree { Leaf(Text), Branch(Text, Tree, Tree) }
struct Entry { tag: u64, text: Text, tree: Tree }
enum Store { Stored(Array(Entry)) }
fn borrowed_length(&store: Store): u64 {
  match &store { Stored(values) => Array::len(values) }
}
fn borrowed_entry(&store: Store, index: u64): Option(Entry) {
  match &store { Stored(values) => match Array::get(values, index) { None => None, Some(entry) => Some(entry) } }
}
fn borrowed_direct(&store: Store, index: u64): Option(Entry) {
  match &store { Stored(values) => Array::get(values, index) }
}
enum Packed { Payload(Text, Text, Text, Text), Fork(Packed, Packed) }
fn child_projected(values: Array(Packed)): Packed {
  match Array::get(values, 0) {
    Some(Fork(child, _)) => child
    Some(value) => value
    None => Payload("", "", "", "")
  }
}
fn child_baseline(values: Array(Packed)): Packed {
  let found := Array::get(values, 0)
  match found {
    Some(Fork(child, _)) => child
    Some(value) => value
    None => Payload("", "", "", "")
  }
}
fn nested(values: Array(Entry)): u64 {
  match Array::get(values, 0) {
    Some(Entry { tag, text: _, tree: _ }) => match Array::get(values, 0) {
      Some(Entry { tag: second, text: _, tree: _ }) => tag + second
      None => 0
    }
    None => 0
  }
}
fn entries(text: Text): Array(Entry) {
  var values := Vec::new()
  Vec::push(&mut values, Entry { tag: 41, text: text,
    tree: Branch("root", Leaf("left"), Leaf("right")) })
  Vec::into_array(values)
}
fn projected(values: Array(Entry), index: u64): u64 {
  match Array::get(values, index) {
    Some(Entry { tag, text: _, tree: _ }) => tag
    None => 0
  }
}
fn baseline(values: Array(Entry), index: u64): u64 {
  let found := Array::get(values, index)
  match found {
    Some(Entry { tag, text: _, tree: _ }) => tag
    None => 0
  }
}
fn recursive(values: Array(Entry)): Text {
  match Array::get(values, 0) {
    Some(Entry { tree: Branch(_, Leaf("different"), _), tag: _, text: _ }) => "wrong"
    Some(Entry { tree: Branch(_, Leaf(text), _), tag: _, text: _ }) => text
    Some(_) => "other"
    None => "missing"
  }
}
fn whole(values: Array(Entry)): Entry {
  match Array::get(values, 0) {
    Some(item) => item
    None => Entry { tag: 0, text: "empty", tree: Leaf("empty") }
  }
}
fn owned(values: Array(Entry)): Option(Entry) { Array::get(values, 0) }
fn with_callback(values: Array(Entry), &f: (u64) -> u64): u64 {
  match Array::get(values, 0) {
    Some(Entry { tag, text: _, tree: _ }) => f(tag)
    None => 0
  }
}
fn capture(values: Array(Entry)): (() -> Text) {
  match Array::get(values, 0) {
    Some(Entry { text, tag: _, tree: _ }) => () => text
    None => () => "missing"
  }
}
var original := entries("old")
let selected := match Array::get(original, { original := entries("new"); 0 }) {
  Some(Entry { text, tag: _, tree: _ }) => { original := entries("body"); text }
  None => "missing"
}
perform show("snapshot", selected)
perform show("current", whole(original).text)
perform show("temporary", projected(entries("temporary"), 0))
perform show("recursive", recursive(original))
perform show("past-end", projected(original, 1))
let captured := capture(entries("captured"))
perform show("captured", captured())
"#
}

/// Builds `name` as an example of the generated package with Cargo, so the
/// runtime gets the dependencies its generated manifest declares.
fn build_example(dir: &Path, name: &str, release: bool) -> std::path::PathBuf {
    let mut cmd = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()));
    cmd.args(["build", "--quiet", "--example", name, "--manifest-path"])
        .arg(dir.join("Cargo.toml"))
        .env("CARGO_TARGET_DIR", dir.join("target"))
        .env("CARGO_BUILD_BUILD_DIR", dir.join("target"));
    if release {
        cmd.arg("--release");
    }
    let output = cmd.output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let profile = if release { "release" } else { "debug" };
    dir.join("target").join(profile).join("examples").join(name)
}

#[test]
fn owned_patterns_public_api_and_clone_counts() {
    tauto_messages::install();
    let expected = tauto::eval::run(source_source())
        .unwrap()
        .outputs
        .into_iter()
        .map(|(label, value)| format!("{label} = {value}\n"))
        .collect::<String>();
    let package = tauto_nir::compile_with(source_source(), true).unwrap();
    let ws = workspace(
        "array-match",
        &package,
        &Sources {
            file: "main.taut",
            text: source_source(),
        },
        &Bindings::default(),
        &Options::default(),
    );
    let dir = std::env::temp_dir().join(format!("tauto-array-match-{}", std::process::id()));
    ws.write(&dir).unwrap();
    // Count Text clones in the generated runtime, without changing production ABI.
    let runtime = dir.join("tauto-rt/src/lib.rs");
    let text = std::fs::read_to_string(&runtime).unwrap();
    assert!(text.contains("#[derive(Clone)]\npub enum Text"));
    let text = text.replacen("#[derive(Clone)]\npub enum Text", "pub enum Text", 1)
        + r#"
pub static TEXT_CLONES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
impl Clone for Text {
    fn clone(&self) -> Self {
        TEXT_CLONES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        match self { Self::Static(s) => Self::Static(s), Self::Shared(s) => Self::Shared(s.clone()) }
    }
}
"#;
    std::fs::write(runtime, text).unwrap();
    std::fs::create_dir_all(dir.join("examples")).unwrap();
    std::fs::write(
        dir.join("examples/caller.rs"),
        r#"
use array_match as generated;
use std::sync::atomic::Ordering::Relaxed;
use generated::api::{Entry, Tree, Packed};
use tauto_rt::{Rc, Text, TEXT_CLONES};
fn packed() -> tauto_rt::stdlib::Array<Packed> {
    let leaf = || Packed::Payload(Text::from("a".to_owned()), Text::from("b".to_owned()),
        Text::from("c".to_owned()), Text::from("d".to_owned()));
    vec![Packed::Fork(Rc::new(leaf()).into(), Rc::new(leaf()).into())].into()
}
fn main() {
    generated::run();
    let a: tauto_rt::stdlib::Array<Entry> = vec![Entry {
        tag: 41, text: Text::from("日本語".to_owned()),
        tree: Tree::Branch(Text::from("root".to_owned()),
            Rc::new(Tree::Leaf(Text::from("left".to_owned()))).into(),
            Rc::new(Tree::Leaf(Text::from("right".to_owned()))).into())
    }].into();
    let store = generated::api::Store::Stored(a.clone());
    assert_eq!(generated::api::borrowed_length(&store), 1);
    assert_eq!(generated::api::borrowed_entry(&store, 0).unwrap().tag, 41);
    assert!(generated::api::borrowed_entry(&store, u64::MAX).is_none());
    let saved = generated::api::borrowed_direct(&store, 0).unwrap();
    drop(store);
    assert_eq!(saved.text.as_ref(), "日本語");
    let unique_store = generated::api::Store::Stored(vec![saved].into());
    let selected = generated::api::borrowed_entry(&unique_store, 0).unwrap();
    drop(unique_store);
    assert_eq!(selected.text.as_ref(), "日本語");
    drop(selected);
    let empty_store = generated::api::Store::Stored(Vec::new().into());
    assert_eq!(generated::api::borrowed_length(&empty_store), 0);
    assert!(generated::api::borrowed_direct(&empty_store, 0).is_none());
    TEXT_CLONES.store(0, Relaxed);
    let old = generated::api::baseline(a.clone(), 0);
    let baseline_clones = TEXT_CLONES.swap(0, Relaxed);
    let new = generated::api::projected(a.clone(), 0);
    let projected_clones = TEXT_CLONES.swap(0, Relaxed);
    assert!(old == new);
    assert!(baseline_clones >= 2, "{baseline_clones}");
    assert_eq!(projected_clones, 0);
    eprintln!("Text clones: baseline={baseline_clones}, projected={projected_clones}");
    assert_eq!(generated::api::recursive(a.clone()).as_ref(), "left");
    assert_eq!(TEXT_CLONES.swap(0, Relaxed), 1);
    let extra = 1_u64;
    let callback = |tag| { assert_eq!(Rc::strong_count(&a), 1); tag + extra };
    assert_eq!(generated::api::with_callback(a.clone(), &callback), 42);
    assert_eq!(generated::api::nested(a.clone()), 82);
    let empty: tauto_rt::stdlib::Array<Entry> = vec![].into();
    assert_eq!(generated::api::projected(empty, 0), 0);
    assert_eq!(generated::api::projected(a.clone(), u64::MAX), 0);
    let mut shared = a.clone();
    Rc::make_mut(&mut shared)[0].tag = 99;
    assert_eq!(generated::api::projected(a.clone(), 0), 41);
    assert_eq!(generated::api::projected(shared, 0), 99);
    let mut owned = generated::api::whole(a.clone());
    owned.tag = 73;
    assert_eq!(generated::api::projected(a.clone(), 0), 41);
    let copied = generated::api::owned(a.clone()).unwrap();
    drop(a);
    assert_eq!(copied.text.as_ref(), "日本語");
    assert_eq!(owned.tag, 73);
    assert_eq!(owned.text.as_ref(), "日本語");
    let unique = packed();
    TEXT_CLONES.store(0, Relaxed);
    let old = generated::api::child_baseline(unique);
    let unique_baseline = TEXT_CLONES.swap(0, Relaxed);
    let unique = packed();
    let new = generated::api::child_projected(unique);
    let unique_projected = TEXT_CLONES.swap(0, Relaxed);
    assert!(old == new);
    assert_eq!(unique_baseline, 0);
    assert_eq!(unique_projected, 0);
    let shared = packed();
    let old = generated::api::child_baseline(shared.clone());
    let shared_baseline = TEXT_CLONES.swap(0, Relaxed);
    let new = generated::api::child_projected(shared.clone());
    let shared_projected = TEXT_CLONES.swap(0, Relaxed);
    assert!(old == new);
    assert_eq!(shared_baseline, 4);
    assert_eq!(shared_projected, 4);
    eprintln!("recursive child Text clones: unique baseline={unique_baseline}, projected={unique_projected}; shared baseline={shared_baseline}, projected={shared_projected}");
}
"#,
    )
    .unwrap();
    let caller = build_example(&dir, "caller", true);
    let output = Command::new(caller).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    eprintln!("{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
    let javascript = tauto_jsgen::generate(&package).unwrap() + "\nawait run();\n";
    std::fs::write(dir.join("program.mjs"), javascript).unwrap();
    let output = Command::new("node")
        .arg(dir.join("program.mjs"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn borrowed_results_are_still_rejected() {
    tauto_messages::install();
    for source in [
        r#"fn invalid(values: Array(Text)): &Text { match Array::get(values, 0) { Some(text) => text, None => "missing" } }"#,
        r#"enum Tree { Leaf(Text), Branch(Tree, Tree) }
fn invalid(values: Array(Tree)): &Tree { match Array::get(values, 0) { Some(tree) => tree, None => Leaf("missing") } }"#,
    ] {
        let error = tauto_nir::compile(source).unwrap_err().to_string();
        assert!(error.contains("borrow"), "{error}");
    }
}

#[test]
fn guards_and_non_immediate_matches_keep_the_owned_lookup() {
    tauto_messages::install();
    for source in [
        r#"pub fn f(values: Array(u64)): u64 { match Array::get(values, 0) { Some(x) if x > 0 => x, Some(y) => y, None => 0 } }"#,
        r#"pub fn f(values: Array(u64)): Option(u64) { match Array::get(values, 0) { whole => whole } }"#,
        r#"pub fn f(values: Array(u64)): u64 { let found := Array::get(values, 0); match found { Some(x) => x, None => 0 } }"#,
        r#"pub fn get(values: Array(u64)): Option(u64) { Array::get(values, 0) }
fn f(values: Array(u64)): u64 { match get(values) { Some(x) => x, None => 0 } }"#,
        r#"pub fn f(values: Array(u64)): u64 { let found := Array::get(values, 0); match &found { Some(x) => x, None => 0 } }"#,
    ] {
        let package = tauto_nir::compile_with(source, true).unwrap();
        let ws = workspace(
            "array-fallback",
            &package,
            &Sources {
                file: "main.taut",
                text: source,
            },
            &Bindings::default(),
            &Options::default(),
        );
        let native = &ws
            .files
            .iter()
            .find(|(path, _)| path == "src/lib.rs")
            .unwrap()
            .1;
        let compact: String = native.chars().filter(|c| !c.is_whitespace()).collect();
        assert!(compact.contains("tauto_rt::stdlib::array_get("), "{native}");
        assert!(!compact.contains(".get(i)"), "{native}");
    }
}

#[test]
fn nested_matches_have_bounded_generated_size() {
    tauto_messages::install();
    let mut sizes = Vec::new();
    for depth in [1, 4, 8, 12] {
        let mut body = r#"1"#.to_owned();
        for level in 0..depth {
            body = format!(
                r#"match Array::get(values, 0) {{ Some(value{}) => {{ {} }}, None => 0 }}"#,
                level.to_string(),
                body
            );
        }
        let source = format!(r#"fn nested(values: Array(u64)): u64 {{ {} }}"#, body);
        let package = tauto_nir::compile_with(&source, true).unwrap();
        let ws = workspace(
            "array-nested",
            &package,
            &Sources {
                file: "main.taut",
                text: &source,
            },
            &Bindings::default(),
            &Options::default(),
        );
        let native = &ws
            .files
            .iter()
            .find(|(path, _)| path == "src/lib.rs")
            .unwrap()
            .1;
        let compact: String = native.chars().filter(|c| !c.is_whitespace()).collect();
        assert_eq!(
            compact.matches("Rc::strong_count").count(),
            1,
            "depth {depth}"
        );
        sizes.push(compact.len());
    }
    assert!(sizes[3] - sizes[2] < 2 * (sizes[2] - sizes[1]), "{sizes:?}");
    eprintln!("nested array match emitted bytes at depths 1/4/8/12: {sizes:?}");
}

#[test]
fn closures_are_scanned_and_handlers_are_conservative_boundaries() {
    tauto_messages::install();
    for (source, expected) in [
        (
            r#"pub fn f(values: Array(u64)): (() -> u64) { match Array::get(values, 0) { Some(first) => () => match Array::get(values, 0) { Some(second) => first + second, None => 0 }, None => () => 0 } }"#,
            1,
        ),
        (
            r#"effect stop(): Never resume 0
fn f(values: Array(u64)): u64 { match Array::get(values, 0) { Some(item) => handle { perform stop(); 0 } with { stop() => item }, None => 0 } }"#,
            0,
        ),
    ] {
        let package = tauto_nir::compile_with(source, true).unwrap();
        let ws = workspace(
            "array-boundaries",
            &package,
            &Sources {
                file: "main.taut",
                text: source,
            },
            &Bindings::default(),
            &Options::default(),
        );
        let native = &ws
            .files
            .iter()
            .find(|(path, _)| path == "src/lib.rs")
            .unwrap()
            .1;
        let compact: String = native.chars().filter(|c| !c.is_whitespace()).collect();
        assert_eq!(
            compact.matches("Rc::strong_count").count(),
            expected,
            "{native}"
        );
    }
}

#[test]
#[ignore = "runs the native same-build array pattern timing workload"]
fn time_array_patterns() {
    tauto_messages::install();
    let package = tauto_nir::compile_with(source_source(), true).unwrap();
    let ws = workspace(
        "array-timing",
        &package,
        &Sources {
            file: "main.taut",
            text: source_source(),
        },
        &Bindings::default(),
        &Options::default(),
    );
    let dir = std::env::temp_dir().join(format!("tauto-array-timing-{}", std::process::id()));
    ws.write(&dir).unwrap();
    std::fs::create_dir_all(dir.join("examples")).unwrap();
    std::fs::write(dir.join("examples/timing.rs"), r#"
use array_timing as generated;
use std::hint::black_box;
use std::time::Instant;
use generated::api::{Entry, Tree};
use tauto_rt::{Rc, Text, stdlib::Array};
#[inline(never)]
fn sample(f: fn(Array<Entry>, u64) -> u64, values: &Array<Entry>) -> (u64, u128) {
    let start = Instant::now();
    let mut total = 0_u64;
    for i in 0..2_000_000_u64 {
        total = total.wrapping_add(black_box(f(black_box(values.clone()), black_box(i & 1023))));
    }
    (total, start.elapsed().as_nanos())
}
fn main() {
    let values: Array<Entry> = (0..1024_u64).map(|tag| Entry {
        tag, text: Text::from(format!("日本語 shared payload {tag}")),
        tree: Tree::Branch(Text::from(format!("root {tag}")),
            Rc::new(Tree::Leaf(Text::from("left".to_owned()))).into(),
            Rc::new(Tree::Leaf(Text::from("right".to_owned()))).into())
    }).collect::<Vec<_>>().into();
    for i in 0..1025 { assert_eq!(generated::api::baseline(values.clone(), i), generated::api::projected(values.clone(), i)); }
    let _ = sample(generated::api::baseline, &values);
    let _ = sample(generated::api::projected, &values);
    for round in 0..9 {
        let (baseline, projected) = if round % 2 == 0 {
            (sample(generated::api::baseline, &values), sample(generated::api::projected, &values))
        } else {
            let projected = sample(generated::api::projected, &values);
            (sample(generated::api::baseline, &values), projected)
        };
        assert_eq!(baseline.0, projected.0);
        println!("{round}\t{}\t{}\t{}", baseline.1, projected.1, baseline.0);
    }
}
"#).unwrap();
    let timing = build_example(&dir, "timing", true);
    let output = Command::new(timing).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    print!("{}", String::from_utf8(output.stdout).unwrap());
    std::fs::remove_dir_all(dir).unwrap();
}
