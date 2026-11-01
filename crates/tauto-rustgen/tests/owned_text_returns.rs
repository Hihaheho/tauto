//! Owned Text conversion crosses only standard container return boundaries.
use std::path::Path;
use std::process::Command;
use tauto_rustgen::{Bindings, Options, Sources, workspace};

#[test]
fn nested_owned_results_convert_text_without_repeating_foreign_calls() {
    let source = r#"
extern {
  fn lookup(&value: Text): Option(Text)
  fn missing(): Option(Text)
  fn nested(ok: Bool): Result(Option(Text), Text)
  fn words(): Vec(Text)
  fn pair(): Pair(Text, Option(Text))
  fn deep(): Pair(Text, Vec(Result(Text, Pair(i64, Text))))
}
perform show("value", lookup("hello"))
perform show("missing", missing())
perform show("ok", nested(true))
perform show("err", nested(false))
perform show("words", Vec::into_list(words()))
perform show("pair", pair())
perform show("deep", deep())
"#;
    let manifest = tauto::manifest::parse(
        r#"rust { extern {
          lookup = "bridge::lookup"
          missing = "bridge::missing"
          nested = "bridge::nested"
          words = "bridge::words"
          pair = "bridge::pair"
          deep = "bridge::deep"
        } }"#,
        Path::new("Tauto.eure"),
    )
    .unwrap();
    let package = tauto_nir::compile(source).unwrap();
    let bindings = Bindings::resolve(&package, Some(&manifest), None).unwrap();
    let mut ws = workspace(
        "owned-text",
        &package,
        &Sources {
            file: "main.taut",
            text: source,
        },
        &bindings,
        &Options::default(),
    );
    let lib = &mut ws
        .files
        .iter_mut()
        .find(|(p, _)| p == "src/lib.rs")
        .unwrap()
        .1;
    lib.push_str(
        r#"
mod bridge {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    pub fn lookup(value: &str) -> Option<String> {
        assert_eq!(CALLS.fetch_add(1, Ordering::Relaxed), 0);
        Some(value.to_owned())
    }
    pub fn missing() -> Option<String> { None }
    pub fn nested(ok: bool) -> Result<Option<String>, String> {
        if ok { Ok(Some("日本語".into())) } else { Err("診断".into()) }
    }
    pub fn words() -> Vec<String> { vec!["一".into(), "二".into()] }
    pub fn pair() -> (String, Option<String>) { ("左".into(), Some("右".into())) }
    pub fn deep() -> (String, Vec<Result<String, (i64, String)>>) {
        ("外".into(), vec![Ok("内".into()), Err((73, "終".into()))])
    }
}
"#,
    );
    let dir = std::env::temp_dir().join(format!("tauto-owned-text-{}", std::process::id()));
    let target = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("owned-text-target");
    let binary = ws.build("owned-text", &dir, &target, false).unwrap();
    let out = Command::new(binary).output().unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let out = String::from_utf8(out.stdout).unwrap();
    for expected in [
        "hello",
        "None",
        "日本語",
        "診断",
        "一",
        "二",
        "左",
        "右",
        "外",
        "内",
        "73",
        "終",
    ] {
        assert!(out.contains(expected), "missing {expected}: {out}");
    }
    std::fs::remove_dir_all(dir).unwrap();
}
