use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

struct Temp(PathBuf);
impl Temp {
    fn new() -> Self {
        static ID: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "tauto-doc-{}-{}",
            std::process::id(),
            ID.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, path: &str, text: &str) -> PathBuf {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, text).unwrap();
        path
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn doc(input: &Path, output: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        .arg("doc")
        .arg(input)
        .arg("-o")
        .arg(output)
        .env("TAUTO_CACHE", "off")
        .output()
        .unwrap()
}
fn assert_code(out: &Output, code: i32) {
    assert_eq!(
        out.status.code(),
        Some(code),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn pages_highlight_sources_and_link_names_across_imports() {
    let tmp = Temp::new();
    tmp.write(
        "lib/shapes.taut",
        "// Shapes.\npub enum Shape {\n  Dot\n}\n\npub fn area(s: Shape): i64 { 0 }\n",
    );
    let main = tmp.write(
        "main.taut",
        "import \"lib/shapes.taut\"\n\nfn twice(n: i64): i64 { n + n }\n\nfn use_it(): i64 {\n  let area: i64 := 1\n  twice(area)\n}\n\nfn other(): i64 { area(Dot) }\n",
    );
    let output = tmp.0.join("docs");
    let out = doc(&main, &output);
    assert_code(&out, 0);
    let index = fs::read_to_string(output.join("index.html")).unwrap();
    assert!(
        index.contains("<a href=\"main.taut.html\">main.taut</a>"),
        "{index}"
    );
    assert!(
        index.contains("lib/shapes.taut.html#L6\">area</a>"),
        "{index}"
    );
    let page = fs::read_to_string(output.join("main.taut.html")).unwrap();
    // Line anchors, keywords and comments.
    assert!(page.contains("id=\"L3\""), "{page}");
    assert!(page.contains("<span class=\"kw\">fn</span>"), "{page}");
    // A call links within the file; a name from an import links to its page.
    assert!(page.contains("<a href=\"#L3\">twice</a>"), "{page}");
    assert!(page.contains("<a href=\"lib/shapes.taut.html#L6\">area</a>(<a href=\"lib/shapes.taut.html#L3\">Dot</a>)"), "{page}");
    // A local of the same name is not linked.
    assert!(page.contains("twice</a>(area)"), "{page}");
    let lib = fs::read_to_string(output.join("lib/shapes.taut.html")).unwrap();
    assert!(
        lib.contains("<span class=\"com\">// Shapes.</span>"),
        "{lib}"
    );
    assert!(lib.contains("href=\"../index.html\""), "{lib}");
    // Same input, same bytes.
    let again = tmp.0.join("again");
    assert_code(&doc(&main, &again), 0);
    assert_eq!(
        page,
        fs::read_to_string(again.join("main.taut.html")).unwrap()
    );
}

#[test]
fn package_discovery_obeys_sources_and_never_executes_runtime() {
    let tmp = Temp::new();
    tmp.write(
        "Tauto.eure",
        "package { name = \"doc-fixture\"\nversion = \"0.1.0\"\n}\n",
    );
    tmp.write(
        "src/main.taut",
        r#"fn twice(n: i64): i64 { n + n }
perform show("must-not-run", 1)
"#,
    );
    tmp.write("outside.taut", "not valid source !\n");
    let output = tmp.0.join("docs");
    let out = doc(&tmp.0, &output);
    assert_code(&out, 0);
    assert!(!String::from_utf8_lossy(&out.stdout).contains("must-not-run"));
    let html = fs::read_to_string(output.join("index.html")).unwrap();
    assert!(html.contains("twice"));
    assert!(!html.contains("outside.taut"));
    assert!(output.join("src/main.taut.html").is_file());
}

#[test]
fn imports_outside_the_root_and_markup_in_paths_stay_out() {
    let tmp = Temp::new();
    tmp.write("shared.taut", "pub fn shared(): i64 { 1 }\n");
    let entry = tmp.write(
        "pkg/main<&>.taut",
        "import \"../shared.taut\"\nfn main_value(): Text { \"<b>&</b>\" }\n",
    );
    let output = tmp.0.join("docs");
    assert_code(&doc(&entry, &output), 0);
    let index = fs::read_to_string(output.join("index.html")).unwrap();
    assert!(index.contains("main&lt;&amp;&gt;.taut"), "{index}");
    assert!(!index.contains("shared"), "{index}");
    let page = fs::read_to_string(output.join("main<&>.taut.html")).unwrap();
    assert!(page.contains("&lt;b&gt;&amp;&lt;/b&gt;"), "{page}");
    assert!(!tmp.0.join("shared.taut.html").exists());
}

#[test]
fn help_usage_and_existing_empty_output_are_safe() {
    let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["doc", "--help"])
        .output()
        .unwrap();
    assert_code(&out, 0);
    for args in [
        vec!["doc"],
        vec!["doc", "file.taut", "--bad"],
        vec!["doc", "file.taut", "-o"],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(args)
            .output()
            .unwrap();
        assert_code(&out, 2);
    }
    let tmp = Temp::new();
    let source = tmp.write(
        "main.taut",
        r#"fn identity(n: i64): i64 { n }
"#,
    );
    let output = tmp.0.join("docs");
    fs::create_dir(&output).unwrap();
    assert_code(&doc(&source, &output), 1);
    assert_eq!(fs::read_dir(&output).unwrap().count(), 0);
}

#[cfg(unix)]
#[test]
fn output_symlinks_are_not_followed() {
    let tmp = Temp::new();
    let source = tmp.write(
        "main.taut",
        r#"fn identity(n: i64): i64 { n }
"#,
    );
    let output = tmp.0.join("docs");
    let missing = tmp.0.join("missing");
    std::os::unix::fs::symlink(&missing, &output).unwrap();
    assert_code(&doc(&source, &output), 1);
    assert!(!missing.exists());
}

#[test]
fn pages_colour_the_tokens_inside_macros_as_an_editor_does() {
    let tmp = Temp::new();
    let main = tmp.write(
        "main.taut",
        "import std::proof::Lang { proof }\nimport std::proof::Forms { proof_by }\n\ntheorem t(): 1 = 1 {\n  proof!(```\n    By Refl.\n  ```)\n}\n",
    );
    let output = tmp.0.join("docs");
    let out = doc(&main, &output);
    assert_code(&out, 0);
    let page = fs::read_to_string(output.join("main.taut.html")).unwrap();
    // The text of the macro is split: its words take the editor's classes.
    assert!(page.contains("<span class=\"kw\">By</span>"), "{page}");
    // What no token colours is plain, not the colour of the text around it.
    assert!(!page.contains("<span class=\"str\">"), "{page}");
}
