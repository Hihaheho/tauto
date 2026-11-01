use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use tauto::report::{self, Report};
use tauto_analyzer::{Options, Workspace};

struct Dir(PathBuf);

impl Dir {
    fn new() -> Dir {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let dir = std::env::temp_dir().join(format!(
            "tauto-analyzer-localization-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
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

struct RestoreLanguage(Option<String>);

impl Drop for RestoreLanguage {
    fn drop(&mut self) {
        tauto_messages::set_language(self.0.as_deref());
    }
}

fn same(incremental: &Result<Report, String>, batch: &Result<Report, String>) {
    match (incremental, batch) {
        (Ok(a), Ok(b)) => {
            assert_eq!(a.text(), b.text());
            assert_eq!(a.json().render(), b.json().render());
        }
        (Err(a), Err(b)) => assert_eq!(a, b),
        (a, b) => panic!(
            "incremental {:?}, batch {:?}",
            a.as_ref().map(|_| "ok"),
            b.as_ref().map(|_| "ok")
        ),
    }
}

fn workspace() -> Workspace {
    Workspace::with_options(Options {
        checkpoint_interval: 3,
        proof_cache: false,
    })
}

fn batch(path: &Path, text: &str) -> Result<Report, String> {
    report::check_report(path, Some(text))
}

#[test]
fn expansion_diagnostics_are_memoized_independently_of_language() {
    tauto_messages::install();
    let _restore = RestoreLanguage(std::env::var("TAUTO_LANG").ok());
    let dir = Dir::new();
    let tables =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../tauto/tests/syntax_fixtures/.tauto-syntax");
    let copied_tables = dir.0.join(".tauto-syntax");
    std::fs::create_dir(&copied_tables).unwrap();
    for entry in std::fs::read_dir(tables).unwrap() {
        let entry = entry.unwrap();
        std::fs::copy(entry.path(), copied_tables.join(entry.file_name())).unwrap();
    }

    let library = r#"syntax!(math, ```par
%start Eqn
%title "math"
%%
Eqn: Sum Equals Sum;
Sum: Term { Plus Term };
Term: Num | Paren;
Paren: LParen Sum RParen;
Num: /[0-9]+/;
Equals: '=';
Plus: '+';
LParen: '(';
RParen: ')';
```) => struct Eqn, struct Paren, struct Sum, struct Sum_Rep1, enum Term,
  fn parse
pub macro fn math(e: math::Eqn): SynExpr ! {macro_error, Div} { quote { not_declared } }
"#.to_string();
    let original = r#"import "math.nib"
theorem t(): Nat { math!(`1 = 1`) }
"#.to_string();
    let lib_path = dir.write("math.nib", &library);
    let path = dir.write("main.nib", &original);

    for (language, phrase) in [("en", "in the expansion of"), ("ja", "の展開の中")] {
        assert!(tauto_messages::set_language(Some(language)));
        let mut ws = workspace();
        ws.set_text(&lib_path, library.clone());
        ws.set_text(&path, original.clone());
        let first = ws.report(&path).unwrap();
        let before = ws.stats(&path);
        assert!(first.text().contains(phrase), "{}", first.text());

        let other_language = if language == "en" { "ja" } else { "en" };
        let other_phrase = if language == "en" {
            "の展開の中"
        } else {
            "in the expansion of"
        };
        assert!(tauto_messages::set_language(Some(other_language)));
        assert!(first.text().contains(other_phrase), "{}", first.text());

        assert!(tauto_messages::set_language(Some(language)));
        let moved = format!("\n{original}");
        ws.set_text(&path, moved.clone());
        let after = ws.report(&path);
        assert!(after.as_ref().unwrap().text().contains(phrase));
        same(&after, &batch(&path, &moved));
        assert!(ws.stats(&path).checked > before.checked);
    }
}
