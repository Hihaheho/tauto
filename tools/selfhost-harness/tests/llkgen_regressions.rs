//! Generated schemas and scanners retain names, empty alternatives and Unicode bounds.
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use tauto_syntax::{Tables, TypeDef};

fn generator() -> &'static Path {
    static BIN: OnceLock<PathBuf> = OnceLock::new();
    BIN.get_or_init(|| selfhost_harness::tote_binary("syntaxgen").unwrap())
}

fn generate(label: &str, grammar: &str) -> Tables {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("llkgen-{label}"));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("grammar.par");
    std::fs::write(&path, format!("%start Root\n%%\n{grammar}\n")).unwrap();
    let out = Command::new(generator())
        .env("TAUTO_STEP_LIMIT", "200000000000")
        .args(["--allow-read", "--", "--gen", path.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    Tables::read(std::str::from_utf8(&out.stdout).unwrap()).unwrap()
}

fn accepts(tables: &Tables, source: &str) -> bool {
    tauto_syntax::parse(tables, source, 0, &Default::default()).is_ok()
}

#[test]
fn constructor_suffixes_are_checked_until_unique() {
    let tables = generate(
        "constructors",
        "Root: AB3 | A B | AB;\nAB3: 'x';\nA: 'a';\nB: 'b';\nAB: 'y';",
    );
    let TypeDef::Enum { ctors, .. } = &tables.schema().types[0] else {
        panic!("expected enum")
    };
    let names: Vec<_> = ctors.iter().map(|ctor| ctor.name.as_str()).collect();
    assert_eq!(names, ["AB3", "AB", "AB4"]);
    for text in ["x", "ab", "y"] {
        assert!(accepts(&tables, text), "{text}");
    }
}

#[test]
fn empty_alternatives_are_preserved_in_either_position() {
    let tables = generate("empty-alternatives", "Root: /(|a)b/ | /(c|)d/;");
    for text in ["b", "ab", "d", "cd"] {
        assert!(accepts(&tables, text), "{text}");
    }
    for text in ["", "a", "c", "bd", "ad"] {
        assert!(!accepts(&tables, text), "{text}");
    }
}

#[test]
fn classes_include_the_maximum_scalar_and_skip_surrogates() {
    let tables = generate(
        "unicode-bounds",
        r"Root: /\x{10FFFF}/ | /[\x{10FFFD}-\x{10FFFF}]/ | /[\x{D7FE}-\x{E001}]/;",
    );
    for text in [
        "\u{10ffff}",
        "\u{10fffe}",
        "\u{10fffd}",
        "\u{d7fe}",
        "\u{d7ff}",
        "\u{e000}",
        "\u{e001}",
    ] {
        assert!(accepts(&tables, text), "{text:?}");
    }
    for text in ["a", "\u{d7fd}", "\u{e002}"] {
        assert!(!accepts(&tables, text), "{text:?}");
    }
}

#[test]
fn malformed_table_input_is_rejected_at_its_source() {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("llkgen-malformed-tables");
    std::fs::create_dir_all(&dir).unwrap();
    let valid = "start 0\nnon_terminals 1 Root\nterminals 1 EndOfInput\nproductions 1 0 0 0\n";
    for (label, source, message) in [
        (
            "start",
            valid.replace("start 0", "start nope"),
            "start: invalid integer",
        ),
        (
            "missing",
            valid.replace("start 0\n", ""),
            "expected one start value",
        ),
        (
            "negative",
            valid.replace("start 0", "start -1"),
            "nonnegative integer",
        ),
        (
            "names",
            valid.replace("non_terminals 1", "non_terminals 2"),
            "name count",
        ),
        (
            "productions",
            valid.replace("productions 1 0 0 0\n", ""),
            "truncated productions",
        ),
        ("lhs", valid.replace("1 0 0 0", "1 1 0 0"), "left side"),
        (
            "symbols",
            valid.replace("1 0 0 0", "1 0 0 1"),
            "truncated production symbols",
        ),
        (
            "nt",
            valid.replace("1 0 0 0", "1 0 0 1 1"),
            "symbol is not a non-terminal",
        ),
        (
            "terminal",
            valid.replace("1 0 0 0", "1 0 0 1 -2"),
            "symbol is not a terminal",
        ),
        (
            "extra",
            valid.replace("1 0 0 0", "1 0 0 0 0"),
            "extra production data",
        ),
    ] {
        let path = dir.join(format!("{label}.tables"));
        std::fs::write(&path, source).unwrap();
        let out = Command::new(generator())
            .args(["--allow-read", "--"])
            .arg(&path)
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(1), "{label}: {out:?}");
        let stderr = String::from_utf8(out.stderr).unwrap();
        assert!(stderr.contains(path.to_str().unwrap()), "{stderr}");
        assert!(stderr.contains(message), "{label}: {stderr}");
        assert!(
            !String::from_utf8(out.stdout)
                .unwrap()
                .contains("lookahead ")
        );
    }
    let math = selfhost_harness::root().join("crates/tauto-syntax/tests/data/math.tables");
    let out = Command::new(generator())
        .args(["--allow-read", "--"])
        .arg(&math)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let expected = std::fs::read_to_string(&math)
        .unwrap()
        .lines()
        .filter(|l| l.starts_with("max_k ") || l.starts_with("lookahead "))
        .map(|l| format!("{l}\n"))
        .collect::<String>();
    assert_eq!(
        String::from_utf8(out.stdout).unwrap(),
        format!("== {}\n{expected}", math.display())
    );
}
