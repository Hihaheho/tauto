//! `totes/unicode` against `char::is_alphanumeric` and `char::is_whitespace`.

use std::fs;

use selfhost_harness::{
    assert_same_dump, llkgen_unicode_table_files, parol_unicode_table_files, root, run_tote_at,
    security_table_files,
    stale, unicode_table_files,
};

/// Reads code points, one a line, and prints `<code point> <alphanumeric> <whitespace>`.
fn main_source() -> &'static str {
    r#"
import std::builtin::os { argv, print, read_file }
import std::text
import unicode::unicode { UnicodeClasses, unicode_is_alphanumeric, unicode_is_whitespace }
import unicode::classes { unicode_classes }
import text::text { text_lines, text_newline, text_parse_u64 }

fn flag(b: Bool): Text {
  if b { "1" } else { "0" }
}

fn number(t: Text): Nat {
  match text_parse_u64(t) {
    Some(n) => n
    None => 0
  }
}

fn one(classes: UnicodeClasses, line: Text): Unit {
  if Text::len(line) > 0 {
    let c := number(line)
    print(Text::concat_all(Cons(line, Cons(" ", Cons(flag(unicode_is_alphanumeric(classes, c)), Cons(" ", Cons(flag(unicode_is_whitespace(classes, c)), Cons(text_newline(), Nil))))))))
  }
}

fn each(classes: UnicodeClasses, lines: List(Text)): Unit {
  match lines {
    Nil => #()
    Cons(line, rest) => {
      one(classes, line)
      each(classes, rest)
    }
  }
}

match perform argv() {
  Cons(path, rest) => match read_file(path) {
    Ok(t) => each(unicode_classes(), text_lines(t))
    Err(e) => print(e)
  }
  Nil => #()
}
"#
}

#[test]
fn the_tables_are_current() {
    let problems = stale(&unicode_table_files());
    assert!(
        problems.is_empty(),
        "{problems:?}: run scripts/generate-unicode-tables.taut"
    );
}

#[test]
fn the_tables_of_the_scanner_generator_are_current() {
    let problems = stale(&llkgen_unicode_table_files());
    assert!(
        problems.is_empty(),
        "{problems:?}: run scripts/generate-unicode-tables.taut"
    );
}

#[test]
fn classes_match_char() {
    // Every ASCII and Latin-1 character, the two sides of each range's ends,
    // and a spread of the rest.
    let mut points: Vec<u32> = (0..=0x2ff).collect();
    let tables: String = unicode_table_files()
        .into_iter()
        .filter(|(path, _)| path.ends_with(".txt"))
        .map(|(_, text)| format!("{text} "))
        .collect();
    for number in tables
        .split_whitespace()
        .filter_map(|number| number.parse::<u32>().ok())
    {
        points.extend([number.saturating_sub(1), number, number + 1]);
    }
    let mut seed = 7u64;
    for _ in 0..3000 {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        points.push(((seed >> 33) % 0x11_0000) as u32);
    }
    points.extend([0xd7ff, 0xd800, 0xdfff, 0xe000, 0x10ffff]);
    points.sort_unstable();
    points.dedup();

    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-unicode-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("probe/src")).unwrap();
    let script: String = points.iter().map(|p| format!("{p}\n")).collect();
    fs::write(dir.join("points.txt"), script).unwrap();
    fs::write(
        dir.join("probe/Tauto.eure"),
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  unicode {{ path = \"{}\" }}\n  text {{ path = \"{}\" }}\n}}\n",
            root().join("totes/unicode").display(),
            root().join("totes/text").display()
        ),
    )
    .unwrap();
    fs::write(dir.join("probe/src/main.taut"), main_source()).unwrap();
    let out = run_tote_at(
        &dir.join("probe"),
        &[dir.join("points.txt").to_string_lossy().into_owned()],
        2_000_000_000,
    );
    assert_eq!(out.error, None);
    let mut rust = String::new();
    for p in &points {
        let c = char::from_u32(*p);
        let yes = |f: fn(char) -> bool| u8::from(c.is_some_and(f));
        rust.push_str(&format!(
            "{p} {} {}\n",
            yes(char::is_alphanumeric),
            yes(char::is_whitespace)
        ));
    }
    assert_same_dump("unicode", &rust, &out.stdout);
}

#[test]
fn the_identifier_tables_of_the_parser_are_current() {
    let problems = stale(&parol_unicode_table_files());
    assert!(
        problems.is_empty(),
        "{problems:?}: run scripts/generate-unicode-tables.taut"
    );
}

/// `tauto_parol::unicode::nfc` against icu_normalizer's NFC, on every
/// character and on pairs and triples of the characters that take part in
/// compositions or have a combining class.
#[test]
fn nfc_matches_icu() {
    use icu_normalizer::ComposingNormalizerBorrowed;
    let icu = ComposingNormalizerBorrowed::new_nfc();
    let check = |s: &str| {
        let want: Vec<u32> = icu.normalize(s).chars().map(|c| c as u32).collect();
        assert_eq!(tauto_parol::unicode::nfc(s), want, "{s:?}");
        assert_eq!(tauto_parol::unicode::is_nfc(s), icu.is_normalized(s), "{s:?}");
    };
    let all: Vec<char> = (0..=0x10FFFFu32).filter_map(char::from_u32).collect();
    for c in &all {
        check(&c.to_string());
    }
    // The characters of the tables: starters that compose, and marks.
    let mut interesting: Vec<char> = Vec::new();
    for (path, text) in parol_unicode_table_files() {
        if path.ends_with("composition.txt") || path.ends_with("decomposition.txt") {
            interesting.extend(
                text.split_whitespace()
                    .filter_map(|n| n.parse::<u32>().ok())
                    .filter_map(char::from_u32),
            );
        }
    }
    interesting.extend(['\u{1100}', '\u{1161}', '\u{11a8}', '\u{ac00}', '\u{ac01}', 'a', 'e']);
    interesting.sort_unstable();
    interesting.dedup();
    let mut seed = 11u64;
    let mut pick = || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        interesting[((seed >> 33) as usize) % interesting.len()]
    };
    for _ in 0..200_000 {
        let n = 2 + (pick() as usize % 3);
        let s: String = (0..n).map(|_| pick()).collect();
        check(&s);
    }
}

#[test]
fn the_tables_of_uts39_are_current() {
    let problems = stale(&security_table_files());
    assert!(
        problems.is_empty(),
        "{problems:?}: run scripts/generate-unicode-tables.taut"
    );
}
