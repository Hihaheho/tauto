//! `totes/unicode` against `char::is_alphanumeric` and `char::is_whitespace`.

use std::fs;

use selfhost_harness::{
    assert_same_dump, llkgen_unicode_table_files, root, run_tote_at, stale, unicode_table_files,
};

/// Reads code points, one a line, and prints `<code point> <alphanumeric> <whitespace>`.
fn main_source() -> &'static str {
    r#"
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
        "{problems:?}: run scripts/generate-unicode-tables.sh"
    );
}

#[test]
fn the_tables_of_the_scanner_generator_are_current() {
    let problems = stale(&llkgen_unicode_table_files());
    assert!(
        problems.is_empty(),
        "{problems:?}: run scripts/generate-unicode-tables.sh"
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
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  unicode {{ path = \"{}\" }}\n}}\n",
            root().join("totes/unicode").display()
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
