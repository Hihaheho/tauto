//! `totes/text` against the Rust standard library's operations on `str`
//! (`docs/design/self-host.md`).

use std::fs;

use selfhost_harness::{assert_same_dump, materialize, root, run_tote_at};

/// What the test tote does to each input: one block of lines.
fn main_source() -> &'static str {
    r#"
fn bool_text(b: Bool): Text {
  if b { "true" } else { "false" }
}

fn opt_u64(o: Option(u64)): Text {
  match o {
    Some(v) => Text::of_u64(v)
    None => "-"
  }
}

fn opt_i64(o: Option(i64)): Text {
  match o {
    Some(v) => Text::of_i64(v)
    None => "-"
  }
}

fn line(name: Text, value: Text): Unit {
  print(Text::concat_all(Cons(name, Cons(" ", Cons(value, Cons(text_newline(), Nil))))))
}

fn joined(parts: List(Text)): Text {
  Text::join(parts, text_code_point(1))
}

fn decode_all(t: Text, i: u64, n: u64): Unit {
  if i < n {
    match text_decode(t, i) {
      Some(#(@code code, @len len)) => line("decode", Text::concat_all(Cons(Text::of_u64(i), Cons(" ", Cons(Text::of_u64(code), Cons(" ", Cons(Text::of_u64(len), Nil)))))))
      None => line("decode", Text::concat_all(Cons(Text::of_u64(i), Cons(" -", Nil))))
    }
    decode_all(t, i + 1, n)
  }
}

fn one(t: Text): Unit {
  line("len", Text::of_u64(Text::len(t)))
  line("chars", Text::of_u64(text_char_count(t)))
  line("lines", joined(text_lines(t)))
  line("split-comma", joined(text_split(t, ",")))
  line("split-ab", joined(text_split(t, "ab")))
  line("find-a", opt_u64(Text::find(t, "a", 0)))
  line("find-a-from-1", opt_u64(Text::find(t, "a", 1)))
  line("find-japanese", opt_u64(Text::find(t, "い", 0)))
  line("find-newline-from-1", opt_u64(Text::find(t, text_newline(), 1)))
  line("starts-a", bool_text(Text::starts_with(t, "a", 0)))
  line("starts-a-at-1", bool_text(Text::starts_with(t, "a", 1)))
  line("parse-i64", opt_i64(text_parse_i64(t)))
  line("parse-u64", opt_u64(text_parse_u64(t)))
  line("repeat", Text::repeat(t, 3))
  decode_all(t, 0, Text::len(t))
}

fn each_path(paths: List(Text)): Unit {
  match paths {
    Nil => #()
    Cons(path, rest) => {
      match read_file(path) {
        Ok(t) => {
          line("==", path)
          one(t)
        }
        Err(e) => line("==", e)
      }
      each_path(rest)
    }
  }
}

each_path(perform argv())
"#
}

fn inputs() -> Vec<String> {
    let mut out: Vec<String> = [
        "",
        "a",
        "abc",
        "a,b,,c",
        ",",
        ",,",
        "aあいう",
        "あいうab",
        "a😀b",
        "😀",
        "ababab",
        "line1\r\nline2\n",
        "\n",
        "\n\n",
        "a\nb",
        "0",
        "-0",
        "+1",
        "-1",
        "+",
        "-",
        "1_000",
        " 1",
        "1 ",
        "12x",
        "00012",
        "9223372036854775807",
        "9223372036854775808",
        "-9223372036854775808",
        "-9223372036854775809",
        "+9223372036854775807",
        "99999999999999999999",
        "-99999999999999999999",
        "٣",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    // A long text, so the loops over its bytes run past their first steps.
    out.push("ab".repeat(40));
    out
}

/// The first position of `needle` from byte `from` that is a character's.
fn find_from(t: &str, needle: &str, from: usize) -> Option<usize> {
    (from..=t.len()).find(|&p| t.is_char_boundary(p) && t[p..].starts_with(needle))
}

fn expected(t: &str) -> String {
    use std::fmt::Write;
    let joined = |parts: Vec<&str>| parts.join("\u{1}");
    let opt = |o: Option<usize>| o.map_or("-".to_string(), |v| v.to_string());
    let mut out = String::new();
    let mut line = |name: &str, value: String| writeln!(out, "{name} {value}").unwrap();
    line("len", t.len().to_string());
    line("chars", t.chars().count().to_string());
    line("lines", joined(t.split('\n').collect()));
    line("split-comma", joined(t.split(",").collect()));
    line("split-ab", joined(t.split("ab").collect()));
    line("find-a", opt(t.find("a")));
    line("find-a-from-1", opt(find_from(t, "a", 1)));
    line("find-japanese", opt(t.find("い")));
    line("find-newline-from-1", opt(find_from(t, "\n", 1)));
    line("starts-a", t.starts_with("a").to_string());
    line(
        "starts-a-at-1",
        (t.is_char_boundary(1.min(t.len())) && t.get(1..).is_some_and(|r| r.starts_with("a")))
            .to_string(),
    );
    line(
        "parse-i64",
        t.parse::<i64>().map_or("-".to_string(), |v| v.to_string()),
    );
    // The evaluator keeps a `u64` in an `i64`.
    line(
        "parse-u64",
        t.parse::<u64>()
            .ok()
            .filter(|v| *v <= i64::MAX as u64)
            .map_or("-".to_string(), |v| v.to_string()),
    );
    line("repeat", t.repeat(3));
    for i in 0..t.len() {
        if t.is_char_boundary(i) {
            let c = t[i..].chars().next().unwrap();
            line("decode", format!("{i} {} {}", c as u32, c.len_utf8()));
        } else {
            line("decode", format!("{i} -"));
        }
    }
    out
}

#[test]
fn text_matches_str() {
    let inputs = inputs();
    let named: Vec<(String, String)> = inputs.iter().map(|s| (s.clone(), s.clone())).collect();
    let m = materialize("text", &named);
    // A tote that depends on `text`.
    let dir = m.dir.join("probe");
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::write(
        dir.join("Tauto.eure"),
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  text {{ path = \"{}\" }}\n}}\n",
            root().join("totes/text").display()
        ),
    )
    .unwrap();
    fs::write(dir.join("src/main.taut"), main_source()).unwrap();
    let out = run_tote_at(&dir, &m.paths, 1_000_000_000);
    assert_eq!(out.error, None);
    let mut rust = String::new();
    for (path, input) in m.paths.iter().zip(&inputs) {
        rust.push_str(&format!("== {path}\n"));
        rust.push_str(&expected(input));
    }
    assert_same_dump("text", &rust, &out.stdout);
}
