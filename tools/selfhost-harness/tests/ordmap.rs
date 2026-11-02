//! `totes/ordmap` against `BTreeMap` (`docs/design/self-host.md`).

use std::collections::BTreeMap;
use std::fmt::Write;
use std::fs;

use selfhost_harness::{assert_same_dump, root, run_tote_at};

/// Reads the script (one operation a line: `i KEY VALUE`, `d KEY`, `f KEY`,
/// `g KEY`) and prints, after each, the answer, the entries, the size and the
/// height.
fn main_source() -> &'static str {
    r#"
fn cmp_i64(a: i64, b: i64): Ordering {
  if a < b { Less } else if a > b { Greater } else { Equal }
}

fn number(t: Text): i64 {
  match text_parse_i64(t) {
    Some(n) => n
    None => 0
  }
}

fn entries_text(es: List(Pair(i64, i64))): Text {
  Text::join(entry_texts(es), ",")
}

fn entry_texts(es: List(Pair(i64, i64))): List(Text) {
  match es {
    Nil => Nil
    Cons(e, rest) => Cons(Text::concat_all(Cons(Text::of_i64(e.fst), Cons(":", Cons(Text::of_i64(e.snd), Nil)))), entry_texts(rest))
  }
}

fn opt(o: Option(i64)): Text {
  match o {
    Some(v) => Text::of_i64(v)
    None => "-"
  }
}

fn report(answer: Text, m: Ordmap(i64, i64)): Unit {
  print(Text::concat_all(Cons(answer, Cons(" ", Cons(entries_text(Ordmap::entries(m)), Cons(" ", Cons(Text::of_u64(Ordmap::size(m)), Cons(" ", Cons(Text::of_u64(Ordmap::height(m)), Cons(text_newline(), Nil))))))))))
}

fn step(m: Ordmap(i64, i64), line: Text): Ordmap(i64, i64) {
  match text_split(line, " ") {
    Nil => m
    Cons(op, args) => match args {
      Nil => m
      Cons(key, rest) => step_with(m, op, number(key), rest)
    }
  }
}

fn step_with(m: Ordmap(i64, i64), op: Text, k: i64, rest: List(Text)): Ordmap(i64, i64) {
  if op == "i" {
    match rest {
      Nil => m
      Cons(value, more) => {
        let next := Ordmap::insert(m, k, number(value), cmp_i64)
        report("i", next)
        next
      }
    }
  } else if op == "d" {
    let next := Ordmap::remove(m, k, cmp_i64)
    report("d", next)
    next
  } else if op == "f" {
    report(floor_text(Ordmap::floor(m, k, cmp_i64)), m)
    m
  } else {
    report(opt(Ordmap::get(m, k, cmp_i64)), m)
    m
  }
}

fn floor_text(o: Option(Pair(i64, i64))): Text {
  match o {
    Some(p) => Text::concat_all(Cons(Text::of_i64(p.fst), Cons("=", Cons(Text::of_i64(p.snd), Nil))))
    None => "-"
  }
}

fn run(m: Ordmap(i64, i64), lines: List(Text)): Unit {
  match lines {
    Nil => #()
    Cons(line, rest) => run(step(m, line), rest)
  }
}

match perform argv() {
  Cons(path, rest) => match read_file(path) {
    Ok(script) => run(Ordmap::empty(), text_lines(script))
    Err(e) => print(e)
  }
  Nil => #()
}
"#
}

/// A linear congruential generator, so that no crate is needed.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self, below: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % below
    }
}

#[test]
fn ordmap_matches_btreemap() {
    let mut rng = Lcg(42);
    let mut script = String::new();
    let mut expected = String::new();
    let mut model: BTreeMap<i64, i64> = BTreeMap::new();
    for step in 0..1000 {
        let key = rng.next(60) as i64 - 10;
        let answer = match rng.next(10) {
            0..=4 => {
                writeln!(script, "i {key} {step}").unwrap();
                model.insert(key, step);
                "i".to_string()
            }
            5..=7 => {
                writeln!(script, "d {key}").unwrap();
                model.remove(&key);
                "d".to_string()
            }
            8 => {
                writeln!(script, "f {key}").unwrap();
                model
                    .range(..=key)
                    .next_back()
                    .map_or("-".to_string(), |(k, v)| format!("{k}={v}"))
            }
            _ => {
                writeln!(script, "g {key}").unwrap();
                model.get(&key).map_or("-".to_string(), |v| v.to_string())
            }
        };
        let entries: Vec<String> = model.iter().map(|(k, v)| format!("{k}:{v}")).collect();
        // The height is the tote's; the bound on it is checked below.
        writeln!(expected, "{answer} {} {}", entries.join(","), model.len()).unwrap();
    }
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("selfhost-harness-ordmap-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("probe/src")).unwrap();
    fs::write(dir.join("script.txt"), &script).unwrap();
    fs::write(
        dir.join("probe/Tauto.eure"),
        format!(
            "package {{\n  name = \"probe\"\n  version = \"0.1.0\"\n}}\n\ndependencies {{\n  ordmap {{ path = \"{}\" }}\n}}\n",
            root().join("totes/ordmap").display()
        ),
    )
    .unwrap();
    fs::write(dir.join("probe/src/main.taut"), main_source()).unwrap();
    let out = run_tote_at(
        &dir.join("probe"),
        &[dir.join("script.txt").to_string_lossy().into_owned()],
        1_000_000_000,
    );
    assert_eq!(out.error, None, "{}", out.stdout);
    // Take the heights out of the output, checking each against the bound.
    let mut seen = String::new();
    for line in out.stdout.lines() {
        let (rest, height) = line.rsplit_once(' ').unwrap();
        let size: f64 = rest.rsplit_once(' ').unwrap().1.parse().unwrap();
        let height: f64 = height.parse().unwrap();
        assert!(
            height <= 1.45 * (size + 2.0).log2(),
            "height {height} of {size} entries in {line}"
        );
        seen.push_str(rest);
        seen.push('\n');
    }
    assert_eq!(out.stdout.lines().count(), 1000);
    assert_same_dump("ordmap", &expected, &seen);
}
