//! The bridge to the generator of random well-typed programs, which is
//! written in Tauto (`totes/fuzz`): a pure function from a sequence of
//! choices to a program. The evaluator runs it, and only the evaluator, so a
//! backend under test never makes its own inputs. A program of a seed comes
//! with the choices it took; replaying them gives the same program, and the
//! tote's shrinker proposes smaller sequences to try when one fails.
//!
//! The rest of this module is what the driver (`tests/fuzz.rs`) keeps of a
//! failure: its signature, whether a case already declares it, the case
//! snippet it writes, and where it saves them.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

pub mod interactions;

/// Compare a normally completed trace against an optional independent oracle.
/// File replays and generated interactions use the same verdict rule.
pub fn matches_expected(shows: &[String], succeeded: bool, expected: Option<&[String]>) -> bool {
    expected.is_none_or(|want| succeeded && shows == want)
}

/// SplitMix64: small, fast, and the same sequence everywhere. The
/// interaction families draw their scalars from it.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }

    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A generated program: its declarations, then its `show` lines. The
/// text of the first `n` lines after the declarations is a program too, so a
/// run that fails can be cut down to the shows before the failure.
#[derive(Clone)]
pub struct Program {
    pub declarations: String,
    pub shows: Vec<String>,
}

impl Program {
    pub fn text(&self, shows: usize) -> String {
        let mut out = self.declarations.clone();
        for line in &self.shows[..shows] {
            out.push_str(line);
        }
        out
    }

    /// A program written by hand: its lines that start with `show(`
    /// are its show lines, and the lines before the first of them its
    /// declarations.
    pub fn from_text(text: &str) -> Self {
        let lines: Vec<&str> = text.split_inclusive('\n').collect();
        let at = lines
            .iter()
            .position(|l| l.starts_with("show("))
            .unwrap_or(lines.len());
        let mut shows: Vec<String> = Vec::new();
        for line in &lines[at..] {
            match shows.last_mut() {
                Some(last) if !line.starts_with("show(") => last.push_str(line),
                _ => shows.push(line.to_string()),
            }
        }
        Program {
            declarations: lines[..at].concat(),
            shows,
        }
    }

    pub fn full(&self) -> String {
        self.text(self.shows.len())
    }
}


/// A program the generator made, with the choices it took.
pub struct Generated {
    pub choices: Vec<u64>,
    pub program: Program,
}

/// The repository's root.
pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Run `call` (a Tauto expression of type `Text` over the fuzz tote's
/// `report.taut`) on the evaluator and read the programs it reports.
fn generate(call: &str) -> Result<Vec<Generated>, String> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let tote = repo_root().join("totes/fuzz/src");
    let tote = tote.canonicalize().map_err(|e| format!("{}: {e}", tote.display()))?;
    let dir = std::env::temp_dir().join(format!(
        "tauto-fuzz-gen-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let path = dir.join("main.taut");
    let text = format!(
        "import \"{}\"\nshow(&{call})\n",
        tote.join("report.taut").display()
    );
    std::fs::write(&path, text).map_err(|e| e.to_string())?;
    let loaded = tauto::program::load(&path);
    let _ = std::fs::remove_dir_all(&dir);
    let loaded = loaded.map_err(|e| format!("the generator does not load: {e}"))?;
    if let Some((error, _)) = loaded.program.errors.first() {
        return Err(format!("the generator does not check: {error}"));
    }
    let got = tauto::exec::run_loaded_with(
        &loaded,
        u64::MAX,
        tauto::exec::RunOptions::default(),
    )
    .map_err(|e| format!("the generator fails: {e}"))?;
    let quoted = got.stdout.trim_end();
    let inner = quoted
        .strip_prefix('"')
        .and_then(|q| q.strip_suffix('"'))
        .ok_or_else(|| format!("the generator shows no text: {quoted}"))?;
    parse_reports(&unescape(inner))
}

/// The programs of the `count` seeds from `first`.
pub fn seeds(first: u64, count: u64) -> Result<Vec<Generated>, String> {
    generate(&format!("fz_seeds_report({first}, {count})"))
}

/// The program a sequence of choices names.
pub fn replay(choices: &[u64]) -> Result<Generated, String> {
    generate(&format!("fz_replay_report({})", list(choices)))?
        .pop()
        .ok_or_else(|| "the generator reports no program".into())
}

/// The programs one shrinking step from `choices`, most promising first.
pub fn shrinks(choices: &[u64]) -> Result<Vec<Generated>, String> {
    generate(&format!("fz_shrink_report({})", list(choices)))
}

fn list(choices: &[u64]) -> String {
    let items: Vec<String> = choices.iter().map(u64::to_string).collect();
    format!("[{}]", items.join(", "))
}

/// Text as `Text::escape_debug` writes it, read back.
pub fn unescape(s: &str) -> String {
    let mut out = String::new();
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some('0') => out.push('\0'),
            Some('u') => {
                let hex: String = chars
                    .by_ref()
                    .skip_while(|&c| c == '{')
                    .take_while(|&c| c != '}')
                    .collect();
                if let Some(c) = u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32) {
                    out.push(c);
                }
            }
            Some(other) => out.push(other),
            None => out.push('\\'),
        }
    }
    out
}

/// The generator's report: `choices …`, `decl …`, `show …` lines, then `end`
/// (`totes/fuzz/src/report.taut`).
pub fn parse_reports(text: &str) -> Result<Vec<Generated>, String> {
    let mut out = Vec::new();
    let mut choices = None;
    let mut declarations = String::new();
    let mut shows = Vec::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("choices") {
            choices = Some(
                rest.split_whitespace()
                    .map(|n| n.parse::<u64>().map_err(|e| format!("choice {n}: {e}")))
                    .collect::<Result<Vec<_>, _>>()?,
            );
        } else if let Some(rest) = line.strip_prefix("decl ") {
            declarations = unescape(rest);
        } else if let Some(rest) = line.strip_prefix("show ") {
            shows.push(unescape(rest));
        } else if line == "end" {
            out.push(Generated {
                choices: choices.take().ok_or("a report without choices")?,
                program: Program {
                    declarations: std::mem::take(&mut declarations),
                    shows: std::mem::take(&mut shows),
                },
            });
        } else if !line.is_empty() {
            return Err(format!("unexpected line in the generator's report: {line}"));
        }
    }
    Ok(out)
}

/// What a backend is seen to do with one program.
#[derive(Debug, Clone, PartialEq)]
pub struct Observation {
    pub shows: Vec<String>,
    /// `None` for a run that ends normally.
    pub error: Option<Failure>,
}

/// How a run did not end normally: the stage that stopped it (`check`,
/// `compile`, `build`, `run`) and its message, normalized as a case
/// runner's status is (`coverage::status`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Failure {
    pub stage: String,
    pub message: String,
}

impl Failure {
    pub fn new(stage: &str, text: &str) -> Self {
        let status = crate::coverage::status(stage, &without_places(&error_kind(text)));
        let message = status
            .strip_prefix(stage)
            .and_then(|m| m.strip_prefix(": "))
            .unwrap_or("")
            .to_string();
        Failure {
            stage: stage.to_string(),
            message,
        }
    }

    /// A run-time error every backend must raise at the same point.
    pub fn is_expected_runtime(&self) -> bool {
        self.stage == "run" && RUNTIME_KINDS.contains(&self.message.as_str())
    }
}

/// A message without what changes from one program to the next: the
/// scratch file it names, and the line, column and byte it points at. Two
/// failures of one cause then read the same.
pub fn without_places(text: &str) -> String {
    let mut out = String::new();
    for line in text.lines() {
        let mut words = Vec::new();
        for word in line.split(' ') {
            // `/tmp/…/main.taut:3:14:` names the scratch file and a place.
            if let Some(at) = word.find(".taut:") {
                let file = word[..at + 5].rsplit('/').next().unwrap_or("");
                words.push(format!("{file}:"));
                continue;
            }
            words.push(word.to_string());
        }
        let mut line = words.join(" ");
        // `(byte 112)`
        while let Some(at) = line.find("(byte ") {
            let end = line[at..].find(')').map_or(line.len(), |e| at + e + 1);
            line.replace_range(at..end, "");
        }
        out.push_str(line.trim_end());
        out.push('\n');
    }
    out
}

/// The run-time errors the programs can raise.
const RUNTIME_KINDS: [&str; 2] = ["the number is too large", "division by zero"];

/// A run-time error by the message every backend gives; any other failure
/// keeps its text.
fn error_kind(message: &str) -> String {
    for kind in RUNTIME_KINDS {
        if message.contains(kind) {
            return kind.into();
        }
    }
    message.trim().to_string()
}

/// What a failure is, so that two failures with the same cause are one: the
/// backends that do not do what the reference does, and for each its stage
/// and normalized message. The reference is the evaluator's observation when
/// it ran, which is only how failures are grouped: no backend is taken to be
/// right.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Signature(pub BTreeMap<String, String>);

impl Signature {
    /// `None` when every backend agrees and none fails in a way a program of
    /// the generator must not.
    pub fn of(seen: &[(String, Observation)]) -> Option<Self> {
        let mut out = BTreeMap::new();
        let reference = seen.iter().find(|(b, _)| b == "eval").or(seen.first())?;
        for (backend, o) in seen {
            let differs = o != &reference.1;
            let bad = o.error.as_ref().is_some_and(|e| !e.is_expected_runtime());
            if differs || bad {
                out.insert(backend.clone(), Self::describe(o));
            }
        }
        // When only the reference is off, every other backend differs from
        // it; name the reference alone.
        if out.len() > 1 && out.len() == seen.len() - 1 && !out.contains_key(&reference.0) {
            let others: Vec<&Observation> = seen
                .iter()
                .filter(|(b, _)| b != &reference.0)
                .map(|(_, o)| o)
                .collect();
            if others.windows(2).all(|w| w[0] == w[1]) {
                out = BTreeMap::from([(reference.0.clone(), Self::describe(&reference.1))]);
            }
        }
        (!out.is_empty()).then_some(Signature(out))
    }

    fn describe(o: &Observation) -> String {
        match &o.error {
            Some(e) if e.message.is_empty() => e.stage.clone(),
            Some(e) => format!("{}: {}", e.stage, e.message),
            None => "output: differs".to_string(),
        }
    }

    /// A short, stable name for the failure's directory.
    pub fn key(&self) -> String {
        // FNV-1a over the signature's text.
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for b in self.text().bytes() {
            h ^= b as u64;
            h = h.wrapping_mul(0x0100_0000_01b3);
        }
        let backends: Vec<&str> = self.0.keys().map(String::as_str).collect();
        format!("{}-{h:016x}", backends.join("+"))
    }

    pub fn text(&self) -> String {
        self.0
            .iter()
            .map(|(b, d)| format!("{b}: {d}"))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

/// What the cases already declare a backend fails at: `<backend>.bug` and
/// `<backend>.unimplemented`, each as `stage: message`.
pub struct Known(Vec<(String, String, String)>);

impl Known {
    pub fn read(cases_dir: &Path) -> Result<Self, String> {
        let mut out = Vec::new();
        for case in crate::rust_cases(cases_dir)? {
            for (backend, what) in &case.opt_outs {
                out.push((backend.clone(), what.clone(), case.name.clone()));
            }
        }
        Ok(Known(out))
    }

    /// The case that already declares this failure, when one does: a case
    /// that declares each failing backend's stage and message (one contains
    /// the other, as a case's declaration is the start of a message). The
    /// evaluator's failures are never declared this way.
    pub fn declaring(&self, sig: &Signature) -> Option<String> {
        let mut found = None;
        for (backend, desc) in &sig.0 {
            let hit = self.0.iter().find(|(b, what, _)| {
                b == backend && !what.trim().is_empty() && (desc.contains(what.as_str()) || what.contains(desc.as_str()))
            })?;
            found = Some(hit.2.clone());
        }
        found
    }
}

/// A case for `cases/`, written from a failure: the program, what the
/// evaluator observed as the expectation, and each other failing backend as a
/// `bug`. The expectation is the evaluator's observation only as a
/// starting point: a person decides which backend is right before the case
/// goes in.
pub fn case_snippet(name: &str, sig: &Signature, text: &str, seen: &[(String, Observation)]) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "// Found by the fuzzer ({}). Check which backend is right before adding it.\n",
        sig.key()
    ));
    for (b, o) in seen {
        out.push_str(&format!("// {b}: {}\n", observed_line(o)));
    }
    out.push_str(&format!("@ cases.{name}\n"));
    for (backend, desc) in &sig.0 {
        if backend != "eval" {
            out.push_str(&format!("{backend}.bug = {}\n", eure_string(desc)));
        }
    }
    out.push_str(&format!("source = ```tauto\n{}```\n", text));
    if let Some((_, eval)) = seen.iter().find(|(b, _)| b == "eval") {
        match &eval.error {
            None => {
                out.push_str(&format!("stdout = ```\n{}\n```\n", eval.shows.join("\n")));
            }
            Some(e) if e.stage == "run" => {
                if !eval.shows.is_empty() {
                    out.push_str(&format!("stdout = ```\n{}\n```\n", eval.shows.join("\n")));
                }
                out.push_str(&format!("run_error = {}\n", eure_string(&e.message)));
            }
            Some(_) => {}
        }
    }
    out
}

fn observed_line(o: &Observation) -> String {
    let shows = o.shows.join(" | ");
    match &o.error {
        None => format!("ok [{shows}]"),
        Some(e) => format!("{}: {} [{shows}]", e.stage, e.message),
    }
}

fn eure_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Where failures are kept between runs: `.fuzz/findings/<signature>/` in
/// the repository, which git ignores.
pub fn findings_dir() -> PathBuf {
    repo_root().join(".fuzz/findings")
}

/// Keep a failure under its signature: the smallest program of a signature
/// stays, a larger one with the same signature is dropped. Returns the
/// directory and whether this one was kept.
pub fn save(sig: &Signature, files: &[(&str, &str)], program_len: usize) -> std::io::Result<(PathBuf, bool)> {
    let dir = findings_dir().join(sig.key());
    let kept = dir.join("program.taut");
    if let Ok(old) = std::fs::read_to_string(&kept)
        && old.len() <= program_len
    {
        return Ok((dir, false));
    }
    std::fs::create_dir_all(&dir)?;
    for (name, text) in files {
        std::fs::write(dir.join(name), text)?;
    }
    Ok((dir, true))
}

#[cfg(test)]
mod oracle_tests {
    use super::matches_expected;

    #[test]
    fn replay_oracle_rejects_shared_wrong_answers() {
        let expected = vec!["result = 3".to_string()];
        let shared_wrong = vec!["result = 4".to_string()];
        for _backend in ["eval", "rust", "javascript"] {
            assert!(!matches_expected(&shared_wrong, true, Some(&expected)));
        }
        assert!(matches_expected(&expected, true, Some(&expected)));
        assert!(!matches_expected(&expected, false, Some(&expected)));
    }

    #[test]
    fn replay_oracle_preserves_event_order_and_multiplicity() {
        let expected = vec!["request = 1".to_string(), "state = 2".to_string()];
        let reversed = expected.iter().rev().cloned().collect::<Vec<_>>();
        assert!(!matches_expected(&reversed, true, Some(&expected)));
        assert!(!matches_expected(&expected[..1], true, Some(&expected)));
        let mut repeated = expected.clone();
        repeated.push(expected[1].clone());
        assert!(!matches_expected(&repeated, true, Some(&expected)));
    }

    #[test]
    fn absent_oracle_leaves_backend_comparison_to_the_runner() {
        assert!(matches_expected(&[], true, None));
        assert!(matches_expected(&[], false, None));
        assert!(matches_expected(&[], true, Some(&[])));
        assert!(!matches_expected(&[], false, Some(&[])));
    }
}

#[cfg(test)]
mod failure_tests {
    use super::*;

    fn ok(shows: &[&str]) -> Observation {
        Observation {
            shows: shows.iter().map(|s| s.to_string()).collect(),
            error: None,
        }
    }

    #[test]
    fn a_message_names_no_scratch_file_or_place() {
        assert_eq!(
            without_places("/tmp/tauto-fuzz-eval-1-2/main.taut:3:14: a thing (byte 112)"),
            "main.taut: a thing\n"
        );
    }

    #[test]
    fn a_signature_names_the_backends_that_are_off() {
        let seen = vec![
            ("eval".to_string(), ok(&["1"])),
            ("rust".to_string(), ok(&["1"])),
            ("javascript".to_string(), ok(&["2"])),
        ];
        let sig = Signature::of(&seen).unwrap();
        assert_eq!(sig.text(), "javascript: output: differs");
        assert!(Signature::of(&seen[..2]).is_none());
    }

    #[test]
    fn when_only_the_reference_is_off_the_signature_names_it() {
        let seen = vec![
            ("eval".to_string(), ok(&["2"])),
            ("rust".to_string(), ok(&["1"])),
            ("javascript".to_string(), ok(&["1"])),
        ];
        assert_eq!(Signature::of(&seen).unwrap().text(), "eval: output: differs");
    }

    #[test]
    fn an_expected_run_time_error_is_no_failure() {
        let err = Observation {
            shows: vec![],
            error: Some(Failure::new("run", "error: division by zero at …")),
        };
        let seen = vec![("eval".to_string(), err.clone()), ("rust".to_string(), err)];
        assert!(Signature::of(&seen).is_none());
    }

    #[test]
    fn a_declared_failure_is_known() {
        let known = Known(vec![(
            "javascript".into(),
            "build: the module does not load".into(),
            "a/b".into(),
        )]);
        let sig = Signature(BTreeMap::from([(
            "javascript".to_string(),
            "build: the module does not load: line 3".to_string(),
        )]));
        assert_eq!(known.declaring(&sig).as_deref(), Some("a/b"));
        let other = Signature(BTreeMap::from([(
            "rust".to_string(),
            "build: the module does not load".to_string(),
        )]));
        assert!(known.declaring(&other).is_none());
    }

    #[test]
    fn the_generators_report_reads_back() {
        let got = parse_reports("choices 1 2\ndecl a\\nb\nshow show(&(1))\\n\nend\n").unwrap();
        assert_eq!(got.len(), 1);
        assert_eq!(got[0].choices, vec![1, 2]);
        assert_eq!(got[0].program.full(), "a\nbshow(&(1))\n");
        assert_eq!(unescape("\\\"\\u{3c9}\\\\"), "\"ω\\");
    }
}
