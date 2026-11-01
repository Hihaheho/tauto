//! Source-reading comparison of elaborated declarations with the core.
#[path = "../../tauto-kernel/tests/support/differential.rs"]
mod generator;
use generator::*;
use tauto::check::Verdict;

/// Functions by well-founded and structural recursion (`wf.rs` and
/// `matching.rs` in `crates/tauto-kernel/src/check/`): the named checker elaborates them to
/// terms of the kernel, and the core must accept every term it accepts. Only
/// that direction is tested here; the declarations as written are not terms of
/// the kernel.
#[test]
fn the_core_accepts_what_the_named_checker_elaborates() {
    tauto_messages::install();
    with_stack(core_accepts_what_the_named_checker_elaborates);
}

fn core_accepts_what_the_named_checker_elaborates() {
    let cases: usize = std::env::var("KERNELS_DIFF_DECLS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(300);
    let seed: u64 = std::env::var("KERNELS_DIFF_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0x9E37_79B9_7F4A_7C15);
    let mut g = Gen {
        rng: Rng(seed),
        fresh: 0,
        recs: 0,
    };
    let library = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../std/WellFounded.taut")
        .canonicalize()
        .unwrap();
    let prefix = generator::prefix();
    let mut source = format!(
r#"import "{}"

{}
{}
"#,
library.display().to_string(),
prefix,
r#"fn id_nat(n: Nat): Nat { n }
"#
);
    let mut decls = Vec::new();
    for i in 0..cases {
        let decl = g.recursive(&format!("g{i}"));
        source.push_str(&decl);
        source.push('\n');
        decls.push(decl);
    }
    let dir = std::env::temp_dir().join(format!("tauto-kernels-diff-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("main.taut");
    std::fs::write(&file, &source).unwrap();
    let entries = tauto::check::check_file(&file).unwrap();
    let mut accepted = 0;
    let mut report = String::new();
    for e in entries.iter().filter(|e| e.file.ends_with("main.taut")) {
        match &e.entry.verdict {
            Verdict::Checked { .. } => accepted += 1,
            Verdict::Failed(d) if d.message.to_string().starts_with("the core kernel rejects") => {
                let base = e.entry.name.split('@').next().unwrap_or("");
                let base = base.strip_suffix("::eq").unwrap_or(base);
                let decl = decls
                    .iter()
                    .find(|d| d.starts_with(&format!("fn {base}(")))
                    .map_or("", |d| d.as_str());
                report.push_str(&format!("{}: {}\n{decl}\n", e.entry.name, d.message));
            }
            _ => {}
        }
    }
    eprintln!("elaborated: {accepted} accepted by both");
    assert!(
        report.is_empty(),
        "the core rejects what the named checker accepts:\n{report}"
    );
    assert!(accepted > cases / 4, "{accepted} accepted");
}
