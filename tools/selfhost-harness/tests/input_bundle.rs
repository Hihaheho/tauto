//! Complete original compiler inputs are distinct from compiler acceptance.
use selfhost_harness::{root, run_tote_native, source_bundle::BundlePlan};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::PathBuf,
};

const CASES: &str = "selfhost-input-bundle.eure";

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"))
            .canonicalize()
            .unwrap()
            .join(format!(
                "tauto-inputs-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, id: &str, bytes: impl AsRef<[u8]>) {
        let path = self.0.join(id);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }
    fn run(&self, wire: &str, audit: bool) -> selfhost_harness::RunOutput {
        self.write("input.bundle", wire);
        let mut args = vec![
            if audit {
                "--contract-inputs".into()
            } else {
                "--contract-bundle".into()
            },
            self.0.join("input.bundle").to_string_lossy().into_owned(),
        ];
        if !audit {
            args.push("answer".into());
        }
        run_tote_native("rustgen", &args, 200_000_000_000)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn plan(case: &str, entry: &str, ids: &[&str]) -> BundlePlan {
    BundlePlan {
        roots: vec![entry.into()],
        files: ids
            .iter()
            .map(|id| ((*id).into(), case_inputs::file(CASES, case, id)))
            .collect(),
    }
}
fn status(output: &selfhost_harness::RunOutput, stage: &str, success: bool) {
    assert_eq!(output.error, None, "{output:?}");
    assert_eq!(output.exit, Some(if success { 0 } else { 1 }), "{output:?}");
    let header = format!("TAUTO-RUSTGEN-CONTRACT/2 {stage}\n");
    assert!(output.stderr.starts_with(&header), "{output:?}");
    if success {
        assert_eq!(output.stderr, header);
    } else {
        assert!(
            output.stdout.is_empty(),
            "partial target/audit output: {output:?}"
        );
        let diagnostic = output.stderr.strip_prefix(&header).unwrap();
        assert!(diagnostic.starts_with("rustgen: ") && diagnostic.ends_with('\n'));
        assert_eq!(diagnostic.lines().count(), 1);
    }
}

#[test]
fn v2_encoding_preserves_exact_bytes_and_explicit_root_order() {
    let p = BundlePlan {
        roots: vec!["日本語.taut".into(), "a.taut".into(), "日本語.taut".into()],
        files: BTreeMap::from([
            ("a.taut".into(), "a\r\n\0".into()),
            ("日本語.taut".into(), "元の入力\n".into()),
            ("table.txt".into(), "\n".into()),
        ]),
    };
    let encoded = p.encode().unwrap();
    assert!(
        encoded.starts_with("TAUTO-SOURCES-2\n3\n14\n日本語.taut\n6\na.taut\n14\n日本語.taut\n3\n")
    );
    // The payload is four bytes, never newline-normalized.
    assert!(encoded.contains("6\n4\na.tauta\r\n\0\n"));
    assert!(encoded.contains("table.txt\n\n"));
    assert_eq!(encoded, p.encode().unwrap());
    for id in [
        "",
        "../escape",
        "/absolute",
        "x//y",
        "x/./y",
        "x\\y",
        "x\ny",
        "x\0y",
    ] {
        let invalid = BundlePlan {
            roots: vec![id.into()],
            files: BTreeMap::from([(id.into(), "".into())]),
        };
        assert!(invalid.encode().is_err(), "{id:?}");
    }
    assert!(
        BundlePlan {
            roots: vec!["missing".into()],
            files: BTreeMap::new()
        }
        .encode()
        .is_err()
    );
    let too_big = BundlePlan {
        roots: vec!["a".into()],
        files: BTreeMap::from([("a".into(), "x".repeat(16 * 1024 * 1024))]),
    };
    assert!(too_big.encode().is_err());
}

#[test]
fn only_explicit_allowed_files_are_read() {
    let s = Scratch::new();
    s.write("src/main.taut", case_inputs::fixture(CASES, "plain_answer"));
    s.write("unlisted-secret.txt", "not a build input");
    s.write("cache/secret.taut", "not a build input");
    let ids = vec!["src/main.taut".into()];
    let p = BundlePlan::from_allowed_files(&s.0, &ids, ids.clone()).unwrap();
    assert_eq!(p.files.len(), 1);
    assert!(!p.encode().unwrap().contains("not a build input"));
    assert!(
        BundlePlan::from_allowed_files(
            &s.0,
            &["src/main.taut".into(), "src/main.taut".into()],
            ids.clone()
        )
        .is_err()
    );
    assert!(BundlePlan::from_allowed_files(&s.0, &["missing".into()], ids.clone()).is_err());
    s.write("invalid.txt", [0xff, 0xfe]);
    assert!(BundlePlan::from_allowed_files(&s.0, &["invalid.txt".into()], ids.clone()).is_err());
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(s.0.join("src"), s.0.join("link")).unwrap();
        assert!(BundlePlan::from_allowed_files(&s.0, &["link/main.taut".into()], ids).is_err());
    }
}

#[test]
fn captured_manifest_metadata_selects_all_roots_without_dependency_main() {
    let files = BTreeMap::from([
        (
            "app/Tauto.eure".into(),
            "package { name=\"app\" } dependencies { dep { path=\"../dep\" } }".into(),
        ),
        ("dep/Tauto.eure".into(), "package { name=\"dep\" }".into()),
        ("dep/src/library.tauto".into(), "".into()),
        (
            "dep/src/main.taut".into(),
            case_inputs::fixture(CASES, "dependency_main"),
        ),
        ("app/src/a.tauto".into(), "".into()),
        ("app/src/z.taut".into(), "".into()),
        (
            "app/src/main.taut".into(),
            case_inputs::fixture(CASES, "plain_answer"),
        ),
    ]);
    let p = BundlePlan::from_tote_files("app", files.clone()).unwrap();
    // Same metadata order as manifest_sources and ToteOrder: sorted source files,
    // then entry main, with dependencies before the package.
    assert_eq!(
        p.roots,
        [
            "dep/src/library.tauto",
            "app/src/a.tauto",
            "app/src/z.taut",
            "app/src/main.taut"
        ]
    );
    assert_eq!(p.files, files);
    assert!(p.files.contains_key("dep/src/main.taut"));
    let mut missing = p.files.clone();
    missing.remove("dep/Tauto.eure");
    assert!(BundlePlan::from_tote_files("app", missing).is_err());
    let mut unsafe_path = p.files.clone();
    unsafe_path.insert(
        "app/Tauto.eure".into(),
        "package { name=\"app\" additional-sources=[\"../../outside\"] }".into(),
    );
    assert!(BundlePlan::from_tote_files("app", unsafe_path).is_err());
    let mut host = p.files;
    host.insert(
        "app/Tauto.eure".into(),
        "package { name=\"app\" } rust { executor=\"tokio\" }".into(),
    );
    assert!(BundlePlan::from_tote_files("app", host).is_err());
}

#[test]
fn explicit_input_command_never_overwrites_an_existing_output() {
    let s = Scratch::new();
    s.write("app/Tauto.eure", "package { name=\"app\" }");
    s.write(
        "app/src/main.taut",
        case_inputs::fixture(CASES, "plain_answer"),
    );
    s.write("allowed.txt", "app/Tauto.eure\napp/src/main.taut\n");
    let run = || {
        std::process::Command::new(env!("CARGO_BIN_EXE_source-bundle"))
            .arg("--tote-inputs")
            .arg(&s.0)
            .arg("app")
            .arg(s.0.join("allowed.txt"))
            .arg(s.0.join("output.bundle"))
            .output()
            .unwrap()
    };
    let first = run();
    assert!(first.status.success(), "{first:?}");
    let original = fs::read(s.0.join("output.bundle")).unwrap();
    assert!(original.starts_with(b"TAUTO-SOURCES-2\n"));
    assert!(!run().status.success());
    assert_eq!(fs::read(s.0.join("output.bundle")).unwrap(), original);
    #[cfg(unix)]
    {
        fs::remove_file(s.0.join("output.bundle")).unwrap();
        s.write("not-output", "unchanged");
        std::os::unix::fs::symlink(s.0.join("not-output"), s.0.join("output.bundle")).unwrap();
        assert!(!run().status.success());
        assert_eq!(fs::read(s.0.join("not-output")).unwrap(), b"unchanged");
    }
}

#[test]
fn tauto_visits_ordered_roots_and_shared_dependencies_once() {
    let s = Scratch::new();
    let mut p = plan(
        "virtual_imports_compile_original_files",
        "src/main.taut",
        &["src/main.taut", "lib/value.taut"],
    );
    p.roots = vec![
        "lib/value.taut".into(),
        "src/main.taut".into(),
        "lib/value.taut".into(),
    ];
    let output = s.run(&p.encode().unwrap(), true);
    status(&output, "input-complete", true);
    let ids: Vec<_> = output
        .stdout
        .lines()
        .map(|line| line.split('\t').nth(1).unwrap())
        .collect();
    assert_eq!(ids, ["lib/value.taut", "src/main.taut"]);
}

#[test]
fn tauto_audits_resources_without_erasing_macros_or_unused_proofs() {
    let s = Scratch::new();
    let resource = plan(
        "resource_availability_does_not_expand_macro",
        "src/main.taut",
        &["Tauto.eure", "src/main.taut", "data/日本語.txt"],
    );
    let audit = s.run(&resource.encode().unwrap(), true);
    status(&audit, "input-complete", true);
    let fields: Vec<_> = audit
        .stdout
        .lines()
        .find(|l| l.starts_with("R\t"))
        .unwrap()
        .split('\t')
        .collect();
    assert_eq!(&fields[..3], &["R", "data/日本語.txt", "src/main.taut"]);
    let start: usize = fields[3].parse().unwrap();
    let end: usize = fields[4].parse().unwrap();
    assert_eq!(
        &resource.files["src/main.taut"][start..end],
        "include_text!(\"../data/日本語.txt\")"
    );
    assert_eq!(
        fields[5].parse::<usize>().unwrap(),
        resource.files["data/日本語.txt"].len()
    );
    let compile = s.run(&resource.encode().unwrap(), false);
    status(&compile, "generated", true);
    assert!(!compile.stdout.contains("include_text!"));
    let proof = plan(
        "unused_imported_proof_is_not_erased",
        "main.taut",
        &["main.taut", "proof.taut"],
    );
    status(
        &s.run(&proof.encode().unwrap(), true),
        "input-complete",
        true,
    );
    let rejected = s.run(&proof.encode().unwrap(), false);
    status(&rejected, "source-rejected", false);
    assert!(
        rejected
            .stderr
            .contains("unsupported declaration: StTheorem")
    );
    let missing = plan(
        "missing_resource_retains_macro_contract",
        "src/main.taut",
        &["Tauto.eure", "src/main.taut"],
    );
    // Inventory resolution is not the shared macro_error observation. The
    // strict shared runner leaves that semantic requirement incomplete.
    status(
        &s.run(&missing.encode().unwrap(), true),
        "resource-rejected",
        false,
    );
    for (case, entry, ids) in [
        (
            "resource_cannot_leave_tote_even_when_supplied",
            "app/src/main.taut",
            vec!["app/Tauto.eure", "app/src/main.taut", "other/data.txt"],
        ),
        (
            "resource_cannot_leave_and_reenter_tote",
            "app/src/main.taut",
            vec!["app/Tauto.eure", "app/src/main.taut", "app/data.txt"],
        ),
        (
            "resource_without_tote_stays_in_source_directory",
            "src/main.taut",
            vec!["src/main.taut", "data.txt"],
        ),
    ] {
        let rejected = s.run(&plan(case, entry, &ids).encode().unwrap(), true);
        status(&rejected, "resource-rejected", false);
        assert!(rejected.stderr.contains("include.outside"));
    }
    let cycle = plan(
        "import_cycle_is_a_loader_diagnostic",
        "a.taut",
        &["a.taut", "b.taut"],
    );
    status(
        &s.run(&cycle.encode().unwrap(), true),
        "load-rejected",
        false,
    );
    let dynamic = BundlePlan {
        roots: vec!["main.taut".into()],
        files: BTreeMap::from([(
            "main.taut".into(),
            case_inputs::fixture(CASES, "dynamic_resource"),
        )]),
    };
    status(
        &s.run(&dynamic.encode().unwrap(), true),
        "input-unsupported",
        false,
    );
}

#[test]
fn malformed_v2_inputs_never_become_language_rejections() {
    let s = Scratch::new();
    let oversized_header = format!("TAUTO-SOURCES-2\n{}\n", "1".repeat(1024 * 1024));
    status(&s.run(&oversized_header, true), "input-error", false);
    for wire in [
        "TAUTO-SOURCES-2\n+1\n1\na\n1\n1\n0\na\n",
        "TAUTO-SOURCES-2\n0\n0\n",
        "TAUTO-SOURCES-2\n4097\n",
        "TAUTO-SOURCES-2\n1\n999999999999999999999999999\n",
        "TAUTO-SOURCES-2\n1\n1\nあ\n0\n",
        "TAUTO-SOURCES-2\n1\n1\na\n0\n",
        "TAUTO-SOURCES-2\n1\n1\na\n2\n1\n0\na\n1\n0\na\n",
        "TAUTO-SOURCES-2\n1\n1\na\n1\n1\n16777216\na",
        "TAUTO-SOURCES-2\n1\n1\na\n1\n1\n0\na\nextra",
        "TAUTO-SOURCES-2\n1\n4\n../a\n0\n",
    ] {
        status(&s.run(wire, true), "input-error", false);
    }
}

#[test]
fn v2_path_limits_are_explicit_infrastructure_bounds() {
    let s = Scratch::new();
    let source = case_inputs::fixture(CASES, "plain_answer");
    let wire = |id: &str| {
        format!(
            "TAUTO-SOURCES-2\n1\n{}\n{id}\n1\n{}\n{}\n{id}{source}\n",
            id.len(),
            id.len(),
            source.len()
        )
    };
    for id in [
        "x".repeat(4096),
        format!("{}x", "あ".repeat(1365)),
        vec!["a"; 256].join("/"),
    ] {
        let p = BundlePlan {
            roots: vec![id.clone()],
            files: BTreeMap::from([(id.clone(), source.clone())]),
        };
        assert_eq!(p.encode().unwrap(), wire(&id));
        status(&s.run(&wire(&id), true), "input-complete", true);
    }
    for id in [
        "x".repeat(4097),
        format!("{}xx", "あ".repeat(1365)),
        vec!["a"; 257].join("/"),
    ] {
        let p = BundlePlan {
            roots: vec![id.clone()],
            files: BTreeMap::from([(id.clone(), source.clone())]),
        };
        assert!(p.encode().is_err());
        status(&s.run(&wire(&id), true), "input-error", false);
        // Also check a non-root file ID: roots cannot mask a file-record defect.
        let other = format!(
            "TAUTO-SOURCES-2\n1\n1\na\n2\n1\n{}\na{source}\n{}\n0\n{id}\n",
            source.len(),
            id.len()
        );
        status(&s.run(&other, true), "input-error", false);
    }
    for fixture in ["oversized_import_path", "oversized_resource_path"] {
        let p = BundlePlan {
            roots: vec!["main.taut".into()],
            files: BTreeMap::from([("main.taut".into(), case_inputs::fixture(CASES, fixture))]),
        };
        status(
            &s.run(&p.encode().unwrap(), true),
            "input-unsupported",
            false,
        );
    }
    for (fixture, id) in [
        ("resolved_import_depth_limit", vec!["a"; 256].join("/")),
        ("resolved_resource_depth_limit", vec!["a"; 256].join("/")),
        (
            "resolved_import_byte_limit",
            format!("{}/a", "x".repeat(4090)),
        ),
        (
            "resolved_resource_byte_limit",
            format!("{}/a", "x".repeat(4090)),
        ),
    ] {
        let p = BundlePlan {
            roots: vec![id.clone()],
            files: BTreeMap::from([(id, case_inputs::fixture(CASES, fixture))]),
        };
        let rejected = s.run(&p.encode().unwrap(), true);
        status(&rejected, "input-unsupported", false);
        assert!(rejected.stderr.contains("resolved"));
    }
}

#[test]
fn complete_compiler_inputs_match_independent_original_byte_oracle() {
    let s = Scratch::new();
    let root = root().canonicalize().unwrap();
    let allowed: Vec<String> = include_str!("data/rustgen-inputs.txt")
        .lines()
        .filter(|s| !s.is_empty() && !s.starts_with('#'))
        .map(String::from)
        .collect();
    let p = BundlePlan::from_tote(&root, "totes/rustgen", &allowed).unwrap();
    // Oracle only: never use its parsed/extracted output or discovered inputs to
    // construct the bundle consumed by the Tauto implementation.
    let oracle = tauto::program::tote_inputs(&root.join("totes/rustgen")).unwrap();
    let ids: Vec<String> = oracle
        .iter()
        .map(|f| {
            f.canonicalize()
                .unwrap()
                .strip_prefix(&root)
                .unwrap()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    for (path, id) in oracle.iter().zip(&ids) {
        let canonical = path.canonicalize().unwrap();
        assert_eq!(
            p.files
                .get(id)
                .unwrap_or_else(|| panic!("unlisted actual compiler input: {id}")),
            &fs::read_to_string(path).unwrap(),
            "original bytes: {id}"
        );
        if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("taut" | "tauto")
        ) {
            // Ancestor manifests also affect include confinement even if they
            // do not select this source as one of the entry tote's roots.
            if let Some(manifest) = canonical
                .parent()
                .unwrap()
                .ancestors()
                .take_while(|dir| dir.starts_with(&root))
                .map(|dir| dir.join("Tauto.eure"))
                .find(|file| file.is_file())
            {
                let manifest_id = manifest.strip_prefix(&root).unwrap().to_str().unwrap();
                assert_eq!(
                    p.files.get(manifest_id),
                    Some(&fs::read_to_string(&manifest).unwrap()),
                    "include boundary manifest: {id}"
                );
            }
        }
    }
    let audit = s.run(&p.encode().unwrap(), true);
    status(&audit, "input-complete", true);
    let mut sources = Vec::new();
    let mut resources = BTreeSet::new();
    let mut base = 0;
    for line in audit.stdout.lines() {
        let f: Vec<_> = line.split('\t').collect();
        match f[0] {
            "S" => {
                assert_eq!(f.len(), 4);
                assert_eq!(f[2].parse::<usize>().unwrap(), base);
                let end = base + p.files[f[1]].len();
                assert_eq!(f[3].parse::<usize>().unwrap(), end);
                base = end + 1;
                sources.push(f[1].to_string());
            }
            "R" => {
                assert_eq!(f.len(), 6);
                assert_eq!(f[5].parse::<usize>().unwrap(), p.files[f[1]].len());
                let start: usize = f[3].parse().unwrap();
                let end: usize = f[4].parse().unwrap();
                assert!(p.files[f[2]][start..end].starts_with("include_text!"));
                resources.insert(f[1].to_string());
            }
            _ => panic!("unexpected audit record: {line}"),
        }
    }
    let expected_sources: Vec<_> = ids
        .iter()
        .filter(|p| {
            matches!(
                std::path::Path::new(p).extension().and_then(|e| e.to_str()),
                Some("taut" | "tauto")
            )
        })
        .cloned()
        .collect();
    let expected_resources: BTreeSet<_> = ids
        .into_iter()
        .filter(|p| !expected_sources.contains(p))
        .collect();
    assert_eq!(sources, expected_sources);
    assert_eq!(resources, expected_resources);
    for id in [
        "totes/unicode/src/classes.taut",
        "totes/text/src/utf8.taut",
        "totes/scan/src/longest.taut",
        "totes/llk/src/derives.taut",
    ] {
        assert!(sources.iter().any(|s| s == id), "{id}");
    }
    assert!(resources.contains("totes/unicode/src/tables/alphanumeric.txt"));
    let compilation = s.run(&p.encode().unwrap(), false);
    status(&compilation, "reader-unsupported", false);
}

#[test]
fn pure_imported_program_runs_after_inputs_are_removed() {
    let s = Scratch::new();
    let p = plan(
        "virtual_imports_compile_original_files",
        "src/main.taut",
        &["src/main.taut", "lib/value.taut"],
    );
    let generated = s.run(&p.encode().unwrap(), false);
    status(&generated, "generated", true);
    s.write("generated/src/main.rs", generated.stdout);
    s.write("generated/Cargo.toml", format!("[package]\nname=\"input-bundle-output\"\nversion=\"0.0.0\"\nedition=\"2024\"\n[dependencies]\ntauto-rt={{path={:?}}}\n[workspace]\n", root().join("crates/tauto-rt")));
    fs::remove_file(s.0.join("input.bundle")).unwrap();
    let executed = std::process::Command::new(env!("CARGO"))
        .current_dir(s.0.join("generated"))
        .env("CARGO_TARGET_DIR", s.0.join("target"))
        .env("CARGO_BUILD_BUILD_DIR", s.0.join("build"))
        .args(["run", "--offline", "--quiet"])
        .output()
        .unwrap();
    assert!(
        executed.status.success(),
        "{}",
        String::from_utf8_lossy(&executed.stderr)
    );
    assert_eq!(executed.stdout, b"42\n");
}

#[test]
fn strict_shared_bundle_route_separates_inventory_from_reader_semantics() {
    use tauto_test_suite::selfhost::{Actual, Backend, Verdict};
    let results = selfhost_harness::shared_cases::run(
        &root().join("cases"),
        Backend::Rust,
        Backend::Rust,
        "selfhost-input-bundle",
        &["rustgen".into()],
    )
    .unwrap();
    for id in [
        "virtual_imports_compile_original_files",
        "unused_imported_proof_is_not_erased",
        "resource_availability_does_not_expand_macro",
        "import_cycle_is_a_loader_diagnostic",
    ] {
        let result = results.iter().find(|r| r.name.ends_with(id)).unwrap();
        assert_eq!(
            result.verdict,
            Verdict::Passed,
            "{}: {:?}",
            result.name,
            result.verdict
        );
        assert!(result.artifacts.contains_key("input_bundle_sha256"));
    }
    let cycle = results
        .iter()
        .find(|r| r.name.ends_with("import_cycle_is_a_loader_diagnostic"))
        .unwrap();
    assert!(cycle.observations.iter().any(|o| o.stage == "load"
        && matches!(&o.actual, Actual::Rejected(message) if message.contains("import cycle"))));
    for id in [
        "missing_resource_retains_macro_contract",
        "resource_cannot_leave_tote_even_when_supplied",
        "resource_cannot_leave_and_reenter_tote",
        "resource_without_tote_stays_in_source_directory",
    ] {
        let result = results.iter().find(|r| r.name.ends_with(id)).unwrap();
        assert!(
            matches!(result.verdict, Verdict::Passed),
            "{}: {:?}",
            result.name,
            result.verdict
        );
        assert!(result.observations.iter().any(|o| o.stage == "macro"
            && matches!(&o.actual, Actual::Rejected(message) if message.contains("include."))));
        assert_eq!(
            result
                .artifacts
                .get("reader_implementation")
                .map(String::as_str),
            Some("tauto-source-reader/include_text; no macro evaluator")
        );
    }
    assert_eq!(results.len(), 8);
}

/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn fixture_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
            ("selfhost-input-bundle.eure", "oversized_resource_path") => {
                r#"fn answer(): Text { include_text!("a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a") }"#
            }
            ("selfhost-input-bundle.eure", "resolved_resource_depth_limit") => {
                r#"fn answer(): Text { include_text!("b/c") }"#
            }
            ("selfhost-input-bundle.eure", "plain_answer") => r#"fn answer(): i64 { 42 }"#,
            ("selfhost-input-bundle.eure", "oversized_import_path") => {
                r#"import "a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a""#
            }
            ("selfhost-input-bundle.eure", "resolved_import_depth_limit") => r#"import "b/c""#,
            ("selfhost-input-bundle.eure", "dependency_main") => r#"fn not_a_root(): i64 { 7 }"#,
            ("selfhost-input-bundle.eure", "dynamic_resource") => {
                r#"fn answer(path: Text): Text { include_text!(path) }"#
            }
            ("selfhost-input-bundle.eure", "resolved_import_byte_limit") => r#"import "bbbbbb""#,
            ("selfhost-input-bundle.eure", "resolved_resource_byte_limit") => {
                r#"fn answer(): Text { include_text!("bbbbbb") }"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn fixture(file: &str, name: &str) -> String {
        fixture_static(file, name).to_string()
    }
    pub fn file_static(file: &str, name: &str, input: &str) -> &'static str {
        match (file, name, input) {
            (
                "selfhost-input-bundle.eure",
                "resource_cannot_leave_tote_even_when_supplied",
                "app/src/main.taut",
            ) => r#"fn answer(): Text { include_text!("../../other/data.txt") }"#,
            (
                "selfhost-input-bundle.eure",
                "resource_cannot_leave_tote_even_when_supplied",
                "app/Tauto.eure",
            ) => r#"package { name="resource-fixture" }"#,
            (
                "selfhost-input-bundle.eure",
                "missing_resource_retains_macro_contract",
                "src/main.taut",
            ) => r#"fn answer(): Text { include_text!("../data/missing.txt") }"#,
            (
                "selfhost-input-bundle.eure",
                "missing_resource_retains_macro_contract",
                "Tauto.eure",
            ) => r#"package { name="resource-fixture" }"#,
            (
                "selfhost-input-bundle.eure",
                "virtual_imports_compile_original_files",
                "lib/value.taut",
            ) => r#"fn value(): i64 { 21 }"#,
            (
                "selfhost-input-bundle.eure",
                "virtual_imports_compile_original_files",
                "src/main.taut",
            ) => {
                r#"import "../lib/value.taut"
fn answer(): i64 { value() + value() }
"#
            }
            (
                "selfhost-input-bundle.eure",
                "resource_without_tote_stays_in_source_directory",
                "src/main.taut",
            ) => r#"fn answer(): Text { include_text!("../data.txt") }"#,
            ("selfhost-input-bundle.eure", "import_cycle_is_a_loader_diagnostic", "a.taut") => {
                r#"import "b.taut""#
            }
            ("selfhost-input-bundle.eure", "import_cycle_is_a_loader_diagnostic", "b.taut") => {
                r#"import "a.taut""#
            }
            (
                "selfhost-input-bundle.eure",
                "resource_availability_does_not_expand_macro",
                "src/main.taut",
            ) => r#"fn answer(): Text { include_text!("../data/日本語.txt") }"#,
            (
                "selfhost-input-bundle.eure",
                "resource_availability_does_not_expand_macro",
                "Tauto.eure",
            ) => r#"package { name="resource-fixture" }"#,
            (
                "selfhost-input-bundle.eure",
                "resource_cannot_leave_and_reenter_tote",
                "app/src/main.taut",
            ) => r#"fn answer(): Text { include_text!("../../app/data.txt") }"#,
            (
                "selfhost-input-bundle.eure",
                "resource_cannot_leave_and_reenter_tote",
                "app/Tauto.eure",
            ) => r#"package { name="resource-fixture" }"#,
            ("selfhost-input-bundle.eure", "unused_imported_proof_is_not_erased", "proof.taut") => {
                r#"theorem retained(A: Prop, a: A): A { a }"#
            }
            ("selfhost-input-bundle.eure", "unused_imported_proof_is_not_erased", "main.taut") => {
                r#"import "proof.taut"
fn answer(): i64 { 42 }
"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    #[allow(dead_code)]
    pub fn file(file: &str, name: &str, input: &str) -> String {
        file_static(file, name, input).to_string()
    }
}
