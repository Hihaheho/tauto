use selfhost_harness::{root, run_tote_at};

#[test]
fn type_comparison_and_declaration_budgets_cover_the_full_input() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("implementation-audit");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Tauto.eure"),
        "package { name = \"implementation-audit\" }",
    )
    .unwrap();
    let source = include_str!("data/implementation_audit.taut").replace(
        "../../../../totes",
        &root().join("totes").display().to_string(),
    );
    std::fs::write(dir.join("src/main.taut"), source).unwrap();
    let out = run_tote_at(&dir, &[], 100_000_000);
    assert_eq!(out.error, None, "{out:?}");
    assert_eq!(out.stderr, "");
    assert_eq!(
        out.stdout,
        "wide equality = true\narity differs = false\nclass and instance extent = 198\n"
    );
}

#[test]
fn nibcheck_modes_preserve_file_order_and_parse_errors() {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("nibcheck-cli-audit");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Tauto.eure"),
        "package { name = \"nibcheck-cli-audit\" }",
    )
    .unwrap();
    let repo = root();
    let mut source = format!(
        r#"import "{}"
"#,
        repo.join("totes/unicode/src/classes.taut")
            .display()
            .to_string()
    );
    for file in ["types_run", "lin_value", "modules"] {
        source.push_str(&format!(
            r#"import "{}"
"#,
            repo.join(format!("totes/nibcheck/src/{file}.taut"))
                .display()
                .to_string()
        ));
    }
    source.push_str(&std::fs::read_to_string(repo.join("totes/nibcheck/src/main.taut")).unwrap());
    std::fs::write(dir.join("src/main.taut"), source).unwrap();
    let prelude = dir.join("prelude.taut");
    let good = dir.join("good.taut");
    let bad = dir.join("bad.taut");
    std::fs::write(&prelude, "").unwrap();
    std::fs::write(
        &good,
        r#"let value := 1
"#,
    )
    .unwrap();
    std::fs::write(&bad, r#"fn broken("#).unwrap();
    for mode in ["--rows", "--types", "--lin"] {
        let args = [
            mode.to_string(),
            prelude.display().to_string(),
            good.display().to_string(),
            bad.display().to_string(),
        ];
        let out = run_tote_at(&dir, &args, 100_000_000);
        assert_eq!(out.error, None, "{mode}: {out:?}");
        assert_eq!(out.stderr, "", "{mode}");
        let head = format!("== {}\n", good.display());
        let tail = format!("== {}\nerror\n", bad.display());
        assert!(out.stdout.starts_with(&head), "{mode}: {}", out.stdout);
        assert!(out.stdout.ends_with(&tail), "{mode}: {}", out.stdout);
        if mode == "--types" {
            assert!(out.stdout.contains("let value i64\n"), "{}", out.stdout);
        } else if mode == "--rows" {
            assert_eq!(
                out.stdout,
                format!(
                    "{head}quant Div Zero\nquant Exceeded AtMostOne\nquant show Direct\n{tail}"
                )
            );
        } else {
            assert_eq!(out.stdout, format!("{head}{tail}"));
        }
    }
}
