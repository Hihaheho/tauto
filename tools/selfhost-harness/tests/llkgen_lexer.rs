//! Unicode scanner properties and contextual scanner regex diagnostics.
use selfhost_harness::run_tote_native;

const STEPS: u64 = 200_000_000_000;

#[test]
fn xid_identifier_tables_accept_unicode_starts_and_continuations() {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("tauto-llk-xid-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let grammar = dir.join("identifier.par");
    std::fs::write(&grammar, "%start Identifier\n%title \"identifier\"\n%%\nIdentifier: /[\\p{XID_Start}_][\\p{XID_Continue}_]*/;\n").unwrap();
    let out = run_tote_native(
        "syntaxgen",
        &["--gen".into(), grammar.display().to_string()],
        STEPS,
    );
    assert_eq!(out.error, None);
    assert_eq!(out.exit, Some(0), "{}", out.stderr);
    let tables = tauto_syntax::Tables::read(&out.stdout).unwrap();
    for text in [
        "日本語",
        "識別子_42",
        "a\u{301}",
        "a\u{b7}",
        "_x",
        "αβ",
        "a9",
    ] {
        assert!(
            tauto_syntax::parse(&tables, text, 0, &Default::default()).is_ok(),
            "{text:?}"
        );
    }
    for text in ["", "9abc", "\u{301}a", "\u{b7}a", "🙂", "a-b"] {
        assert!(
            tauto_syntax::parse(&tables, text, 0, &Default::default()).is_err(),
            "{text:?}"
        );
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn regex_errors_identify_rule_and_unicode_character_position() {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("tauto-llk-regex-errors-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let grammar = dir.join("bad.par");
    for (rule, context, position, reason) in [
        ("Bad: /日本語[z-a]/;", "rule Bad", 7, "a range is backwards"),
        ("Bad: /\\d(/;", "rule Bad", 4, "an unclosed group"),
        ("Bad: /\\p{Nd/;", "rule Bad", 6, "an unfinished property"),
        ("Bad: /abc(/;", "rule Bad", 5, "an unclosed group"),
        ("Bad: /[abc/;", "rule Bad", 5, "an unfinished class"),
        (
            "Bad: /\\p{Unknown}/;",
            "rule Bad",
            3,
            "the property Unknown is not supported",
        ),
        (
            "Bad: /a/ ?= /日本語(/;",
            "lookahead of rule Bad",
            5,
            "an unclosed group",
        ),
        (
            "Bad: One Two;\nOne: /[abc/;\nTwo: /[abc/;",
            "rule One, Two",
            5,
            "an unfinished class",
        ),
    ] {
        std::fs::write(
            &grammar,
            format!("%start Bad\n%title \"bad\"\n%%\n{rule}\n"),
        )
        .unwrap();
        let out = run_tote_native(
            "syntaxgen",
            &["--gen".into(), grammar.display().to_string()],
            STEPS,
        );
        assert_eq!(out.error, None);
        assert_eq!(out.exit, Some(1), "{out:?}");
        assert_eq!(out.stdout, "");
        assert_eq!(
            out.stderr.trim(),
            format!(
                "the grammar: regular expression in {context} at character {position}: {reason}"
            )
        );
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn decimal_digit_aliases_and_complements_use_unicode_decimal_category() {
    let dir = std::env::temp_dir()
        .canonicalize()
        .unwrap()
        .join(format!("tauto-llk-decimal-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let grammar = dir.join("number.par");
    let digits = ["0123456789", "٠١٢", "०१२", "１２９", "𝟘𝟡"];
    let non_digits = [
        "²", "Ⅳ", "四", "a", "\u{301}", "🙂", ":", "/", "\u{65f}", "\u{66a}",
    ];
    for (pattern, negated) in [
        (r"\d+", false),
        (r"\p{Nd}+", false),
        (r"\p{Decimal_Number}+", false),
        (r"\D+", true),
        (r"\P{Nd}+", true),
        (r"\P{Decimal_Number}+", true),
        (r"[^\d]+", true),
    ] {
        std::fs::write(
            &grammar,
            format!("%start Number\n%%\nNumber: /{pattern}/;\n"),
        )
        .unwrap();
        let out = run_tote_native(
            "syntaxgen",
            &["--gen".into(), grammar.display().to_string()],
            STEPS,
        );
        assert_eq!(out.error, None);
        assert_eq!(out.exit, Some(0), "{pattern}: {}", out.stderr);
        let tables = tauto_syntax::Tables::read(&out.stdout).unwrap();
        for (texts, expected) in [(&digits[..], !negated), (&non_digits[..], negated)] {
            for text in texts {
                assert_eq!(
                    tauto_syntax::parse(&tables, text, 0, &Default::default()).is_ok(),
                    expected,
                    "{pattern}: {text:?}"
                );
            }
        }
        for text in ["", "1a", "١\u{301}"] {
            assert!(
                tauto_syntax::parse(&tables, text, 0, &Default::default()).is_err(),
                "{pattern}: {text:?}"
            );
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}
