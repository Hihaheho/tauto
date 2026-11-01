use std::process::Command;

#[test]
fn top_level_help_and_version_succeed_on_stdout() {
    for flag in ["--help", "-h", "help"] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .arg(flag)
            .output()
            .unwrap();
        assert!(out.status.success());
        assert!(out.stderr.is_empty());
        let text = String::from_utf8(out.stdout).unwrap();
        for command in [
            "tauto run",
            "tauto test",
            "tauto bench",
            "tauto doc",
            "tauto build",
            "tauto syntax",
            "tauto macro",
            "tauto bind",
            "tauto --help",
            "tauto --version",
        ] {
            assert!(text.contains(command), "{command}: {text}");
        }
    }
    for flag in ["--version", "-V"] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .arg(flag)
            .output()
            .unwrap();
        assert!(out.status.success());
        assert!(out.stderr.is_empty());
        assert_eq!(
            String::from_utf8(out.stdout).unwrap(),
            format!("tauto {}\n", env!("CARGO_PKG_VERSION"))
        );
    }
    for args in [vec!["--not-a-command"], vec!["--version", "extra"], vec![]] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            // The messages below are the English ones, whatever the language here.
            .env("TAUTO_LANG", "en")
            .args(args)
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(2));
        assert!(out.stdout.is_empty());
        assert!(String::from_utf8_lossy(&out.stderr).contains("usage: tauto"));
    }
}
