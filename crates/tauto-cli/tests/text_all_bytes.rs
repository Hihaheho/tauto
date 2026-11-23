//! `Text::all_bytes` gives the same answer on every backend as its
//! definition over the bytes.
use std::fs;
use std::process::Command;

#[test]
fn all_bytes_agrees_on_every_backend() {
    let root = std::env::temp_dir().join(format!("tauto-all-bytes-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    let main = root.join("main.taut");
    fs::write(
        &main,
        r#"import std::base
import std::text { Text }

fn plain(c: Nat): Bool {
  not(Bool::or(c == 34, Bool::or(c == 92, c < 32)))
}

show(&Text::all_bytes("ab\"c", plain))
show(&Text::all_bytes("abc", plain))
show(&Text::all_bytes("", plain))
show(&Text::all_bytes("a\nb", plain))
show(&Text::all_bytes("é", (c: Nat) => 128 <= c))
"#,
    )
    .unwrap();
    let expected = "false\ntrue\ntrue\nfalse\ntrue\n";
    for args in [
        &[][..],
        &["--backend", "rust"][..],
        &["--backend", "javascript"][..],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("run")
            .args(args)
            .arg(&main)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(String::from_utf8_lossy(&out.stdout), expected, "{args:?}");
    }
    let _ = fs::remove_dir_all(&root);
}
