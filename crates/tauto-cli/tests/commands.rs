//! Commands a tote gives (`docs/design/commands.md`): `tauto NAME ARGS…` in a
//! project, what the project grants them, and how a name is chosen.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn root(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("tauto-commands-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    d
}

/// `<root>/<name>/Tauto.eure`, with `more` after its `package`, and `files`.
fn tote(root: &Path, name: &str, more: &str, files: &[(&str, &str)]) -> PathBuf {
    let d = root.join(name);
    fs::create_dir_all(d.join("src")).unwrap();
    fs::write(
        d.join("Tauto.eure"),
        format!(
            "package {{\n  name = \"{name}\"\n  version = \"0.1.0\"\n  sources = [\"src\"]\n}}\n{more}"
        ),
    )
    .unwrap();
    for (file, text) in files {
        let path = d.join(file);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    d
}

fn tauto(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        .current_dir(dir)
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(args)
        .output()
        .unwrap()
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

const GREET: &str = r#"
commands {
  hi {
    main = "cmd/hi.taut"
    about = "Greets each name it is given"
  }
  cat {
    main = "cmd/cat.taut"
    about = "Prints a file"
  }
}
"#;

/// The tote `greet`, giving `hi` and `cat`.
fn greet(root: &Path) -> PathBuf {
    tote(
        root,
        "greet",
        GREET,
        &[
            (
                "src/greet.taut",
                r#"fn greeting(name: Text): Text {
  concat("hi ", name)
}
"#,
            ),
            (
                "cmd/hi.taut",
                r#"fn each_name(names: List(Text)): Unit ! {stdout} {
  match names {
    Nil => #()
    Cons(n, rest) => {
      print(concat(greeting(n), "\n"))
      each_name(rest)
    }
  }
}

each_name(perform argv())
"#,
            ),
            (
                "cmd/cat.taut",
                r#"match perform argv() {
  Cons(path, _) => match read_file(path) {
    Ok(t) => print(t)
    Err(e) => {
      eprint(concat(e, "\n"))
      perform exit(3)
    }
  }
  Nil => perform exit(2)
}
"#,
            ),
        ],
    )
}

fn depends(names: &[&str]) -> String {
    let lines: Vec<String> = names
        .iter()
        .map(|n| format!("  {n} {{ path = \"../{n}\" }}\n"))
        .collect();
    format!("dependencies {{\n{}}}\n", lines.concat())
}

#[test]
fn a_dependencys_command_runs_with_all_its_arguments() {
    let r = root("runs");
    greet(&r);
    let app = tote(&r, "app", &depends(&["greet"]), &[]);
    // `--offline` and `--help` after the name are the command's.
    let out = tauto(&app.join("src"), &["hi", "Ryo", "--offline", "--help"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), "hi Ryo\nhi --offline\nhi --help\n");
}

#[test]
fn the_host_denies_a_command_what_the_project_does_not_grant() {
    let r = root("grant");
    greet(&r);
    let app = tote(
        &r,
        "app",
        &depends(&["greet"]),
        &[("data/a.txt", "inside\n")],
    );
    fs::write(r.join("outside.txt"), "outside\n").unwrap();
    let out = tauto(&app, &["cat", "data/a.txt"]);
    assert_eq!(out.status.code(), Some(1));
    let err = stderr(&out);
    assert!(
        err.starts_with(
            "the command cat of greet needs read to run; the host denies it by default\n"
        ),
        "{err}"
    );
    assert!(err.contains("tote = \"greet\""), "{err}");
    assert!(err.contains("read = [\"PATH\"]"), "{err}");
    // A flag widens nothing: it is the command's argument.
    let out = tauto(&app, &["cat", "--allow-read", "data/a.txt"]);
    assert_eq!(out.status.code(), Some(1));

    let grant = "trust {\n  commands {\n    cat {\n      tote = \"greet\"\n      read = [\"data\"]\n    }\n  }\n}\n";
    tote(
        &r,
        "app",
        &format!("{}{grant}", depends(&["greet"])),
        &[("data/a.txt", "inside\n")],
    );
    // The granted path is the project's, wherever the command runs from.
    let out = tauto(&app.join("src"), &["cat", "../data/a.txt"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), "inside\n");
    let out = tauto(&app, &["cat", "../outside.txt"]);
    assert_eq!(out.status.code(), Some(3), "{}", stderr(&out));
    assert!(stderr(&out).contains("does not cover"), "{}", stderr(&out));
}

#[test]
fn a_grant_is_for_one_totes_command() {
    let r = root("grant-tote");
    greet(&r);
    let grant = "trust {\n  commands {\n    cat {\n      tote = \"other\"\n      read = true\n    }\n  }\n}\n";
    let app = tote(&r, "app", &format!("{}{grant}", depends(&["greet"])), &[]);
    let out = tauto(&app, &["cat", "Tauto.eure"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(
        stderr(&out).contains("trust.commands.cat in Tauto.eure is for the tote other, which gives no command cat (greet does)"),
        "{}",
        stderr(&out)
    );
}

#[test]
fn a_dependencys_externs_need_the_projects_trust() {
    let r = root("extern");
    tote(
        &r,
        "ext",
        "commands {\n  leak {\n    main = \"cmd/leak.taut\"\n    about = \"Calls host code\"\n  }\n}\n",
        &[
            (
                "src/ext.taut",
                r#"extern {
  fn leak(url: Text): Text
}
"#,
            ),
            (
                "cmd/leak.taut",
                r#"print(leak("x"))
"#,
            ),
        ],
    );
    let app = tote(&r, "app", &depends(&["ext"]), &[]);
    let out = tauto(&app, &["leak"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(
        stderr(&out).starts_with("dependency ext declares extern functions"),
        "{}",
        stderr(&out)
    );
}

#[test]
fn two_totes_giving_one_name_are_chosen_between() {
    let r = root("choose");
    greet(&r);
    tote(
        &r,
        "other",
        "commands {\n  hi {\n    main = \"cmd/hi.taut\"\n    about = \"Another hi\"\n  }\n}\n",
        &[(
            "cmd/hi.taut",
            r#"print("other\n")
"#,
        )],
    );
    let app = tote(&r, "app", &depends(&["greet", "other"]), &[]);
    let out = tauto(&app, &["hi", "x"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(
        stderr(&out).starts_with("the totes greet and other each give a command hi; choose one"),
        "{}",
        stderr(&out)
    );
    let help = stdout(&tauto(&app, &["--help"]));
    assert!(
        help.contains("tauto hi  (other) Another hi  [not run: several totes give it"),
        "{help}"
    );
    let chosen = "trust {\n  commands {\n    hi { tote = \"other\" }\n  }\n}\n";
    tote(
        &r,
        "app",
        &format!("{}{chosen}", depends(&["greet", "other"])),
        &[],
    );
    let out = tauto(&app, &["hi", "x"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), "other\n");
}

#[test]
fn the_projects_own_command_runs_and_wins() {
    let r = root("own");
    let greet = greet(&r);
    let out = tauto(&greet, &["hi", "me"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), "hi me\n");
    let app = tote(
        &r,
        "app",
        &format!(
            "{}commands {{\n  hi {{\n    main = \"cmd/hi.taut\"\n    about = \"Mine\"\n  }}\n}}\n",
            depends(&["greet"])
        ),
        &[(
            "cmd/hi.taut",
            r#"print("other\n")
"#,
        )],
    );
    let out = tauto(&app, &["hi"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), "other\n");
}

#[test]
fn only_direct_dependencies_give_commands() {
    let r = root("direct");
    greet(&r);
    tote(&r, "mid", &depends(&["greet"]), &[]);
    let app = tote(&r, "app", &depends(&["mid"]), &[]);
    let out = tauto(&app, &["hi"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(
        stderr(&out).starts_with("no command hi:"),
        "{}",
        stderr(&out)
    );
}

#[test]
fn a_built_in_name_is_never_a_totes_command() {
    let r = root("built-in");
    tote(
        &r,
        "shadow",
        "commands {\n  test {\n    main = \"cmd/test.taut\"\n    about = \"Would be tauto test\"\n  }\n}\n",
        &[(
            "cmd/test.taut",
            r#"print("other\n")
"#,
        )],
    );
    let app = tote(&r, "app", &depends(&["shadow"]), &[]);
    let help = stdout(&tauto(&app, &["--help"]));
    assert!(
        help.contains("tauto test  (shadow) Would be tauto test  [not run: tauto has a built-in command of this name]"),
        "{help}"
    );
    let out = tauto(&app, &["test", "--json"]);
    assert!(!stdout(&out).contains("other"), "{}", stdout(&out));
}

#[test]
fn help_audit_and_add_show_the_commands() {
    let r = root("show");
    greet(&r);
    let app = tote(&r, "app", "", &[]);
    let out = tauto(&app, &["add", "--path", "../greet"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stdout(&out).contains("  tauto hi  Greets each name it is given\n"),
        "{}",
        stdout(&out)
    );
    let help = stdout(&tauto(&app, &["--help"]));
    assert!(
        help.contains("  tauto cat  (greet) Prints a file  [granted nothing]\n"),
        "{help}"
    );
    let audit = stdout(&tauto(&app, &["audit", "--json"]));
    assert!(
        audit.contains(r#""commands":[{"name":"cat","main":"cmd/cat.taut","about":"Prints a file","granted":[]}"#),
        "{audit}"
    );
}

#[test]
fn check_reads_each_command_as_it_runs() {
    let r = root("check");
    let greet = greet(&r);
    let out = tauto(&greet, &["check", "--tote", "."]);
    assert!(out.status.success(), "{}{}", stdout(&out), stderr(&out));
    fs::write(
        greet.join("cmd/hi.taut"),
        r#"print(greeting(1))
"#,
    )
    .unwrap();
    let out = tauto(&greet, &["check", "--tote", "."]);
    assert_eq!(out.status.code(), Some(1));
    assert!(stdout(&out).contains("cmd/hi.taut:1:"), "{}", stdout(&out));
    // A main among the sources would be read by every dependent.
    let inside = GREET.replace("cmd/hi.taut", "src/greet.taut");
    tote(&r, "greet", &inside, &[]);
    let out = tauto(&greet, &["check", "--tote", "."]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        stderr(&out).contains("which is one of its sources"),
        "{}",
        stderr(&out)
    );
}
