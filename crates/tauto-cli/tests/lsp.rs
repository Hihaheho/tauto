//! `tauto lsp` over a pipe: the handshake, the colours and the completion of
//! a syntax literal, a diagnostic, and the answers about names: hover,
//! definition, references and rename.

use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Command, Stdio};

use serde_json::{Value, json};

const MATH: &str = include_str!("../../tauto/tests/syntax_fixtures/math.par");

fn frame(v: &Value) -> String {
    let b = v.to_string();
    format!("Content-Length: {}\r\n\r\n{b}", b.len())
}

fn read(out: &mut impl BufRead) -> Value {
    let mut n = 0;
    loop {
        let mut l = String::new();
        out.read_line(&mut l).unwrap();
        if let Some(v) = l.trim().strip_prefix("Content-Length:") {
            n = v.trim().parse().unwrap();
        }
        if l.trim().is_empty() {
            break;
        }
    }
    let mut b = vec![0; n];
    out.read_exact(&mut b).unwrap();
    serde_json::from_slice(&b).unwrap()
}

#[test]
fn the_server_colours_completes_and_reports() {
    let dir = std::env::temp_dir().join(format!("tauto-lsp-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let tables =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../tauto/tests/syntax_fixtures/.tauto-syntax");
    std::os::unix::fs::symlink(tables, dir.join(".tauto-syntax")).unwrap();
    std::fs::write(
        dir.join("math.nib"),
        format!(
            r#"import std::prelude::Macro
syntax!(math, ```par
{}```) => struct Eqn, struct Paren, struct Sum, struct Sum_Rep1,
  enum Term, fn parse
macro fn math(e: math::Eqn): SynExpr ! {{macro_error, Div}} {{ quote {{ Eq(Nat, 1, 1) }} }}
"#,
            MATH
        ),
    )
    .unwrap();
    let main = r#"import "math.nib"
theorem t(): math!(`1 + 2 = 3`) { Refl(Nat, 1) }
"#;
    let open = dir.join("main.nib");
    std::fs::write(&open, main).unwrap();
    let uri = format!("file://{}", open.display());

    let mut child = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .arg("lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    let mut out = BufReader::new(child.stdout.take().unwrap());
    let mut send = |v: Value| input.write_all(frame(&v).as_bytes()).unwrap();

    send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    let init = read(&mut out);
    assert_eq!(init["result"]["capabilities"]["textDocumentSync"], 1);

    send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen",
        "params":{"textDocument":{"uri":uri,"text":main}}}));
    let published = read(&mut out);
    assert_eq!(published["method"], "textDocument/publishDiagnostics");

    send(
        json!({"jsonrpc":"2.0","id":2,"method":"textDocument/semanticTokens/full",
        "params":{"textDocument":{"uri":uri}}}),
    );
    let tokens = read(&mut out);
    let data = tokens["result"]["data"].as_array().unwrap();
    // `1 + 2 = 3` on line 1: five tokens of five numbers each; the first is a number.
    assert_eq!(data.len(), 25, "{data:?}");
    assert_eq!(data[0], 1);
    assert_eq!(data[3], 1);

    // After `1 + ` the grammar wants a number or a parenthesis.
    let col = main.lines().nth(1).unwrap().find("2 =").unwrap();
    let changed = main.replace("1 + 2 = 3", "1 + ");
    send(json!({"jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":uri},"contentChanges":[{"text":changed}]}}));
    let _ = read(&mut out);
    send(
        json!({"jsonrpc":"2.0","id":3,"method":"textDocument/completion",
        "params":{"textDocument":{"uri":uri},"position":{"line":1,"character":col}}}),
    );
    let items = read(&mut out);
    let mut labels: Vec<&str> = items["result"]
        .as_array()
        .unwrap()
        .iter()
        .map(|i| i["label"].as_str().unwrap())
        .collect();
    labels.sort();
    assert_eq!(labels, ["LParen", "Num"]);

    send(json!({"jsonrpc":"2.0","id":4,"method":"shutdown"}));
    let _ = read(&mut out);
    send(json!({"jsonrpc":"2.0","method":"exit"}));
    drop(input);
    assert!(child.wait().unwrap().success());
}

/// A call of a macro, a syntax and the macro that reads it, in two files.
fn macro_fixture(name: &str) -> (std::path::PathBuf, std::path::PathBuf) {
    let dir = std::env::temp_dir().join(format!("tauto-lsp-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let tables =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../tauto/tests/syntax_fixtures/.tauto-syntax");
    std::os::unix::fs::symlink(tables, dir.join(".tauto-syntax")).unwrap();
    std::fs::write(
        dir.join("math.nib"),
        format!(
            r#"import std::prelude::Macro
syntax!(math, ```par
{}```) => struct Eqn, struct Paren, struct Sum, struct Sum_Rep1,
  enum Term, fn parse
macro fn math(e: math::Eqn): SynExpr ! {{macro_error, Div}} {{ quote {{ Eq(Nat, 1, 1) }} }}
"#,
            MATH
        ),
    )
    .unwrap();
    let open = dir.join("main.nib");
    std::fs::write(
        &open,
        r#"import "math.nib"
theorem t(): math!(`1 + 2 = 3`) { Refl(Nat, 1) }
fn answer(n: i64): i64 { let m := n + 1
 m + n }
"#,
    )
    .unwrap();
    (dir, open)
}

#[test]
fn the_server_answers_about_names() {
    let (dir, open) = macro_fixture("names");
    let main = std::fs::read_to_string(&open).unwrap();
    let uri = format!("file://{}", open.display());
    let math_uri = format!(
        "file://{}",
        dir.join("math.nib").canonicalize().unwrap().display()
    );

    let mut child = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .arg("lsp")
        .env("LANG", "ja_JP.UTF-8")
        .env_remove("TAUTO_LANG")
        .env_remove("LC_ALL")
        .env_remove("LC_MESSAGES")
        .env("XDG_CONFIG_HOME", dir.join("config"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    let mut out = BufReader::new(child.stdout.take().unwrap());
    let mut send = |v: Value| input.write_all(frame(&v).as_bytes()).unwrap();

    send(json!({"jsonrpc":"2.0","id":1,"method":"initialize",
        "params":{"rootUri": format!("file://{}", dir.display())}}));
    let caps = &read(&mut out)["result"]["capabilities"];
    assert_eq!(caps["hoverProvider"], true);
    assert_eq!(caps["definitionProvider"], true);
    assert_eq!(caps["renameProvider"]["prepareProvider"], true);

    send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen",
        "params":{"textDocument":{"uri":uri,"text":main}}}));
    let _ = read(&mut out);

    let at = |line: usize, needle: &str, into: usize| -> Value {
        let text = main.lines().nth(line).unwrap();
        json!({"line": line, "character": text.find(needle).unwrap() + into})
    };
    let mut id = 10;
    let mut ask = |method: &str, extra: Value| -> Value {
        id += 1;
        let mut params = json!({"textDocument": {"uri": uri}});
        for (k, v) in extra.as_object().unwrap() {
            params[k] = v.clone();
        }
        send(json!({"jsonrpc":"2.0","id":id,"method":method,"params":params}));
        read(&mut out)
    };

    // The transport preserves the CLI proof's Japanese text and hover ranges.
    let cli = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["--lang", "ja", "proof"])
        .arg(&open)
        .args(["t", "--format", "natural"])
        .output()
        .unwrap();
    assert!(
        cli.status.success(),
        "{}",
        String::from_utf8_lossy(&cli.stderr)
    );
    let natural = String::from_utf8(cli.stdout).unwrap();
    assert!(natural.contains("を示す"), "{natural}");
    let indented = natural
        .lines()
        .map(|line| format!("    {line}\n"))
        .collect::<String>();
    let mut theorem_hover = None;
    for (needle, into, width) in [("theorem", 2, 7), ("t()", 0, 1)] {
        let h = ask(
            "textDocument/hover",
            json!({"position": at(1, needle, into)}),
        );
        let contents = h["result"]["contents"]["value"].as_str().unwrap();
        assert!(contents.ends_with(&indented), "{contents}");
        let range = &h["result"]["range"];
        assert_eq!(range["start"]["line"], 1);
        assert_eq!(
            range["end"]["character"].as_u64().unwrap()
                - range["start"]["character"].as_u64().unwrap(),
            width
        );
        if let Some(first) = &theorem_hover {
            assert_eq!(contents, first);
        }
        theorem_hover = Some(contents.to_string());
    }

    // The hover on a call of a macro shows what it expands to.
    let h = ask("textDocument/hover", json!({"position": at(1, "math!", 1)}));
    let text = h["result"]["contents"]["value"].as_str().unwrap();
    assert!(text.contains("macro"), "{text}");
    assert!(text.contains("expands to"), "{text}");
    assert!(text.contains("Eq(Nat, 1, 1)"), "{text}");

    // The macro's name goes to the `macro` line of the other file.
    let d = ask(
        "textDocument/definition",
        json!({"position": at(1, "math!", 1)}),
    );
    assert_eq!(d["result"]["uri"], math_uri.as_str(), "{d}");
    let math_nib = std::fs::read_to_string(dir.join("math.nib")).unwrap();
    let line = math_nib
        .lines()
        .position(|l| l.starts_with("macro fn math"))
        .unwrap();
    assert_eq!(d["result"]["range"]["start"]["line"], line);

    // A local of the second function: its type is the checker's.
    let h = ask(
        "textDocument/hover",
        json!({"position": at(2, "m := n", 0)}),
    );
    let text = h["result"]["contents"]["value"].as_str().unwrap();
    assert!(text.contains("let m"), "{text}");
    assert!(text.contains("type: `i64`"), "{text}");

    // Its uses, and a rename.
    let r = ask(
        "textDocument/references",
        json!({"position": at(2, "m := n", 0),
        "context": {"includeDeclaration": true}}),
    );
    assert_eq!(r["result"].as_array().unwrap().len(), 2, "{r}");
    let p = ask(
        "textDocument/prepareRename",
        json!({"position": at(2, "m := n", 0)}),
    );
    assert_eq!(p["result"]["placeholder"], "m");
    let r = ask(
        "textDocument/rename",
        json!({"position": at(2, "m := n", 0), "newName": "next"}),
    );
    let edits = r["result"]["changes"][&uri]
        .as_array()
        .unwrap_or_else(|| panic!("{r}"));
    assert_eq!(edits.len(), 2, "{r}");
    assert!(edits.iter().all(|e| e["newText"] == "next"));
    // A rename that would capture is an error with a reason.
    let r = ask(
        "textDocument/rename",
        json!({"position": at(2, "m := n", 0), "newName": "n"}),
    );
    assert!(r["error"]["message"].as_str().unwrap().contains("n"), "{r}");
    // So is a name the server cannot find the declaration of.
    let p = ask(
        "textDocument/prepareRename",
        json!({"position": at(0, "import", 1)}),
    );
    assert!(p["error"].is_object(), "{p}");

    // didChange invalidates the proof even though the declaration name is unchanged.
    let changed = main.replace("Refl(Nat, 1)", "?pending");
    send(json!({"jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":uri},"contentChanges":[{"text":changed}]}}));
    let _ = read(&mut out);
    send(
        json!({"jsonrpc":"2.0","id":98,"method":"textDocument/hover",
        "params":{"textDocument":{"uri":uri},"position": at(1, "theorem", 1)}}),
    );
    let h = read(&mut out);
    let contents = h["result"]["contents"]["value"].as_str().unwrap();
    assert!(contents.contains("?pending"), "{contents}");
    assert!(!contents.ends_with(&indented), "{contents}");

    send(json!({"jsonrpc":"2.0","id":99,"method":"shutdown"}));
    let _ = read(&mut out);
    send(json!({"jsonrpc":"2.0","method":"exit"}));
    drop(input);
    assert!(child.wait().unwrap().success());
}

#[test]
fn a_wrong_goal_in_a_step_gets_a_quick_fix() {
    let dir = std::env::temp_dir().join(format!("tauto-lsp-fix-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("lib.taut"),
        r#"macro fn same(s: ProofStep): SynExpr { Syn::hole(1, s.span) }
"#,
    )
    .unwrap();
    let main = r#"import "lib.taut"
theorem t(n: Nat): n = n {
  by same!(): n = n {
    ⊢ Succ(n) = n from ?rest
  }
}
"#;
    let open = dir.join("main.taut");
    std::fs::write(&open, main).unwrap();
    let uri = format!("file://{}", open.display());

    let mut child = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .arg("lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    let mut out = BufReader::new(child.stdout.take().unwrap());
    let mut send = |v: Value| input.write_all(frame(&v).as_bytes()).unwrap();

    send(json!({"jsonrpc":"2.0","id":1,"method":"initialize",
        "params":{"rootUri": format!("file://{}", dir.display())}}));
    let caps = &read(&mut out)["result"]["capabilities"];
    assert!(caps["codeActionProvider"].is_object(), "{caps}");

    send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen",
        "params":{"textDocument":{"uri":uri,"text":main}}}));
    let published = read(&mut out);
    let diagnostics = published["params"]["diagnostics"].clone();
    let mismatch = diagnostics
        .as_array()
        .unwrap()
        .iter()
        .find(|d| {
            d["message"]
                .as_str()
                .unwrap()
                .contains("step.goal_mismatch")
        })
        .unwrap_or_else(|| panic!("{diagnostics}"))
        .clone();

    send(
        json!({"jsonrpc":"2.0","id":2,"method":"textDocument/codeAction",
        "params":{"textDocument":{"uri":uri},
                  "range": mismatch["range"],
                  "context":{"diagnostics":[mismatch]}}}),
    );
    let actions = read(&mut out);
    let action = &actions["result"][0];
    assert_eq!(action["kind"], "quickfix", "{actions}");
    let edit = &action["edit"]["changes"][&uri][0];
    assert_eq!(edit["newText"], "⊢ n = n", "{actions}");
    // The range is the arm's `⊢ …` up to the `from`, on the fourth line.
    assert_eq!(edit["range"]["start"]["line"], 3, "{actions}");
    assert_eq!(edit["range"]["start"]["character"], 4, "{actions}");
    assert_eq!(edit["range"]["end"]["character"], 17, "{actions}");

    send(json!({"jsonrpc":"2.0","id":3,"method":"shutdown"}));
    let _ = read(&mut out);
    send(json!({"jsonrpc":"2.0","method":"exit"}));
    drop(input);
    assert!(child.wait().unwrap().success());
}

#[test]
fn a_syntax_error_at_the_end_of_the_file_is_shown_at_the_end() {
    let dir = std::env::temp_dir().join(format!("tauto-lsp-eof-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    // The body of `f` is never closed: the parser runs into the end of the file.
    let main = "fn f(n: Nat): Nat {\n  n\n";
    let open = dir.join("main.taut");
    std::fs::write(&open, main).unwrap();
    let uri = format!("file://{}", open.display());

    let mut child = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .arg("lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    let mut out = BufReader::new(child.stdout.take().unwrap());
    let mut send = |v: Value| input.write_all(frame(&v).as_bytes()).unwrap();

    send(json!({"jsonrpc":"2.0","id":1,"method":"initialize",
        "params":{"rootUri": format!("file://{}", dir.display())}}));
    let _ = read(&mut out);
    send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen",
        "params":{"textDocument":{"uri":uri,"text":main}}}));
    let published = read(&mut out);
    let diagnostics = published["params"]["diagnostics"].clone();
    let first = &diagnostics[0];
    // The end of the file is the third line (from 0, the second), not the first.
    assert_eq!(first["range"]["start"]["line"], 2, "{diagnostics}");
    assert_eq!(first["range"]["start"]["character"], 0, "{diagnostics}");

    send(json!({"jsonrpc":"2.0","id":2,"method":"shutdown"}));
    let _ = read(&mut out);
    send(json!({"jsonrpc":"2.0","method":"exit"}));
    drop(input);
    assert!(child.wait().unwrap().success());
}

#[test]
fn an_escape_becomes_its_sign_as_it_is_typed() {
    let dir = std::env::temp_dir().join(format!("tauto-lsp-escape-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let uri = format!("file://{}", dir.join("main.taut").display());

    let mut child = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .arg("lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    let mut out = BufReader::new(child.stdout.take().unwrap());
    let mut send = |v: Value| input.write_all(frame(&v).as_bytes()).unwrap();

    send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}));
    let caps = &read(&mut out)["result"]["capabilities"];
    assert_eq!(
        caps["completionProvider"]["triggerCharacters"],
        json!(["\\"])
    );
    let on_type = &caps["documentOnTypeFormattingProvider"];
    assert_eq!(on_type["firstTriggerCharacter"], " ");
    assert!(
        on_type["moreTriggerCharacter"]
            .as_array()
            .unwrap()
            .contains(&json!("("))
    );

    let text = "theorem t(): \\forall ";
    send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen",
        "params":{"textDocument":{"uri":uri,"text":text}}}));
    let _ = read(&mut out);
    send(
        json!({"jsonrpc":"2.0","id":2,"method":"textDocument/onTypeFormatting",
        "params":{"textDocument":{"uri":uri},"position":{"line":0,"character":21},
            "ch":" ","options":{"tabSize":2,"insertSpaces":true}}}),
    );
    assert_eq!(
        read(&mut out)["result"],
        json!([{"range":{"start":{"line":0,"character":13},"end":{"line":0,"character":20}},
            "newText":"∀"}])
    );

    let text = "theorem t(): \\ex";
    send(json!({"jsonrpc":"2.0","method":"textDocument/didChange",
        "params":{"textDocument":{"uri":uri},"contentChanges":[{"text":text}]}}));
    let _ = read(&mut out);
    send(
        json!({"jsonrpc":"2.0","id":3,"method":"textDocument/completion",
        "params":{"textDocument":{"uri":uri},"position":{"line":0,"character":16}}}),
    );
    let items = read(&mut out)["result"].clone();
    assert_eq!(items[0]["label"], "\\exists");
    assert_eq!(items[0]["textEdit"]["newText"], "∃");

    send(json!({"jsonrpc":"2.0","id":4,"method":"shutdown"}));
    let _ = read(&mut out);
    send(json!({"jsonrpc":"2.0","method":"exit"}));
    drop(input);
    assert!(child.wait().unwrap().success());
}
