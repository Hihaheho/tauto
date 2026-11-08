//! `lsp-bench SERVER [ARGS…] -- SCENARIO FILE…`: runs the language server
//! `SERVER ARGS…` on its standard input and output and reports, one line per
//! measure, how long its answers took and how much memory it held.
//!
//! Scenarios:
//!
//! - `open`: each file is opened in a fresh server; reports the time to its
//!   diagnostics and to its semantic tokens, and the memory after. With
//!   `LSP_BENCH_DUMP=1` it prints the diagnostics too.
//! - `edit`: the first file is opened, then edited `LSP_BENCH_EDITS` times
//!   (20 by default) by adding a line break at its end; reports the median
//!   and the slowest time from an edit to its diagnostics and tokens. With
//!   `LSP_BENCH_EDIT_AT=middle` the line break goes before the first
//!   statement from the middle line on instead, so every statement after it
//!   moves.
//! - `session`: one server opens every file in turn, asks for its tokens and
//!   closes it; reports the peak memory and the memory at the end.
//!
//! Memory is the server's resident set (`VmRSS`, `VmHWM` of
//! `/proc/PID/status`), so this runs on Linux.

use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::{Value, json};

struct Server {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    next_id: i64,
}

impl Server {
    fn start(cmd: &[String]) -> Server {
        let mut child = Command::new(&cmd[0])
            .args(&cmd[1..])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap_or_else(|e| panic!("{}: {e}", cmd[0]));
        let input = child.stdin.take().unwrap();
        let output = BufReader::new(child.stdout.take().unwrap());
        let mut s = Server {
            child,
            input,
            output,
            next_id: 1,
        };
        let root = std::env::current_dir().unwrap();
        s.request("initialize", json!({"rootUri": uri(&root), "capabilities": {}}));
        s.notify("initialized", json!({}));
        s
    }

    fn send(&mut self, v: &Value) {
        let body = v.to_string();
        write!(self.input, "Content-Length: {}\r\n\r\n{body}", body.len()).unwrap();
        self.input.flush().unwrap();
    }

    fn read(&mut self) -> Value {
        let mut len = 0;
        loop {
            let mut line = String::new();
            if self.output.read_line(&mut line).unwrap() == 0 {
                panic!("the server ended");
            }
            let line = line.trim_end();
            if line.is_empty() {
                break;
            }
            if let Some(n) = line.strip_prefix("Content-Length:") {
                len = n.trim().parse().unwrap();
            }
        }
        let mut body = vec![0; len];
        self.output.read_exact(&mut body).unwrap();
        serde_json::from_slice(&body).unwrap()
    }

    fn notify(&mut self, method: &str, params: Value) {
        self.send(&json!({"jsonrpc": "2.0", "method": method, "params": params}));
    }

    /// Sends a request and waits for its answer, skipping notifications.
    fn request(&mut self, method: &str, params: Value) -> Value {
        let id = self.next_id;
        self.next_id += 1;
        self.send(&json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}));
        loop {
            let m = self.read();
            if m["id"] == json!(id) {
                return m;
            }
        }
    }

    /// Waits for the diagnostics of `uri`, and gives them.
    fn diagnostics(&mut self, uri: &str) -> Value {
        loop {
            let m = self.read();
            if m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == uri {
                return m["params"]["diagnostics"].clone();
            }
        }
    }

    fn tokens(&mut self, uri: &str) {
        self.request(
            "textDocument/semanticTokens/full",
            json!({"textDocument": {"uri": uri}}),
        );
    }

    /// The resident set now and at its peak, in KiB.
    fn memory(&self) -> (u64, u64) {
        let status =
            std::fs::read_to_string(format!("/proc/{}/status", self.child.id())).unwrap_or_default();
        let field = |name: &str| {
            status
                .lines()
                .find_map(|l| l.strip_prefix(name))
                .and_then(|r| r.split_whitespace().next()?.parse().ok())
                .unwrap_or(0)
        };
        (field("VmRSS:"), field("VmHWM:"))
    }

    fn stop(mut self) {
        self.request("shutdown", Value::Null);
        self.notify("exit", Value::Null);
        let _ = self.child.wait();
    }
}

fn uri(p: &Path) -> String {
    format!("file://{}", p.display())
}

fn ms(d: Duration) -> String {
    format!("{:.1}", d.as_secs_f64() * 1000.0)
}

fn open(s: &mut Server, path: &Path, version: i64) -> (String, String) {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let u = uri(&path.canonicalize().unwrap());
    s.notify(
        "textDocument/didOpen",
        json!({"textDocument": {"uri": u, "languageId": "tauto", "version": version, "text": text}}),
    );
    (u, text)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let split = args.iter().position(|a| a == "--").expect("SERVER [ARGS…] -- SCENARIO FILE…");
    let server = &args[..split];
    let scenario = args.get(split + 1).expect("a scenario: open, edit or session");
    let files: Vec<PathBuf> = args[split + 2..].iter().map(PathBuf::from).collect();
    match scenario.as_str() {
        "open" => {
            for f in &files {
                let mut s = Server::start(server);
                let t = Instant::now();
                let (u, _) = open(&mut s, f, 1);
                let found = s.diagnostics(&u);
                let diag = t.elapsed();
                // With `LSP_BENCH_DUMP=1`, the diagnostics, to compare two runs.
                if std::env::var("LSP_BENCH_DUMP").is_ok_and(|v| v == "1") {
                    println!("diagnostics {} {found}", f.display());
                }
                s.tokens(&u);
                let tokens = t.elapsed();
                let (rss, hwm) = s.memory();
                println!(
                    "open {} diagnostics_ms={} tokens_ms={} rss_kib={rss} peak_kib={hwm}",
                    f.display(),
                    ms(diag),
                    ms(tokens)
                );
                s.stop();
            }
        }
        "edit" => {
            let edits: usize = std::env::var("LSP_BENCH_EDITS")
                .ok()
                .and_then(|n| n.parse().ok())
                .unwrap_or(20);
            let middle = std::env::var("LSP_BENCH_EDIT_AT").is_ok_and(|a| a == "middle");
            let f = files.first().expect("a file");
            let mut s = Server::start(server);
            let (u, mut text) = open(&mut s, f, 1);
            s.diagnostics(&u);
            let mut times = Vec::new();
            for v in 0..edits {
                if middle {
                    // A line break before the first statement from the middle line on: the
                    // statements after it move, and none of them changes.
                    let lines = text.matches('\n').count();
                    let at = text
                        .match_indices('\n')
                        .skip(lines / 2)
                        .map(|(i, _)| i + 1)
                        .find(|&i| {
                            text[i..]
                                .chars()
                                .next()
                                .is_some_and(|c| c.is_alphabetic() || c == '@')
                        })
                        .unwrap_or(text.len());
                    text.insert(at, '\n');
                } else {
                    text.push('\n');
                }
                let t = Instant::now();
                s.notify(
                    "textDocument/didChange",
                    json!({"textDocument": {"uri": u, "version": v + 2}, "contentChanges": [{"text": text}]}),
                );
                s.diagnostics(&u);
                s.tokens(&u);
                times.push(t.elapsed());
            }
            times.sort();
            let (rss, hwm) = s.memory();
            println!(
                "edit {} at={} edits={edits} median_ms={} max_ms={} rss_kib={rss} peak_kib={hwm}",
                f.display(),
                if middle { "middle" } else { "end" },
                ms(times[times.len() / 2]),
                ms(*times.last().unwrap())
            );
            // With `LSP_BENCH_VERIFY=1`, the diagnostics after the edits are compared with
            // those of a server that opens the edited text afresh.
            let verify = std::env::var("LSP_BENCH_VERIFY").is_ok_and(|v| v == "1");
            if verify {
                let v = edits as i64 + 2;
                s.notify(
                    "textDocument/didChange",
                    json!({"textDocument": {"uri": u, "version": v}, "contentChanges": [{"text": text}]}),
                );
                let kept = s.diagnostics(&u);
                s.stop();
                let mut fresh = Server::start(server);
                fresh.notify(
                    "textDocument/didOpen",
                    json!({"textDocument": {"uri": u, "languageId": "tauto", "version": v, "text": text}}),
                );
                let afresh = fresh.diagnostics(&u);
                fresh.stop();
                if kept == afresh {
                    println!("verify same diagnostics={}", kept.as_array().map_or(0, Vec::len));
                } else {
                    println!("verify DIFFERENT\nkept={kept}\nafresh={afresh}");
                }
            } else {
                s.stop();
            }
        }
        "session" => {
            let mut s = Server::start(server);
            let t = Instant::now();
            for f in &files {
                let (u, _) = open(&mut s, f, 1);
                s.diagnostics(&u);
                s.tokens(&u);
                s.notify("textDocument/didClose", json!({"textDocument": {"uri": u}}));
                s.diagnostics(&u);
            }
            let (rss, hwm) = s.memory();
            println!(
                "session files={} total_ms={} rss_kib={rss} peak_kib={hwm}",
                files.len(),
                ms(t.elapsed())
            );
            s.stop();
        }
        other => panic!("unknown scenario {other}"),
    }
}
