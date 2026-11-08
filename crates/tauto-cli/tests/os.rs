//! The standard effects (`std/prelude/Os.taut`, `docs/design/host-effects.md`).

use std::fs;

use tauto::eval::{RunError, RunOptions, run_program_with};
use tauto::surface::parse_program;

fn run(source: &str, args: &[&str]) -> Result<tauto::eval::Outcome, RunError> {
    run_with(source, args, &["--allow-read", "--allow-write"])
}

fn run_with(source: &str, args: &[&str], flags: &[&str]) -> Result<tauto::eval::Outcome, RunError> {
    let program = parse_program(source).unwrap();
    let flags: Vec<String> = flags.iter().map(|f| f.to_string()).collect();
    let options = RunOptions {
        args: args.iter().map(|a| a.to_string()).collect(),
        permissions: tauto::eval::Permissions::from_args(&flags).unwrap().0,
        ..RunOptions::default()
    };
    run_program_with(&program, 1_000_000, options)
}

fn shown(source: &str) -> Vec<String> {
    run(source, &[])
        .unwrap()
        .outputs
        .into_iter()
        .map(|(n, v)| format!("{n} = {v}"))
        .collect()
}

fn temp(name: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("tauto-os-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    d
}

#[test]
fn read_file() {
    let d = temp("read");
    fs::write(d.join("f.txt"), "hello").unwrap();
    let src = format!(
        r#"perform show("r", read_file("{}"))"#,
        d.join("f.txt").display().to_string()
    );
    assert_eq!(shown(&src), ["r = Ok(\"hello\")"]);
}

#[test]
fn read_missing() {
    let d = temp("missing");
    let src = format!(
        r#"perform show("r", read_file("{}"))"#,
        d.join("none").display().to_string()
    );
    let got = shown(&src);
    assert!(got[0].starts_with("r = Err("), "{got:?}");
}

#[test]
fn write_then_read() {
    let d = temp("write");
    let path = d.join("f.txt");
    let src = format!(
        r#"let w := write_file("{}", "abc")
perform show("w", w)
perform show("r", read_file("{}"))"#,
        path.display().to_string(),
        path.display().to_string()
    );
    assert_eq!(shown(&src), ["w = Ok(())", "r = Ok(\"abc\")"]);
    assert_eq!(fs::read_to_string(path).unwrap(), "abc");
}

#[test]
fn the_cli_prints_and_exits() {
    let d = temp("cli");
    fs::write(
        d.join("main.nib"),
        r#"import std::prelude::Os

print("out")
eprint("err")
perform exit(3)"#,
    )
    .unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["run", d.join("main.nib").to_str().unwrap(), "--", "x"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(3));
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "out");
    assert_eq!(String::from_utf8(out.stderr).unwrap(), "err");
}

#[test]
fn a_backend_flag_after_the_separator_goes_to_the_program() {
    let d = temp("cli-backend-arg");
    fs::write(
        d.join("main.nib"),
        r#"import std::prelude::Os

print("out")
eprint("err")
perform exit(3)"#,
    )
    .unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args([
            "run",
            d.join("main.nib").to_str().unwrap(),
            "--",
            "--backend",
            "rust",
        ])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(3));
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "out");
    assert_eq!(String::from_utf8(out.stderr).unwrap(), "err");
}

#[test]
fn a_permission_not_given_stops_the_run_before_it_starts() {
    let src = r#"print("started")
perform show("r", read_file("/x"))"#;
    let err = run_with(src, &[], &[]).unwrap_err();
    assert_eq!(
        err.to_string(),
        "the program needs --allow-read to run; the host denies it by default"
    );
}

#[test]
fn a_handled_effect_needs_no_permission() {
    let src = r#"let r := handle { read_file("/x") } with { fs_read(p), k => k(Ok(p)) }
perform show("r", r)"#;
    assert_eq!(
        run_with(src, &[], &[]).unwrap().outputs,
        [("r".to_string(), "Ok(\"/x\")".to_string())]
    );
}

#[test]
fn a_request_outside_the_permission_is_denied() {
    let d = temp("scoped");
    let src = format!(
        r#"perform show("r", perform fs_read("{}"))"#,
        d.join("../elsewhere.txt").display().to_string()
    );
    let flag = format!("--allow-read={}", d.display());
    let shown = run_with(&src, &[], &[&flag]).unwrap().outputs;
    assert!(shown[0].1.starts_with("Err(Denied("), "{shown:?}");
    let src = r#"perform show("e", perform env("PATH"))
perform show("n", http_get("https://b.example/"))"#;
    let shown = run_with(src, &[], &["--allow-env=HOME", "--allow-net=a.example"])
        .unwrap()
        .outputs;
    assert!(shown[0].1.starts_with("Err(Denied("), "{shown:?}");
    assert!(shown[1].1.starts_with("Err(Denied("), "{shown:?}");
}

#[test]
fn the_cli_takes_permission_flags() {
    let d = temp("flags");
    fs::write(d.join("f.txt"), "hi").unwrap();
    fs::write(
        d.join("main.nib"),
        format!(
            r#"import std::prelude::Os

match read_file("{}") {{
  Ok(t) => print(t)
  Err(e) => eprint(e)
}}"#,
            d.join("f.txt").display().to_string()
        ),
    )
    .unwrap();
    let main = d.join("main.nib");
    let denied = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["run", main.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(!denied.status.success());
    assert!(
        String::from_utf8(denied.stderr)
            .unwrap()
            .contains("--allow-read")
    );
    let allowed = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args([
            "run",
            &format!("--allow-read={}", d.display()),
            main.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_eq!(String::from_utf8(allowed.stdout).unwrap(), "hi");
}

/// A task waits to read a stream no one writes to, with no deadline;
/// shutting the stream down from the main task wakes it at the end of the
/// stream. Built with the Rust backend, where the read blocks a thread of the
/// reactor's pool for blocking work while the tasks go on.
#[test]
fn a_shutdown_from_another_task_wakes_a_read_in_the_rust_backend() {
    let d = std::env::temp_dir().join(format!("tauto-os-tcp-rust-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    fs::write(
        d.join("main.taut"),
        r#"import std::prelude::Os
import std::prelude::Par
import std::prelude::Shared

fn read_woken(s: TcpStream): Result(Bytes, IoError) ! {∀ T. spawn(T), sleep, tcp_read, tcp_shutdown, wait} {
  let forever: Option(i64) := None
  let t := perform spawn(() => perform tcp_read(s, 8, forever))
  perform sleep(50)
  match perform tcp_shutdown(s, ShutdownRead) {
    Ok(u) => Task::join(t)
    Err(e) => {
      let r := Task::join(t)
      Err(e)
    }
  }
}
let forever: Option(i64) := None
match perform tcp_listen("127.0.0.1:0") {
  Ok(l) => match perform tcp_connect(l.address, forever) {
    Ok(c) => match perform tcp_accept(l, forever) {
      Ok(s) => {
        perform show("read", read_woken(s))
        perform tcp_close(c)
      }
      Err(e) => perform show("accept", io_message(e))
    }
    Err(e) => perform show("connect", io_message(e))
  }
  Err(e) => perform show("listen", io_message(e))
}
"#,
    )
    .unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["build", "--backend", "rust", "main.taut"])
        .current_dir(&d)
        .env("TAUTO_TARGET_DIR", d.join("target"))
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let exe = String::from_utf8(out.stdout).unwrap().trim().to_string();
    let run = std::process::Command::new(&exe)
        .args(["--allow-net=127.0.0.1", "--"])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "{stdout}{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(stdout.contains("read = Ok(Bytes[])"), "{stdout}");
    let _ = fs::remove_dir_all(&d);
}

/// A large file read with `fs_read_bytes` is one `Bytes`, not a list of
/// its bytes: reading 16 MB neither overflows the stack (as a `List(u8)`
/// of that length did when it was dropped) nor takes a cell per byte.
#[test]
fn a_large_file_is_read_as_bytes() {
    let d = temp("large-bytes");
    let mut data = vec![0u8; 16_000_000];
    data[15_999_999] = 7;
    fs::write(d.join("big.bin"), &data).unwrap();
    let main = d.join("main.taut");
    fs::write(
        &main,
        "import std::prelude::Os\nimport std::prelude::Shared\n\nmatch perform fs_read_bytes(\"big.bin\") {\n  Ok(b) => print(Text::of_u64(Bytes::len(b)))\n  Err(e) => print(io_message(e))\n}\n",
    )
    .unwrap();
    for backend in [
        &["--backend", "eval"][..],
        &["--backend", "rust"][..],
        &["--backend", "vm"][..],
    ] {
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("run")
            .args(backend)
            .args(["--allow-read", main.file_name().unwrap().to_str().unwrap()])
            .current_dir(&d)
            .output()
            .unwrap();
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            "16000000",
            "{backend:?}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

#[test]
fn net_addr_connects_to_the_address_it_names() {
    use std::io::{Read, Write};
    let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    let server = std::thread::spawn(move || {
        let (mut s, _) = listener.accept().unwrap();
        let mut seen = Vec::new();
        let mut buf = [0; 1024];
        while !seen.windows(4).any(|w| w == b"\r\n\r\n") {
            let n = s.read(&mut buf).unwrap();
            seen.extend_from_slice(&buf[..n]);
        }
        s.write_all(b"HTTP/1.1 200 OK\r\ncontent-length: 2\r\nconnection: close\r\n\r\nok")
            .unwrap();
        String::from_utf8_lossy(&seen).to_ascii_lowercase()
    });
    let src = format!(
        r#"import std::prelude::Os
import std::prelude::Shared

let r := Request {{ method: "GET", url: "http://pinned.invalid:{port}/", headers: Nil, body: Bytes::of_list(Nil) }}
match perform net_addr(r, "127.0.0.1") {{
  Ok(response) => perform show("body", Text::of_bytes(response.body))
  Err(e) => perform show("body", io_message(e))
}}
"#
    );
    let shown = run_with(&src, &[], &["--allow-net"]).unwrap().outputs;
    assert_eq!(shown, [("body".to_string(), "Some(\"ok\")".to_string())]);
    let request = server.join().unwrap();
    assert!(
        request.contains(&format!("host: pinned.invalid:{port}")),
        "{request}"
    );
}

/// The test certificates of the host's TLS, made by the run-time library's
/// TLS tests.
#[path = "../../tauto-rt/tests/tls/certs.rs"]
mod tls_certs;

fn tls_dir() -> String {
    tls_certs::dir().display().to_string()
}

fn tls_pem(name: &str) -> Vec<u8> {
    tls_certs::read(name)
}

fn tls_client_source(port: u16, roots: &str, name: &str) -> String {
    r#"import std::prelude::Os
import std::prelude::Secret
import std::prelude::Shared

fn talk(address: Text, client: TlsClient): Result(Pair(Bytes, Option(Text)), IoError) ! {tcp_connect, tls_connect, tls_read, tls_write, tls_close} {
  let forever: Option(i64) := None
  match perform tcp_connect(address, forever) {
    Ok(s) => match perform tls_connect(s, client, forever) {
      Ok(t) => match perform tls_write(t, Bytes::of_list([104, 105]), forever) {
        Ok(u) => {
          let got := perform tls_read(t, 64, forever)
          perform tls_close(t)
          match got {
            Ok(b) => Ok(Pair { fst: b, snd: t.alpn })
            Err(e) => Err(e)
          }
        }
        Err(e) => Err(e)
      }
      Err(e) => Err(e)
    }
    Err(e) => Err(e)
  }
}
match perform fs_read_bytes("{dir}/{roots}") {
  Ok(ca) => {
    let client := TlsClient { server_name: "{name}", roots: OnlyRoots(ca), client_cert: None, alpn: ["http/1.1"] }
    match talk("127.0.0.1:{port}", client) {
      Ok(p) => {
        perform show("reply", p.fst)
        perform show("alpn", p.snd)
      }
      Err(e) => perform show("error", io_message(e))
    }
  }
  Err(e) => perform show("roots", io_message(e))
}
"#
        .replace("{dir}", &tls_dir())
        .replace("{roots}", roots)
        .replace("{name}", name)
        .replace("{port}", &port.to_string())
}

/// A rustls server on a thread that echoes what one client sends.
fn tls_echo_server() -> (u16, std::thread::JoinHandle<()>) {
    use tauto_rt::tls::{self, ServerCert, ServerOptions};
    let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    let config = tls::server_config(&ServerOptions {
        certs: vec![ServerCert {
            names: vec![],
            chain_pem: tls_pem("a.pem"),
            key_pem: tls_pem("a.key"),
        }],
        alpn: vec![b"http/1.1".to_vec()],
        client_roots: None,
    })
    .unwrap();
    let server = std::thread::spawn(move || {
        let (sock, _) = listener.accept().unwrap();
        // A client that refuses the certificate ends the handshake here.
        if let Ok(mut t) = tls::accept(config, sock) {
            let got = t.read(64).unwrap();
            t.write(&got).unwrap();
            let _ = t.close();
        }
    });
    (port, server)
}

fn tls_outputs(source: &str, flags: &[&str]) -> Vec<String> {
    run_with(source, &[], flags)
        .unwrap()
        .outputs
        .into_iter()
        .map(|(n, v)| format!("{n} = {v}"))
        .collect()
}

/// The program connects, verifies the server against the CA it read,
/// writes and reads back through TLS, and sees the protocol ALPN chose.
#[test]
fn a_program_speaks_tls_to_a_server() {
    let (port, server) = tls_echo_server();
    let source = tls_client_source(port, "ca.pem", "a.test");
    let shown = tls_outputs(&source, &["--allow-read", "--allow-net=127.0.0.1"]);
    server.join().unwrap();
    assert_eq!(shown.len(), 2, "{shown:?}");
    assert!(
        shown[0].starts_with("reply = ") && shown[0].contains("104") && shown[0].contains("105"),
        "{shown:?}"
    );
    assert_eq!(shown[1], "alpn = Some(\"http/1.1\")", "{shown:?}");
}

/// A server whose certificate the roots do not sign is refused, and the
/// program sees why as an `IoError`.
#[test]
fn a_program_refuses_a_server_its_roots_do_not_sign() {
    let (port, server) = tls_echo_server();
    let source = tls_client_source(port, "other.pem", "a.test");
    let shown = tls_outputs(&source, &["--allow-read", "--allow-net=127.0.0.1"]);
    server.join().unwrap();
    assert!(
        shown.len() == 1
            && shown[0].starts_with("error = ")
            && shown[0].contains("invalid peer certificate"),
        "{shown:?}"
    );
}

/// The program answers a TLS client on a port it listens on, and sees the
/// SNI name the client sent.
#[test]
fn a_program_answers_a_tls_client() {
    use tauto_rt::tls::{self, ClientOptions, Roots};
    let port = {
        let l = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        l.local_addr().unwrap().port()
    };
    let source = r#"import std::prelude::Os
import std::prelude::Secret
import std::prelude::Shared

fn serve(l: TcpListener, server: TlsServer): Result(Pair(Bytes, Option(Text)), IoError) ! {tcp_accept, tls_accept, tls_read, tls_write, tls_shutdown, tls_close} {
  let forever: Option(i64) := None
  match perform tcp_accept(l, forever) {
    Ok(s) => match perform tls_accept(s, server, forever) {
      Ok(t) => match perform tls_read(t, 64, forever) {
        Ok(got) => {
          let w := perform tls_write(t, got, forever)
          let shut := perform tls_shutdown(t, ShutdownWrite)
          perform tls_close(t)
          match w {
            Ok(u) => Ok(Pair { fst: got, snd: t.server_name })
            Err(e) => Err(e)
          }
        }
        Err(e) => Err(e)
      }
      Err(e) => Err(e)
    }
    Err(e) => Err(e)
  }
}
match perform fs_read_bytes("{dir}/a.pem") {
  Ok(chain) => match perform fs_read_bytes("{dir}/a.key") {
    Ok(key) => {
      let server := TlsServer { certs: [TlsCert { names: [], chain: chain, key: secret(key) }], alpn: ["http/1.1"], client_roots: None }
      match perform tcp_listen("127.0.0.1:{port}") {
        Ok(l) => match serve(l, server) {
          Ok(p) => {
            perform show("got", p.fst)
            perform show("sni", p.snd)
          }
          Err(e) => perform show("error", io_message(e))
        }
        Err(e) => perform show("listen", io_message(e))
      }
    }
    Err(e) => perform show("key", io_message(e))
  }
  Err(e) => perform show("chain", io_message(e))
}
"#
        .replace("{dir}", &tls_dir())
        .replace("{port}", &port.to_string());
    let config = tls::client_config(&ClientOptions {
        roots: Roots::Only(tls_pem("ca.pem")),
        client_cert: None,
        alpn: vec![b"http/1.1".to_vec()],
    })
    .unwrap();
    let client = std::thread::spawn(move || {
        // The program listens once it has read its certificate.
        let sock = loop {
            match std::net::TcpStream::connect(("127.0.0.1", port)) {
                Ok(s) => break s,
                Err(_) => std::thread::sleep(std::time::Duration::from_millis(20)),
            }
        };
        let mut t = tls::connect(config, "localhost", sock).unwrap();
        t.write(b"hi").unwrap();
        let back = t.read(64).unwrap();
        assert!(
            t.read(64).unwrap().is_empty(),
            "the server sends close_notify"
        );
        back
    });
    let shown = tls_outputs(&source, &["--allow-read", "--allow-net=127.0.0.1"]);
    assert_eq!(client.join().unwrap(), b"hi");
    assert_eq!(shown.len(), 2, "{shown:?}");
    assert!(
        shown[0].starts_with("got = ") && shown[0].contains("104"),
        "{shown:?}"
    );
    assert_eq!(shown[1], "sni = Some(\"localhost\")", "{shown:?}");
}

/// The Rust backend answers TLS too: its crate turns on the `tls` feature of
/// the run-time library for a program that uses the network.
#[test]
fn a_program_built_with_the_rust_backend_speaks_tls() {
    let d = std::env::temp_dir().join(format!("tauto-os-tls-rust-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    let (port, server) = tls_echo_server();
    fs::write(
        d.join("main.taut"),
        tls_client_source(port, "ca.pem", "a.test"),
    )
    .unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["build", "--backend", "rust", "main.taut"])
        .current_dir(&d)
        .env("TAUTO_TARGET_DIR", d.join("target"))
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let exe = String::from_utf8(out.stdout).unwrap().trim().to_string();
    let run = std::process::Command::new(&exe)
        .args(["--allow-read", "--allow-net=127.0.0.1", "--"])
        .output()
        .unwrap();
    server.join().unwrap();
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "{stdout}{}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(stdout.contains("alpn = Some(\"http/1.1\")"), "{stdout}");
    let _ = fs::remove_dir_all(&d);
}

/// The machine of `--backend vm` answers the stream and started-program
/// requests: an accept waits in a task while the main task connects and
/// writes, a read waiting in a task wakes when another shuts the stream
/// down, and a started program is written to, waited for and read.
#[test]
fn the_vm_answers_streams_and_started_programs() {
    let d = temp("vm-streams");
    let main = d.join("main.taut");
    fs::write(&main, include_str!("vm_streams.taut")).unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["run", "--backend", "vm", "--allow-net=127.0.0.1", "--allow-run=sh", "main.taut"])
        .current_dir(&d)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{stdout}{}", String::from_utf8_lossy(&out.stderr));
    for line in [
        "write = Ok(())",
        "served = Ok(Bytes[104, 101, 108, 108, 111])",
        "read = Ok(Bytes[])",
        "wait = Ok(Some(0))",
    ] {
        assert!(stdout.contains(line), "{line}: {stdout}");
    }
    let _ = fs::remove_dir_all(&d);
}
