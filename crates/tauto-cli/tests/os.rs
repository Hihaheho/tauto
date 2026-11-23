//! The standard effects (`std/builtin/os.taut`, `docs/design/host-effects.md`).

use std::fs;

use tauto::exec::{RunError, RunOptions, run_source_with};

fn run(source: &str, args: &[&str]) -> Result<tauto::exec::Outcome, RunError> {
    run_with(source, args, &["--allow-read", "--allow-write"])
}

fn run_with(source: &str, args: &[&str], flags: &[&str]) -> Result<tauto::exec::Outcome, RunError> {
    let flags: Vec<String> = flags.iter().map(|f| f.to_string()).collect();
    let options = RunOptions {
        args: args.iter().map(|a| a.to_string()).collect(),
        permissions: tauto::exec::Permissions::from_args(&flags).unwrap().0,
        ..RunOptions::default()
    };
    // A program is read as `tauto run` reads a file: what it uses of the
    // standard effects it imports.
    let source = if source.contains("import std::builtin::os") {
        source.to_string()
    } else {
        format!("import std::builtin::os\n{source}")
    };
    run_source_with(&source, 1_000_000, options)
}

/// What the program writes with `show`, a line each.
fn shown(source: &str) -> Vec<String> {
    run(source, &[])
        .unwrap()
        .stdout
        .lines()
        .map(str::to_string)
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
        r#"show(&read_file("{}"))"#,
        d.join("f.txt").display().to_string()
    );
    assert_eq!(shown(&src), ["Ok(\"hello\")"]);
}

#[test]
fn read_missing() {
    let d = temp("missing");
    let src = format!(
        r#"show(&read_file("{}"))"#,
        d.join("none").display().to_string()
    );
    let got = shown(&src);
    assert!(got[0].starts_with("Err("), "{got:?}");
}

#[test]
fn write_then_read() {
    let d = temp("write");
    let path = d.join("f.txt");
    let src = format!(
        r#"let w := write_file("{}", "abc")
show(&w)
show(&read_file("{}"))"#,
        path.display().to_string(),
        path.display().to_string()
    );
    assert_eq!(shown(&src), ["Ok(())", "Ok(\"abc\")"]);
    assert_eq!(fs::read_to_string(path).unwrap(), "abc");
}

#[test]
fn the_cli_prints_and_exits() {
    let d = temp("cli");
    fs::write(
        d.join("main.nib"),
        r#"import std::builtin::os

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
        r#"import std::builtin::os

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
show(&read_file("/x"))"#;
    let err = run_with(src, &[], &[]).unwrap_err();
    assert_eq!(
        err.to_string(),
        "the program needs --allow-read to run; the host denies it by default"
    );
}

#[test]
fn a_handled_effect_needs_no_permission() {
    let src = r#"let r := handle { read_file("/x") } with { fs_read(p), k => k(Ok(p)) }
show(&r)"#;
    assert_eq!(
        run_with(src, &[], &[]).unwrap().outputs,
        [("r".to_string(), "Ok(\"/x\")".to_string())]
    );
}

#[test]
fn a_request_outside_the_permission_is_denied() {
    let d = temp("scoped");
    let src = format!(
        r#"show(&(perform fs_read("{}")))"#,
        d.join("../elsewhere.txt").display().to_string()
    );
    let flag = format!("--allow-read={}", d.display());
    let shown = run_with(&src, &[], &[&flag]).unwrap().outputs;
    assert!(shown[0].1.starts_with("Err(Denied("), "{shown:?}");
    let src = r#"show(&(perform env("PATH")))
show(&http_get("https://b.example/"))"#;
    let shown = run_with(src, &[], &["--allow-env=HOME", "--allow-net=a.example"])
        .unwrap()
        .outputs;
    assert!(shown[0].1.starts_with("Err(Denied("), "{shown:?}");
    assert!(shown[1].1.starts_with("Err(Denied("), "{shown:?}");
}

/// `tauto run` asks at the start for what the program's effects need; with
/// no terminal to ask at it does not start, and `--yes` allows it.
#[test]
fn the_cli_asks_for_what_the_effects_need() {
    let d = temp("flags");
    fs::write(d.join("f.txt"), "hi").unwrap();
    fs::write(
        d.join("main.nib"),
        format!(
            r#"import std::builtin::os

match read_file("{}") {{
  Ok(t) => print(t)
  Err(e) => eprint(e)
}}"#,
            d.join("f.txt").display().to_string()
        ),
    )
    .unwrap();
    let main = d.join("main.nib");
    let tauto = |args: &[&str]| {
        let mut c = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"));
        c.arg("run")
            .args(args)
            .arg(&main)
            .env("TAUTO_HOME", d.join("home"))
            .env("TAUTO_LANG", "en");
        // A session of its own: no terminal to ask at.
        #[cfg(unix)]
        unsafe {
            use std::os::unix::process::CommandExt;
            c.pre_exec(|| {
                libc::setsid();
                Ok(())
            });
        }
        c.output().unwrap()
    };
    let denied = tauto(&[]);
    assert!(!denied.status.success());
    let stderr = String::from_utf8(denied.stderr).unwrap();
    assert!(stderr.contains("+ read: read files"), "{stderr}");
    assert!(stderr.contains("--yes"), "{stderr}");
    let allowed = tauto(&["--yes"]);
    assert_eq!(String::from_utf8(allowed.stdout).unwrap(), "hi");
}

/// A task waits to read a stream no one writes to, with no deadline;
/// shutting the stream down from the main task wakes it at the end of the
/// stream. Built with the Rust backend, where the read waits on the reactor's
/// poller while the tasks go on.
#[test]
fn a_shutdown_from_another_task_wakes_a_read_in_the_rust_backend() {
    let d = std::env::temp_dir().join(format!("tauto-os-tcp-rust-{}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    fs::create_dir_all(&d).unwrap();
    fs::write(
        d.join("main.taut"),
        r#"import std::builtin::os
import std::builtin::par
import std::prelude::collections

fn read_woken(s: TcpStream): Result(Bytes, IoError) ! {∀ T. spawn(() -> T ! {tcp_read, wait, mutex_claim, mutex_take_claimed}), sleep, tcp_read, tcp_shutdown, tcp_close, wait, mutex_new} {
  let forever: Option(i64) := None
  let stop := TcpStream::stopper(&s)
  // A task takes the stream through a cell, since what `spawn` runs is shared.
  let cell := perform mutex_new(s)
  let t := perform spawn(() => perform tcp_read(Mutex::take(cell), 8, forever))
  perform sleep(50)
  let shut := perform tcp_shutdown(stop, ShutdownRead)
  match Task::join(t) {
    TcpRead { stream, got } => {
      perform tcp_close(stream)
      match shut {
        Ok(u) => got
        Err(e) => Err(e)
      }
    }
  }
}
let forever: Option(i64) := None
match perform tcp_listen("127.0.0.1:0") {
  Ok(l) => match perform tcp_connect(TcpListener::address(&l), forever) {
    Ok(c) => match perform tcp_accept(l, forever) {
      TcpAccepted { listener, got } => {
        match got {
          Ok(s) => show(&read_woken(s))
          Err(e) => show(&io_message(e))
        }
        perform tcp_unlisten(TcpListener::stopper(&listener))
        perform tcp_close(c)
      }
    }
    Err(e) => show(&io_message(e))
  }
  Err(e) => show(&io_message(e))
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
    assert!(stdout.contains("Ok(Bytes[])"), "{stdout}");
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
        "import std::builtin::os\nimport std::prelude::collections\n\nmatch perform fs_read_bytes(\"big.bin\") {\n  Ok(b) => print(Text::of_u64(Bytes::len(b)))\n  Err(e) => print(io_message(e))\n}\n",
    )
    .unwrap();
    for backend in [
        &["--backend", "rust"][..],
        &["--backend", "vm"][..],
    ] {
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("run")
            .args(backend)
            .args(["--yes", main.file_name().unwrap().to_str().unwrap()])
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
        r#"import std::builtin::os
import std::prelude::collections

let r := Request {{ method: "GET", url: "http://pinned.invalid:{port}/", headers: Nil, body: Bytes::of_list(Nil) }}
match perform net_addr(r, "127.0.0.1") {{
  Ok(response) => show(&Text::of_bytes(response.body))
  Err(e) => show(&io_message(e))
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

/// A server of one exchange for `net_open`: it reads the chunked request body,
/// answers its length in a header, then sends `one`, waits, and sends `two`.
fn serve_pieces(listener: std::net::TcpListener) -> std::thread::JoinHandle<Vec<u8>> {
    use std::io::{BufRead, BufReader, Read, Write};
    std::thread::spawn(move || {
        let (s, _) = listener.accept().unwrap();
        let mut r = BufReader::new(s.try_clone().unwrap());
        let mut line = String::new();
        loop {
            line.clear();
            r.read_line(&mut line).unwrap();
            if line == "\r\n" {
                break;
            }
        }
        let mut body = Vec::new();
        loop {
            line.clear();
            r.read_line(&mut line).unwrap();
            let n = usize::from_str_radix(line.trim(), 16).unwrap();
            let mut chunk = vec![0; n + 2];
            r.read_exact(&mut chunk).unwrap();
            if n == 0 {
                break;
            }
            body.extend_from_slice(&chunk[..n]);
        }
        let mut w = s;
        write!(
            w,
            "HTTP/1.1 200 OK\r\nx-got: {}\r\ntransfer-encoding: chunked\r\n\r\n3\r\none\r\n",
            body.len()
        )
        .unwrap();
        w.flush().unwrap();
        std::thread::sleep(std::time::Duration::from_millis(500));
        write!(w, "3\r\ntwo\r\n0\r\n\r\n").unwrap();
        body
    })
}

fn pieces_source(port: u16) -> String {
    format!(
        r#"import std::builtin::os
import std::prelude::collections

fn header(hs: List(Text × Text)): Text {{
  match hs {{
    Nil => ""
    Cons(h, rest) => match h {{
      #(k, v) => if k == "x-got" {{ v }} else {{ header(rest) }}
    }}
  }}
}}

fn text(r: Result(Bytes, IoError)): Text {{
  match r {{
    Ok(b) => match Text::of_bytes(b) {{
      Some(t) => t
      None => "?"
    }}
    Err(e) => io_message(e)
  }}
}}

let head := RequestHead {{ method: "POST", url: "http://127.0.0.1:{port}/", headers: Nil }}
match perform net_open(head, None) {{
  Ok(req) => match perform net_write(req, Bytes::of_text("hel"), None) {{
    Written {{ body: req2, result }} => match perform net_write(req2, Bytes::of_text("lo"), None) {{
      Written {{ body: req3, result }} => match perform net_finish(req3, None) {{
        Responded(Opened {{ head, body }}) => {{
          show(&header(head.headers))
          match perform net_read(body, 64, None) {{
            Piece {{ body: b2, got }} => {{
              show(&text(got))
              match perform net_read(b2, 64, None) {{
                Piece {{ body: b3, got }} => {{
                  show(&text(got))
                  match perform net_read(b3, 64, None) {{
                    Piece {{ body: b4, got }} => {{
                      show(&text(got))
                      perform net_close(b4)
                    }}
                  }}
                }}
              }}
            }}
          }}
        }}
        Unanswered(r) => perform net_cancel(r)
        NoResponse(e) => show(&io_message(e))
      }}
    }}
  }}
  Err(e) => show(&io_message(e))
}}
"#
    )
}

/// `net_open` sends the request body as it is written and gives the response
/// body as it arrives: the first read takes the first piece, before the
/// server sends the second.
#[test]
fn net_open_gives_the_body_a_piece_at_a_time() {
    let expected = [
        ("got", "\"5\""),
        ("first", "\"one\""),
        ("second", "\"two\""),
        ("end", "\"\""),
    ]
    .map(|(k, v)| (k.to_string(), v.to_string()));
    let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    let server = serve_pieces(listener);
    let shown = run_with(&pieces_source(port), &[], &["--allow-net"])
        .unwrap()
        .outputs;
    assert_eq!(shown, expected);
    assert_eq!(server.join().unwrap(), b"hello");
    for backend in [&["--backend", "vm"][..], &["--backend", "rust"][..]] {
        let d = temp("net-open");
        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        let port = listener.local_addr().unwrap().port();
        let server = serve_pieces(listener);
        fs::write(d.join("main.taut"), pieces_source(port)).unwrap();
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
            .arg("run")
            .args(backend)
            .args(["--yes", "main.taut"])
            .current_dir(&d)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        for (k, v) in &expected {
            assert!(
                stdout.contains(&format!("{k} = {v}")),
                "{backend:?}: {stdout}{}",
                String::from_utf8_lossy(&out.stderr)
            );
        }
        assert_eq!(server.join().unwrap(), b"hello");
        let _ = fs::remove_dir_all(&d);
    }
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
    r#"import std::builtin::os
import std::builtin::secret
import std::prelude::collections

fn talk(address: Text, client: TlsClient): Result(Bytes × Option(Text), IoError) ! {tcp_connect, tls_connect, tls_read, tls_write, tls_close} {
  let forever: Option(i64) := None
  match perform tcp_connect(address, forever) {
    Ok(s) => match perform tls_connect(s, client, forever) {
      Ok(t) => {
        let alpn := TlsStream::alpn(&t)
        match perform tls_write(t, Bytes::of_list([104, 105]), forever) {
          TlsWritten { stream, result } => match result {
            Ok(u) => match perform tls_read(stream, 64, forever) {
              TlsRead { stream: t2, got } => {
                perform tls_close(t2)
                match got {
                  Ok(b) => Ok(#(b, alpn))
                  Err(e) => Err(e)
                }
              }
            }
            Err(e) => {
              perform tls_close(stream)
              Err(e)
            }
          }
        }
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
        show(&p.fst)
        show(&p.snd)
      }
      Err(e) => show(&io_message(e))
    }
  }
  Err(e) => show(&io_message(e))
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
        shown[0].contains("104") && shown[0].contains("105"),
        "{shown:?}"
    );
    assert_eq!(shown[1], "Some(\"http/1.1\")", "{shown:?}");
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
        shown.len() == 1 && shown[0].contains("invalid peer certificate"),
        "{shown:?}"
    );
}

fn tls_server_source(port: u16) -> String {
    r#"import std::builtin::os
import std::builtin::secret
import std::prelude::collections

fn serve(l: TcpListener, server: TlsServer): Result(Bytes × Option(Text), IoError) ! {tcp_accept, tcp_unlisten, tls_accept, tls_read, tls_write, tls_shutdown, tls_close} {
  let forever: Option(i64) := None
  match perform tcp_accept(l, forever) {
    TcpAccepted { listener, got: accepted } => {
      perform tcp_unlisten(TcpListener::stopper(&listener))
      match accepted {
        Ok(s) => match perform tls_accept(s, server, forever) {
          Ok(t) => {
            let name := TlsStream::server_name(&t)
            let stop := TlsStream::stopper(&t)
            match perform tls_read(t, 64, forever) {
              TlsRead { stream, got } => match got {
                Ok(bytes) => match perform tls_write(stream, bytes, forever) {
                  TlsWritten { stream: t2, result } => {
                    let shut := perform tls_shutdown(stop, ShutdownWrite)
                    perform tls_close(t2)
                    match result {
                      Ok(u) => Ok(#(bytes, name))
                      Err(e) => Err(e)
                    }
                  }
                }
                Err(e) => {
                  perform tls_close(stream)
                  Err(e)
                }
              }
            }
          }
          Err(e) => Err(e)
        }
        Err(e) => Err(e)
      }
    }
  }
}
match perform fs_read_bytes("{dir}/a.pem") {
  Ok(chain) => match perform fs_read_bytes("{dir}/a.key") {
    Ok(key) => {
      let server := TlsServer { certs: [TlsCert { names: [], chain: chain, key: secret(key) }], alpn: ["http/1.1"], client_roots: None }
      match perform tcp_listen("127.0.0.1:{port}") {
        Ok(l) => match serve(l, server) {
          Ok(p) => {
            show(&p.fst)
            show(&p.snd)
          }
          Err(e) => show(&io_message(e))
        }
        Err(e) => show(&io_message(e))
      }
    }
    Err(e) => show(&io_message(e))
  }
  Err(e) => show(&io_message(e))
}
"#
        .replace("{dir}", &tls_dir())
        .replace("{port}", &port.to_string())
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
    let source = tls_server_source(port);
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
        shown[0].contains("104"),
        "{shown:?}"
    );
    assert_eq!(shown[1], "Some(\"localhost\")", "{shown:?}");
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
    assert!(stdout.contains("Some(\"http/1.1\")"), "{stdout}");
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
        .args(["run", "--backend", "vm", "--yes", "main.taut"])
        .current_dir(&d)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "{stdout}{}",
        String::from_utf8_lossy(&out.stderr)
    );
    for line in [
        "Ok(())",
        "Ok(Bytes[104, 101, 108, 108, 111])",
        "Ok(Bytes[])",
        "Ok(Some(0))",
    ] {
        assert!(stdout.contains(line), "{line}: {stdout}");
    }
    let _ = fs::remove_dir_all(&d);
}

/// The shown lines of `source` run by `tauto run --backend vm`.
fn vm_tls_outputs(name: &str, source: &str) -> Vec<String> {
    let d = temp(name);
    fs::write(d.join("main.taut"), source).unwrap();
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["run", "--backend", "vm", "--yes", "main.taut"])
        .current_dir(&d)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    assert!(
        out.status.success(),
        "{stdout}{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let _ = fs::remove_dir_all(&d);
    stdout.lines().map(str::to_string).collect()
}

/// The machine of `--backend vm` speaks TLS as a client: it connects,
/// verifies the server, writes, reads and sees the ALPN protocol.
#[test]
fn the_vm_speaks_tls_to_a_server() {
    let (port, server) = tls_echo_server();
    let shown = vm_tls_outputs(
        "vm-tls-client",
        &tls_client_source(port, "ca.pem", "a.test"),
    );
    server.join().unwrap();
    assert_eq!(shown.len(), 2, "{shown:?}");
    assert!(
        shown[0].contains("104") && shown[0].contains("105"),
        "{shown:?}"
    );
    assert_eq!(shown[1], "Some(\"http/1.1\")", "{shown:?}");
}

/// The machine of `--backend vm` answers a TLS client and sees its SNI name.
#[test]
fn the_vm_answers_a_tls_client() {
    use tauto_rt::tls::{self, ClientOptions, Roots};
    let port = {
        let l = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        l.local_addr().unwrap().port()
    };
    let config = tls::client_config(&ClientOptions {
        roots: Roots::Only(tls_pem("ca.pem")),
        client_cert: None,
        alpn: vec![b"http/1.1".to_vec()],
    })
    .unwrap();
    let client = std::thread::spawn(move || {
        let sock = loop {
            match std::net::TcpStream::connect(("127.0.0.1", port)) {
                Ok(s) => break s,
                Err(_) => std::thread::sleep(std::time::Duration::from_millis(20)),
            }
        };
        let mut t = tls::connect(config, "localhost", sock).unwrap();
        t.write(b"hi").unwrap();
        t.read(64).unwrap()
    });
    let shown = vm_tls_outputs("vm-tls-server", &tls_server_source(port));
    assert_eq!(client.join().unwrap(), b"hi");
    assert_eq!(shown.len(), 2, "{shown:?}");
    assert!(
        shown[0].contains("104"),
        "{shown:?}"
    );
    assert_eq!(shown[1], "Some(\"localhost\")", "{shown:?}");
}

/// What a run needs is asked before anything is built: a run that is not
/// allowed (no terminal, no `--yes`) stops before it generates a crate or
/// compiles anything, on the Rust and JavaScript backends alike.
#[test]
fn a_run_that_is_not_allowed_builds_nothing() {
    for backend in ["rust", "javascript"] {
        let d = temp(&format!("ask-before-build-{backend}"));
        let target = d.join("target-dir");
        fs::write(
            d.join("main.taut"),
            "import std::builtin::os\n\nmatch perform fs_read_bytes(\"x\") {\n  Ok(b) => print(\"ok\")\n  Err(e) => print(io_message(e))\n}\n",
        )
        .unwrap();
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_tauto"))
            .args(["run", "--backend", backend, "main.taut"])
            .current_dir(&d)
            .env("TAUTO_HOME", d.join("home"))
            .env("TAUTO_TARGET_DIR", &target)
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap();
        assert!(
            !out.status.success(),
            "{backend}: {}",
            String::from_utf8_lossy(&out.stdout)
        );
        assert!(
            !target.join("ws").exists() && !target.join("target").exists(),
            "{backend}: built before asking: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        let _ = fs::remove_dir_all(&d);
    }
}
