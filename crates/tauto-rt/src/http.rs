//! HTTP whose bodies go a piece at a time (`net_open` and its companions in
//! `std/builtin/os.taut`). A request being sent and a response being read
//! are numbers into a table of this process, as `tcp` keeps streams, so a
//! task on another thread reaches the same exchange.
//!
//! A request is sent by a thread of its own: the program's writes reach it
//! through a channel of one piece, so a write waits while the peer is slow
//! to take the last one. Once the program finishes the request, the thread
//! answers the status and headers, then reads the response body into a
//! channel of one piece, so the host reads ahead at most one piece of what
//! the program has not asked for. Each operation that waits takes a deadline
//! in the nanoseconds of `monotonic_clock`; one that passes is `Ok(None)`.
//!
//! A body that breaks off is an error, not an end: a program must not take
//! a cut response for a whole one.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError, SyncSender, TrySendError};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Duration;

use crate::Text;
use crate::stdlib::Bytes;

/// The largest piece the host reads from a response body at once.
const PIECE: usize = 1 << 16;

/// What the sending thread answers once the request is finished: the
/// status and each header's name and value, and the body's pieces.
type Head = Result<(Vec<String>, Receiver<Result<Vec<u8>, String>>), String>;

/// A request the program is still writing.
struct Sending {
    /// `None` once finished: the thread then sees the end of the body.
    body: Mutex<Option<SyncSender<Vec<u8>>>>,
    head: Mutex<Receiver<Head>>,
    /// Set when the request goes without being finished (closed, or dropped
    /// with the run): the thread then fails the body rather than end it, so
    /// the peer never takes a cut body for a whole one.
    abandoned: Arc<AtomicBool>,
    finished: AtomicBool,
}

impl Drop for Sending {
    fn drop(&mut self) {
        if !self.finished.load(Ordering::SeqCst) {
            self.abandoned.store(true, Ordering::SeqCst);
        }
    }
}

/// A response body the program reads.
struct Reading {
    pieces: Mutex<Receiver<Result<Vec<u8>, String>>>,
    /// Bytes a read left over when it asked for fewer than the piece held.
    rest: Mutex<Vec<u8>>,
    /// Set once the body ended or failed: every later read sees the same.
    done: Mutex<Option<Result<(), String>>>,
}

enum Entry {
    Sending(Arc<Sending>),
    Reading(Arc<Reading>),
}

#[derive(Default)]
struct Table {
    entries: HashMap<u64, Entry>,
    next: u64,
}

fn table() -> &'static Mutex<Table> {
    static TABLE: OnceLock<Mutex<Table>> = OnceLock::new();
    TABLE.get_or_init(Mutex::default)
}

fn with<T>(f: impl FnOnce(&mut Table) -> T) -> T {
    f(&mut table().lock().unwrap_or_else(|e| e.into_inner()))
}

fn add(e: Entry) -> u64 {
    with(|t| {
        t.next += 1;
        t.entries.insert(t.next, e);
        t.next
    })
}

fn sending(id: u64) -> Result<Arc<Sending>, Text> {
    with(|t| match t.entries.get(&id) {
        Some(Entry::Sending(s)) => Some(s.clone()),
        _ => None,
    })
    .ok_or_else(|| Text::from("no such request"))
}

fn reading(id: u64) -> Result<Arc<Reading>, Text> {
    with(|t| match t.entries.get(&id) {
        Some(Entry::Reading(r)) => Some(r.clone()),
        _ => None,
    })
    .ok_or_else(|| Text::from("no such response"))
}

fn left(deadline: Option<i64>) -> Option<Duration> {
    deadline.map(|d| {
        let now = crate::stdlib::os_monotonic_ns();
        Duration::from_nanos((d - now).max(0) as u64)
    })
}

fn recv<T>(rx: &Receiver<T>, deadline: Option<i64>) -> Result<T, RecvTimeoutError> {
    match left(deadline) {
        None => rx.recv().map_err(|_| RecvTimeoutError::Disconnected),
        Some(d) => rx.recv_timeout(d),
    }
}

/// Closes every request and response, as `tauto dev` does between runs: a
/// body a run dropped without closing goes here. The threads see their
/// channels gone and stop.
pub fn drop_exchanges() {
    with(|t| t.entries.clear());
}

/// Ends a request or a response; a read or write waiting on it in another
/// task sees its channel gone.
pub fn os_http_close(id: u64) {
    with(|t| t.entries.remove(&id));
}

/// Starts a request to the URL `os_check` gave, connected to `address` if it
/// is not empty (as `os_fetch_vec`). `headers` are each header's name and
/// value. The number of the request, whose body the program then writes.
#[cfg(feature = "net")]
pub fn os_http_open_vec(
    method: Text,
    url: Text,
    address: Text,
    headers: Vec<Text>,
) -> Result<u64, Text> {
    let client = crate::stdlib::http_client(&url, &address)?;
    let method =
        reqwest::Method::from_bytes(method.as_bytes()).map_err(|e| Text::from(e.to_string()))?;
    let mut request = client.request(method, &*url);
    for pair in headers.chunks(2) {
        if let [name, value] = pair {
            request = request.header(&**name, &**value);
        }
    }
    use std::sync::mpsc::sync_channel;
    let (body_tx, body_rx) = sync_channel::<Vec<u8>>(1);
    let (head_tx, head_rx) = sync_channel::<Head>(1);
    let abandoned = Arc::new(AtomicBool::new(false));
    let reader = Pieces {
        from: body_rx,
        piece: Vec::new(),
        at: 0,
        abandoned: abandoned.clone(),
    };
    std::thread::spawn(move || {
        let sent = request
            .body(reqwest::blocking::Body::new(reader))
            .send()
            .map_err(|e| e.to_string());
        let mut response = match sent {
            Ok(r) => r,
            Err(e) => {
                let _ = head_tx.send(Err(e));
                return;
            }
        };
        let mut head = vec![response.status().as_u16().to_string()];
        for (name, value) in response.headers() {
            let Ok(value) = std::str::from_utf8(value.as_bytes()) else {
                let _ = head_tx.send(Err(format!(
                    "the value of the response header {name} is not UTF-8"
                )));
                return;
            };
            head.push(name.as_str().to_string());
            head.push(value.to_string());
        }
        let (tx, rx) = sync_channel(1);
        if head_tx.send(Ok((head, rx))).is_err() {
            return;
        }
        let mut buf = vec![0; PIECE];
        loop {
            use std::io::Read;
            let got = match response.read(&mut buf) {
                Ok(0) => {
                    let _ = tx.send(Ok(Vec::new()));
                    return;
                }
                Ok(n) => Ok(buf[..n].to_vec()),
                Err(e) => Err(format!("the response body broke off: {e}")),
            };
            let failed = got.is_err();
            if tx.send(got).is_err() || failed {
                return;
            }
        }
    });
    Ok(add(Entry::Sending(Arc::new(Sending {
        body: Mutex::new(Some(body_tx)),
        head: Mutex::new(head_rx),
        abandoned,
        finished: AtomicBool::new(false),
    }))))
}

#[cfg(not(feature = "net"))]
pub fn os_http_open_vec(_: Text, _: Text, _: Text, _: Vec<Text>) -> Result<u64, Text> {
    Err(Text::from(
        "this build has no network: the `net` feature of tauto-rt is off".to_string(),
    ))
}

/// The request body as the sending thread reads it: the pieces the program
/// wrote, then the end once it finished (its sender is gone).
#[cfg(feature = "net")]
struct Pieces {
    from: Receiver<Vec<u8>>,
    piece: Vec<u8>,
    at: usize,
    abandoned: Arc<AtomicBool>,
}

#[cfg(feature = "net")]
impl std::io::Read for Pieces {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        while self.at == self.piece.len() {
            match self.from.recv() {
                Ok(p) => {
                    self.piece = p;
                    self.at = 0;
                }
                Err(_) if self.abandoned.load(Ordering::SeqCst) => {
                    return Err(std::io::Error::other(
                        "the request was closed before it was finished",
                    ));
                }
                Err(_) => return Ok(0),
            }
        }
        let n = buf.len().min(self.piece.len() - self.at);
        buf[..n].copy_from_slice(&self.piece[self.at..self.at + n]);
        self.at += n;
        Ok(n)
    }
}

/// Writes all of `bytes` to a request's body. `Ok(None)` when the deadline
/// passed before the sending thread took the last piece.
pub fn os_http_write_vec(
    id: u64,
    bytes: Vec<u8>,
    deadline: Option<i64>,
) -> Result<Option<()>, Text> {
    let s = sending(id)?;
    let body = s.body.lock().unwrap_or_else(|e| e.into_inner());
    let Some(tx) = body.as_ref() else {
        return Err(Text::from("the request is finished"));
    };
    if bytes.is_empty() {
        return Ok(Some(()));
    }
    let gone = || Text::from("the request failed before its body was sent");
    match deadline {
        None => tx.send(bytes).map(Some).map_err(|_| gone()),
        Some(_) => {
            let mut piece = bytes;
            loop {
                match tx.try_send(piece) {
                    Ok(()) => return Ok(Some(())),
                    Err(TrySendError::Disconnected(_)) => return Err(gone()),
                    Err(TrySendError::Full(p)) => {
                        if left(deadline) == Some(Duration::ZERO) {
                            return Ok(None);
                        }
                        piece = p;
                        std::thread::sleep(Duration::from_millis(1));
                    }
                }
            }
        }
    }
}

/// Ends a request's body and waits for the response: its status and each
/// header's name and value, then the number of its body. Once it answers,
/// the request's number names nothing, whether it succeeded or not.
/// `Ok(None)` when the deadline passed first: the body stays ended, and the
/// request goes on, for the next finish to wait for again.
pub fn os_http_finish_vec(
    id: u64,
    deadline: Option<i64>,
) -> Result<Option<(Vec<Text>, u64)>, Text> {
    let s = sending(id)?;
    s.finished.store(true, Ordering::SeqCst);
    s.body.lock().unwrap_or_else(|e| e.into_inner()).take();
    let head = s.head.lock().unwrap_or_else(|e| e.into_inner());
    let got = recv(&head, deadline);
    if !matches!(got, Err(RecvTimeoutError::Timeout)) {
        os_http_close(id);
    }
    match got {
        Ok(Ok((fields, pieces))) => {
            let fields = fields.into_iter().map(Text::from).collect();
            let body = add(Entry::Reading(Arc::new(Reading {
                pieces: Mutex::new(pieces),
                rest: Mutex::new(Vec::new()),
                done: Mutex::new(None),
            })));
            Ok(Some((fields, body)))
        }
        Ok(Err(e)) => Err(Text::from(e)),
        Err(RecvTimeoutError::Timeout) => Ok(None),
        Err(RecvTimeoutError::Disconnected) => Err(Text::from("the request failed")),
    }
}

/// Up to `max` bytes of a response body, as soon as any arrive; none at its
/// end. `Ok(None)` when the deadline passed first.
pub fn os_http_read_vec(id: u64, max: u64, deadline: Option<i64>) -> Result<Option<Vec<u8>>, Text> {
    let r = reading(id)?;
    let max = max.min(1 << 20) as usize;
    let mut rest = r.rest.lock().unwrap_or_else(|e| e.into_inner());
    if rest.is_empty() {
        let mut done = r.done.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(d) = done.as_ref() {
            return d.clone().map(|()| Some(Vec::new())).map_err(Text::from);
        }
        if max == 0 {
            return Ok(Some(Vec::new()));
        }
        let pieces = r.pieces.lock().unwrap_or_else(|e| e.into_inner());
        match recv(&pieces, deadline) {
            Ok(Ok(p)) if p.is_empty() => {
                *done = Some(Ok(()));
                return Ok(Some(Vec::new()));
            }
            Ok(Ok(p)) => *rest = p,
            Ok(Err(e)) => {
                *done = Some(Err(e.clone()));
                return Err(Text::from(e));
            }
            Err(RecvTimeoutError::Timeout) => return Ok(None),
            Err(RecvTimeoutError::Disconnected) => {
                let e = "the response body broke off".to_string();
                *done = Some(Err(e.clone()));
                return Err(Text::from(e));
            }
        }
    }
    let n = rest.len().min(max);
    Ok(Some(rest.drain(..n).collect()))
}

/// `os_http_write_vec` with `Bytes`, as the prelude's extern takes it.
pub fn os_http_write(id: u64, bytes: Bytes, deadline: Option<i64>) -> Result<Option<()>, Text> {
    os_http_write_vec(id, bytes.to_vec(), deadline)
}

/// `os_http_read_vec` as `Bytes`, as the prelude's extern gives it.
pub fn os_http_read(id: u64, max: u64, deadline: Option<i64>) -> Result<Option<Bytes>, Text> {
    os_http_read_vec(id, max, deadline).map(|b| b.map(Into::into))
}

#[cfg(all(test, feature = "net"))]
mod tests {
    use super::*;
    use std::io::{BufRead, BufReader, Read, Write};
    use std::net::TcpListener;

    /// A server of one exchange: it reads a chunked request body, answers
    /// its length in a header, then sends `pieces` one at a time, each
    /// after the client acknowledged nothing (they arrive as they are
    /// written). `cut` ends the connection before the last chunk.
    fn serve(pieces: Vec<&'static str>, cut: bool) -> (String, std::thread::JoinHandle<Vec<u8>>) {
        let l = TcpListener::bind("127.0.0.1:0").unwrap();
        let url = format!("http://{}/", l.local_addr().unwrap());
        let h = std::thread::spawn(move || {
            let (s, _) = l.accept().unwrap();
            let mut r = BufReader::new(s.try_clone().unwrap());
            let mut line = String::new();
            let mut chunked = false;
            loop {
                line.clear();
                r.read_line(&mut line).unwrap();
                if line
                    .to_ascii_lowercase()
                    .starts_with("transfer-encoding: chunked")
                {
                    chunked = true;
                }
                if line == "\r\n" {
                    break;
                }
            }
            let mut body = Vec::new();
            while chunked {
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
                "HTTP/1.1 200 OK\r\nx-got: {}\r\ntransfer-encoding: chunked\r\n\r\n",
                body.len()
            )
            .unwrap();
            for p in pieces {
                write!(w, "{:x}\r\n{p}\r\n", p.len()).unwrap();
                w.flush().unwrap();
                std::thread::sleep(Duration::from_millis(30));
            }
            if !cut {
                write!(w, "0\r\n\r\n").unwrap();
            }
            body
        });
        (url, h)
    }

    fn read_all(body: u64) -> Result<Vec<String>, Text> {
        let mut got = Vec::new();
        loop {
            let p = os_http_read_vec(body, 1024, None)?.unwrap();
            if p.is_empty() {
                return Ok(got);
            }
            got.push(String::from_utf8(p).unwrap());
        }
    }

    #[test]
    fn a_body_goes_both_ways_a_piece_at_a_time() {
        let (url, server) = serve(vec!["one", "two", "three"], false);
        let req = os_http_open_vec("POST".into(), url.as_str().into(), "".into(), vec![]).unwrap();
        os_http_write_vec(req, b"hello ".to_vec(), None)
            .unwrap()
            .unwrap();
        os_http_write_vec(req, b"world".to_vec(), None)
            .unwrap()
            .unwrap();
        let (head, body) = os_http_finish_vec(req, None).unwrap().unwrap();
        assert_eq!(&*head[0], "200");
        assert!(head.iter().any(|h| &**h == "11"), "{head:?}");
        let got = read_all(body).unwrap();
        assert_eq!(got.concat(), "onetwothree");
        assert!(got.len() >= 2, "the pieces came at once: {got:?}");
        assert_eq!(server.join().unwrap(), b"hello world");
        // The end stays the end, and the request's number names nothing.
        assert_eq!(os_http_read_vec(body, 8, None).unwrap().unwrap(), b"");
        assert!(os_http_write_vec(req, b"x".to_vec(), None).is_err());
        os_http_close(body);
        assert!(os_http_read_vec(body, 8, None).is_err());
    }

    #[test]
    fn a_body_that_breaks_off_is_an_error() {
        let (url, _server) = serve(vec!["one", "two"], true);
        let req = os_http_open_vec("GET".into(), url.as_str().into(), "".into(), vec![]).unwrap();
        let (_, body) = os_http_finish_vec(req, None).unwrap().unwrap();
        assert!(read_all(body).is_err());
        // And it stays one.
        assert!(os_http_read_vec(body, 8, None).is_err());
    }

    #[test]
    fn a_read_whose_deadline_passes_answers_none() {
        let (url, _server) = serve(vec!["late"], false);
        let req = os_http_open_vec("GET".into(), url.as_str().into(), "".into(), vec![]).unwrap();
        let (_, body) = os_http_finish_vec(req, None).unwrap().unwrap();
        let now = crate::stdlib::os_monotonic_ns();
        let first = os_http_read_vec(body, 8, Some(now)).unwrap();
        // The piece may already be there; a past deadline never waits, and
        // what it did not take is still there for the next read.
        let mut all = String::from_utf8(first.unwrap_or_default()).unwrap();
        all.push_str(&read_all(body).unwrap().concat());
        assert_eq!(all, "late");
    }

    #[test]
    fn a_finish_whose_deadline_passes_can_wait_again() {
        let l = TcpListener::bind("127.0.0.1:0").unwrap();
        let url = format!("http://{}/", l.local_addr().unwrap());
        let server = std::thread::spawn(move || {
            let (mut s, _) = l.accept().unwrap();
            let mut buf = [0; 1024];
            let _ = s.read(&mut buf);
            std::thread::sleep(Duration::from_millis(200));
            write!(s, "HTTP/1.1 204 No Content\r\n\r\n").unwrap();
            std::thread::sleep(Duration::from_millis(100));
        });
        let req = os_http_open_vec("GET".into(), url.as_str().into(), "".into(), vec![]).unwrap();
        let soon = crate::stdlib::os_monotonic_ns() + 10_000_000;
        assert!(os_http_finish_vec(req, Some(soon)).unwrap().is_none());
        assert!(os_http_write_vec(req, b"x".to_vec(), None).is_err());
        let (head, body) = os_http_finish_vec(req, None).unwrap().unwrap();
        assert_eq!(&*head[0], "204");
        assert_eq!(os_http_read_vec(body, 8, None).unwrap().unwrap(), b"");
        assert!(os_http_finish_vec(req, None).is_err());
        server.join().unwrap();
    }

    #[test]
    fn closing_an_unfinished_request_does_not_send_a_cut_body() {
        let l = TcpListener::bind("127.0.0.1:0").unwrap();
        let url = format!("http://{}/", l.local_addr().unwrap());
        let server = std::thread::spawn(move || {
            let (mut s, _) = l.accept().unwrap();
            let mut all = Vec::new();
            let _ = s.read_to_end(&mut all);
            String::from_utf8_lossy(&all).into_owned()
        });
        let req = os_http_open_vec("POST".into(), url.as_str().into(), "".into(), vec![]).unwrap();
        os_http_write_vec(req, b"part".to_vec(), None)
            .unwrap()
            .unwrap();
        os_http_close(req);
        let seen = server.join().unwrap();
        assert!(
            !seen.ends_with("0\r\n\r\n"),
            "the cut body was ended: {seen:?}"
        );
    }
}
