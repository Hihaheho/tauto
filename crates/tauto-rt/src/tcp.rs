//! Byte streams of `--allow-net` (`tcp_*` in `std/prelude/Os.taut`): TCP,
//! and Unix domain sockets where the system has them, over the standard
//! library. A listener or a stream is a number into a table of this process,
//! so a task on another thread reaches the same socket.
//!
//! Each operation that waits takes a deadline in the nanoseconds of
//! `monotonic_clock`; `None` waits as long as it takes. A deadline that
//! passes is `Ok(None)`, which the prelude makes `Err(TimedOut)`. Shutting
//! a stream down from another task wakes a read waiting on it, which then
//! sees the end of the stream.
//!
//! A TCP stream sends each write as soon as it is made (`TCP_NODELAY`), as
//! the JavaScript host does: a header written before its body would
//! otherwise wait on the peer's delayed acknowledgement.

use crate::Text;
use std::collections::HashMap;
use std::io::{ErrorKind, Read, Write};
use std::net::{Shutdown, TcpListener, TcpStream, ToSocketAddrs};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

#[cfg(unix)]
use std::os::unix::net::{UnixListener, UnixStream};

/// How often a waiting accept looks again for a connection, a deadline and
/// a close.
const ACCEPT_POLL: Duration = Duration::from_millis(10);

enum Listener {
    Tcp(TcpListener),
    #[cfg(unix)]
    Unix(UnixListener),
}

/// The socket under a stream. A host that layers a protocol over a stream
/// (TLS) takes it with [`take`]; the deadlines and shutdowns of this module
/// act on this socket, so they hold under the layer too.
pub enum Socket {
    Tcp(TcpStream),
    #[cfg(unix)]
    Unix(UnixStream),
}

impl Socket {
    /// Sets the read timeout of the socket itself.
    pub fn set_read_timeout(&self, t: Option<Duration>) -> std::io::Result<()> {
        match self {
            Socket::Tcp(c) => c.set_read_timeout(t),
            #[cfg(unix)]
            Socket::Unix(c) => c.set_read_timeout(t),
        }
    }

    /// Sets the write timeout of the socket itself.
    pub fn set_write_timeout(&self, t: Option<Duration>) -> std::io::Result<()> {
        match self {
            Socket::Tcp(c) => c.set_write_timeout(t),
            #[cfg(unix)]
            Socket::Unix(c) => c.set_write_timeout(t),
        }
    }

    /// Another handle to the same socket, as `TcpStream::try_clone`.
    pub fn try_clone(&self) -> std::io::Result<Socket> {
        Ok(match self {
            Socket::Tcp(c) => Socket::Tcp(c.try_clone()?),
            #[cfg(unix)]
            Socket::Unix(c) => Socket::Unix(c.try_clone()?),
        })
    }

    pub fn shutdown(&self, how: Shutdown) -> std::io::Result<()> {
        shutdown(self, how)
    }
}

impl Read for Socket {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match self {
            Socket::Tcp(c) => c.read(buf),
            #[cfg(unix)]
            Socket::Unix(c) => c.read(buf),
        }
    }
}

impl Write for Socket {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self {
            Socket::Tcp(c) => c.write(buf),
            #[cfg(unix)]
            Socket::Unix(c) => c.write(buf),
        }
    }
    fn flush(&mut self) -> std::io::Result<()> {
        match self {
            Socket::Tcp(c) => c.flush(),
            #[cfg(unix)]
            Socket::Unix(c) => c.flush(),
        }
    }
}

/// Takes a stream's socket out of the table, for a host that layers a
/// protocol over it: the number no longer names a stream. `None` when no
/// stream has the number, or a task still holds it in a wait.
pub fn take(id: u64) -> Option<Socket> {
    let opened = with(|t| t.streams.remove(&id))?;
    match Arc::try_unwrap(opened) {
        Ok(o) => Some(o.socket),
        Err(back) => {
            with(|t| t.streams.insert(id, back));
            None
        }
    }
}

/// Puts a socket in the table as a stream, as `tcp_accept` and
/// `tcp_connect` do: its number, its address and its peer's.
pub fn add(socket: Socket, local: String, peer: String) -> Vec<Text> {
    add_stream(socket, local, peer)
}

struct Opened<T> {
    socket: T,
    /// Raised by close: a wait in another task stops at its next look.
    closed: AtomicBool,
}

#[derive(Default)]
struct Table {
    listeners: HashMap<u64, Arc<Opened<Listener>>>,
    streams: HashMap<u64, Arc<Opened<Socket>>>,
    next: u64,
    /// Set by `keep_listeners`: a listener outlives the run that opened it,
    /// and an accept gives up waiting when the flag is raised.
    keep: Option<Arc<AtomicBool>>,
    /// Each kept listener's number, by the address it was asked for.
    asked: HashMap<String, (u64, String)>,
}

/// For `tauto dev`: a listener outlives the run that opened it, so a run
/// that listens again on the same address is given the same listener and
/// the address stays bound across reloads. While `stop` is raised, an
/// accept stops waiting and fails.
pub fn keep_listeners(stop: Arc<AtomicBool>) {
    with(|t| t.keep = Some(stop));
}

/// For `tauto dev`, when a run is stopped: its streams are closed, which
/// ends a read or write waiting on one.
pub fn drop_streams() {
    let streams: Vec<_> = with(|t| t.streams.drain().map(|(_, s)| s).collect());
    for s in streams {
        s.closed.store(true, Ordering::Release);
        let _ = shutdown(&s.socket, Shutdown::Both);
    }
}

fn stopping() -> bool {
    with(|t| t.keep.as_ref().is_some_and(|k| k.load(Ordering::Relaxed)))
}

static TABLE: Mutex<Option<Table>> = Mutex::new(None);

fn with<T>(f: impl FnOnce(&mut Table) -> T) -> T {
    let mut guard = TABLE.lock().unwrap_or_else(|e| e.into_inner());
    f(guard.get_or_insert_with(Table::default))
}

fn failed(e: impl std::fmt::Display) -> Text {
    Text::from(e.to_string())
}

/// An address as the permission check reads it: `HOST:PORT` (an IPv6 host
/// in brackets) or `unix:PATH`.
pub enum Address {
    Tcp { host: String, port: u16 },
    Unix(String),
}

impl Address {
    pub fn parse(text: &str) -> Option<Address> {
        if let Some(path) = text.strip_prefix("unix:") {
            return (!path.is_empty()).then(|| Address::Unix(path.to_string()));
        }
        let (host, port) = text.rsplit_once(':')?;
        let port = port.parse().ok().filter(|_| !port.starts_with('+'))?;
        let host = match host.strip_prefix('[') {
            Some(inner) => inner
                .strip_suffix(']')?
                .parse::<std::net::Ipv6Addr>()
                .ok()?
                .to_string(),
            None => {
                let plain = !host.is_empty()
                    && host
                        .bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'-');
                if !plain {
                    return None;
                }
                host.to_ascii_lowercase()
            }
        };
        Some(Address::Tcp { host, port })
    }

    /// The address as text again, in the spelling the host acts on.
    pub fn text(&self) -> String {
        match self {
            Address::Tcp { host, port } if host.contains(':') => format!("[{host}]:{port}"),
            Address::Tcp { host, port } => format!("{host}:{port}"),
            Address::Unix(path) => format!("unix:{path}"),
        }
    }
}

/// What is left of `deadline` (nanoseconds of `monotonic_clock`); `Some(0)`
/// once it has passed.
fn left(deadline: Option<i64>) -> Option<Duration> {
    deadline.map(|d| {
        let now = crate::stdlib::os_monotonic_ns();
        Duration::from_nanos(d.saturating_sub(now).max(0) as u64)
    })
}

/// Runs `op` on the socket once without waiting, for a deadline that has
/// already passed: what has already arrived (or room the socket already has)
/// still counts, as a timeout polls once before it gives up.
fn without_waiting<T>(
    socket: &Socket,
    op: impl FnOnce(&Socket) -> std::io::Result<T>,
) -> std::io::Result<T> {
    let set = |on: bool| match socket {
        Socket::Tcp(c) => c.set_nonblocking(on),
        #[cfg(unix)]
        Socket::Unix(c) => c.set_nonblocking(on),
    };
    set(true)?;
    let done = op(socket);
    set(false)?;
    done
}

fn timed_out(e: &std::io::Error) -> bool {
    matches!(e.kind(), ErrorKind::WouldBlock | ErrorKind::TimedOut)
}

fn add_stream(socket: Socket, local: String, peer: String) -> Vec<Text> {
    let id = with(|t| {
        let id = t.next;
        t.next += 1;
        let opened = Opened {
            socket,
            closed: AtomicBool::new(false),
        };
        t.streams.insert(id, Arc::new(opened));
        id
    });
    vec![
        Text::from(id.to_string()),
        Text::from(local),
        Text::from(peer),
    ]
}

fn stream(id: u64) -> Result<Arc<Opened<Socket>>, Text> {
    with(|t| t.streams.get(&id).cloned()).ok_or_else(|| Text::from(format!("no stream {id}")))
}

/// Listens on an address the permission check gave: the listener's number,
/// then the address bound (with port 0 the system picks the port).
pub fn os_tcp_listen_vec(address: Text) -> Result<Vec<Text>, Text> {
    let kept = with(|t| {
        t.keep.as_ref()?;
        let (id, bound) = t.asked.get(&*address)?.clone();
        t.listeners.contains_key(&id).then_some((id, bound))
    });
    if let Some((id, bound)) = kept {
        return Ok(vec![Text::from(id.to_string()), Text::from(bound)]);
    }
    let (listener, bound) = match Address::parse(&address) {
        Some(Address::Tcp { host, port }) => {
            let l = TcpListener::bind((host.as_str(), port)).map_err(failed)?;
            let bound = l.local_addr().map_err(failed)?.to_string();
            (Listener::Tcp(l), bound)
        }
        #[cfg(unix)]
        Some(Address::Unix(path)) => {
            let l = UnixListener::bind(&path).map_err(failed)?;
            (Listener::Unix(l), format!("unix:{path}"))
        }
        _ => return Err(Text::from(format!("cannot listen on {address}"))),
    };
    match &listener {
        Listener::Tcp(l) => l.set_nonblocking(true),
        #[cfg(unix)]
        Listener::Unix(l) => l.set_nonblocking(true),
    }
    .map_err(failed)?;
    let id = with(|t| {
        let id = t.next;
        t.next += 1;
        let opened = Opened {
            socket: listener,
            closed: AtomicBool::new(false),
        };
        t.listeners.insert(id, Arc::new(opened));
        if t.keep.is_some() {
            t.asked.insert(address.to_string(), (id, bound.clone()));
        }
        id
    });
    Ok(vec![Text::from(id.to_string()), Text::from(bound)])
}

/// The next connection to a listener: the stream's number, the local
/// address, then the peer's. `Ok(None)` when the deadline passes first; a
/// deadline already past still takes a connection that is already waiting.
pub fn os_tcp_accept_vec(listener: u64, deadline: Option<i64>) -> Result<Option<Vec<Text>>, Text> {
    let l = with(|t| t.listeners.get(&listener).cloned())
        .ok_or_else(|| Text::from(format!("no listener {listener}")))?;
    loop {
        if l.closed.load(Ordering::Acquire) {
            return Err(Text::from("the listener was closed"));
        }
        if stopping() {
            return Err(Text::from("the program is reloading"));
        }
        let accepted = match &l.socket {
            Listener::Tcp(s) => s.accept().and_then(|(c, peer)| {
                c.set_nonblocking(false)?;
                c.set_nodelay(true)?;
                let local = c.local_addr()?.to_string();
                Ok((Socket::Tcp(c), local, peer.to_string()))
            }),
            #[cfg(unix)]
            Listener::Unix(s) => s.accept().and_then(|(c, peer)| {
                c.set_nonblocking(false)?;
                let local = c.local_addr()?;
                let name = |a: &std::os::unix::net::SocketAddr| match a.as_pathname() {
                    Some(p) => format!("unix:{}", p.display()),
                    None => "unix:".to_string(),
                };
                Ok((Socket::Unix(c), name(&local), name(&peer)))
            }),
        };
        match accepted {
            Ok((socket, local, peer)) => return Ok(Some(add_stream(socket, local, peer))),
            Err(e) if e.kind() == ErrorKind::WouldBlock => match left(deadline) {
                Some(d) if d.is_zero() => return Ok(None),
                Some(d) => std::thread::sleep(d.min(ACCEPT_POLL)),
                None => std::thread::sleep(ACCEPT_POLL),
            },
            Err(e) if e.kind() == ErrorKind::Interrupted => {}
            Err(e) => return Err(failed(e)),
        }
    }
}

/// Connects to an address the permission check gave: the stream's number,
/// the local address, then the peer's. `Ok(None)` when the deadline passes
/// first. A host name is tried at each of its addresses in turn.
pub fn os_tcp_connect_vec(address: Text, deadline: Option<i64>) -> Result<Option<Vec<Text>>, Text> {
    match Address::parse(&address) {
        Some(Address::Tcp { host, port }) => {
            let mut last = None;
            for addr in (host.as_str(), port).to_socket_addrs().map_err(failed)? {
                let tried = match left(deadline) {
                    Some(d) if d.is_zero() => return Ok(None),
                    Some(d) => TcpStream::connect_timeout(&addr, d),
                    None => TcpStream::connect(addr),
                };
                match tried {
                    Ok(s) => {
                        s.set_nodelay(true).map_err(failed)?;
                        let local = s.local_addr().map_err(failed)?.to_string();
                        let peer = s.peer_addr().map_err(failed)?.to_string();
                        return Ok(Some(add_stream(Socket::Tcp(s), local, peer)));
                    }
                    Err(e) => last = Some(e),
                }
            }
            match last {
                Some(e) if timed_out(&e) => Ok(None),
                Some(e) => Err(failed(e)),
                None => Err(Text::from(format!("{host} has no address"))),
            }
        }
        #[cfg(unix)]
        Some(Address::Unix(path)) => {
            let s = UnixStream::connect(&path).map_err(failed)?;
            Ok(Some(add_stream(
                Socket::Unix(s),
                "unix:".to_string(),
                format!("unix:{path}"),
            )))
        }
        _ => Err(Text::from(format!("cannot connect to {address}"))),
    }
}

/// Up to `max` bytes, as soon as any arrive; none at the end of the stream
/// (the peer shut its side, or this side was shut down for reading).
/// `Ok(None)` when the deadline passes first. A deadline already past still
/// takes bytes (or the end) that have already arrived, without waiting.
pub fn os_tcp_read_vec(id: u64, max: u64, deadline: Option<i64>) -> Result<Option<Vec<u8>>, Text> {
    let s = stream(id)?;
    let mut buf = vec![0; max.min(1 << 20) as usize];
    if buf.is_empty() {
        return Ok(Some(buf));
    }
    loop {
        if s.closed.load(Ordering::Acquire) {
            return Ok(Some(Vec::new()));
        }
        let wait = left(deadline);
        let expired = wait.is_some_and(|d| d.is_zero());
        let read = if expired {
            without_waiting(&s.socket, |socket| match socket {
                Socket::Tcp(c) => (&*c).read(&mut buf),
                #[cfg(unix)]
                Socket::Unix(c) => (&*c).read(&mut buf),
            })
        } else {
            match &s.socket {
                Socket::Tcp(c) => c.set_read_timeout(wait).and_then(|()| (&*c).read(&mut buf)),
                #[cfg(unix)]
                Socket::Unix(c) => c.set_read_timeout(wait).and_then(|()| (&*c).read(&mut buf)),
            }
        };
        match read {
            Ok(n) => {
                buf.truncate(n);
                return Ok(Some(buf));
            }
            Err(e) if e.kind() == ErrorKind::Interrupted => {}
            Err(e) if timed_out(&e) => {
                if expired {
                    return Ok(None);
                }
            }
            Err(e) => return Err(failed(e)),
        }
    }
}

/// Writes all of `bytes`. `Ok(None)` when the deadline passes first; some
/// of the bytes may have been sent by then. A deadline already past still
/// sends what the socket takes without waiting.
pub fn os_tcp_write_vec(
    id: u64,
    bytes: Vec<u8>,
    deadline: Option<i64>,
) -> Result<Option<()>, Text> {
    let s = stream(id)?;
    let mut at = 0;
    while at < bytes.len() {
        if s.closed.load(Ordering::Acquire) {
            return Err(Text::from("the stream was closed"));
        }
        let wait = left(deadline);
        let expired = wait.is_some_and(|d| d.is_zero());
        let wrote = if expired {
            without_waiting(&s.socket, |socket| match socket {
                Socket::Tcp(c) => (&*c).write(&bytes[at..]),
                #[cfg(unix)]
                Socket::Unix(c) => (&*c).write(&bytes[at..]),
            })
        } else {
            match &s.socket {
                Socket::Tcp(c) => c
                    .set_write_timeout(wait)
                    .and_then(|()| (&*c).write(&bytes[at..])),
                #[cfg(unix)]
                Socket::Unix(c) => c
                    .set_write_timeout(wait)
                    .and_then(|()| (&*c).write(&bytes[at..])),
            }
        };
        match wrote {
            Ok(0) => return Err(Text::from("the stream takes no more bytes")),
            Ok(n) => at += n,
            Err(e) if e.kind() == ErrorKind::Interrupted => {}
            Err(e) if timed_out(&e) => {
                if expired {
                    return Ok(None);
                }
            }
            Err(e) => return Err(failed(e)),
        }
    }
    Ok(Some(()))
}

/// `os_tcp_read_vec` as `Bytes`, as the prelude's extern takes it.
pub fn os_tcp_read(
    id: u64,
    max: u64,
    deadline: Option<i64>,
) -> Result<Option<crate::stdlib::Bytes>, Text> {
    os_tcp_read_vec(id, max, deadline).map(|b| b.map(Into::into))
}

/// `os_tcp_write_vec` of `Bytes`, as the prelude's extern takes it.
pub fn os_tcp_write(
    id: u64,
    bytes: crate::stdlib::Bytes,
    deadline: Option<i64>,
) -> Result<Option<()>, Text> {
    os_tcp_write_vec(id, bytes.to_vec(), deadline)
}

/// Shuts down reading (0), writing (1) or both (2). Shutting down reading
/// wakes a read waiting in another task.
pub fn os_tcp_shutdown(id: u64, how: u64) -> Result<(), Text> {
    let s = stream(id)?;
    let how = match how {
        0 => Shutdown::Read,
        1 => Shutdown::Write,
        _ => Shutdown::Both,
    };
    shutdown(&s.socket, how).map_err(failed)
}

fn shutdown(socket: &Socket, how: Shutdown) -> std::io::Result<()> {
    let r = match socket {
        Socket::Tcp(c) => c.shutdown(how),
        #[cfg(unix)]
        Socket::Unix(c) => c.shutdown(how),
    };
    // Shut down already, or the peer has gone: there is nothing left to do.
    match r {
        Err(e) if e.kind() == ErrorKind::NotConnected => Ok(()),
        r => r,
    }
}

/// Closes a stream: a wait on it in another task ends, and the number no
/// longer names it. Closing one closed already does nothing.
pub fn os_tcp_close(id: u64) {
    if let Some(s) = with(|t| t.streams.remove(&id)) {
        s.closed.store(true, Ordering::Release);
        let _ = shutdown(&s.socket, Shutdown::Both);
    }
}

/// Stops listening: an accept waiting in another task fails, and a Unix
/// socket's file is removed.
pub fn os_tcp_unlisten(id: u64) {
    if let Some(l) = with(|t| t.listeners.remove(&id)) {
        l.closed.store(true, Ordering::Release);
        #[cfg(unix)]
        if let Listener::Unix(u) = &l.socket {
            if let Some(p) = u
                .local_addr()
                .ok()
                .and_then(|a| a.as_pathname().map(|p| p.to_path_buf()))
            {
                let _ = std::fs::remove_file(p);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(t: &Text) -> u64 {
        t.parse().unwrap()
    }

    fn after(ms: i64) -> Option<i64> {
        Some(crate::stdlib::os_monotonic_ns() + ms * 1_000_000)
    }

    #[test]
    fn addresses() {
        let text = |t: &str| Address::parse(t).map(|a| a.text());
        assert_eq!(text("Example.COM:80").as_deref(), Some("example.com:80"));
        assert_eq!(text("[::1]:8080").as_deref(), Some("[::1]:8080"));
        assert_eq!(
            text("unix:/run/a.sock").as_deref(),
            Some("unix:/run/a.sock")
        );
        for bad in [
            "example.com",
            ":80",
            "a:+80",
            "a:70000",
            "[x]:1",
            "a b:1",
            "unix:",
            "a/b:1",
        ] {
            assert!(Address::parse(bad).is_none(), "{bad}");
        }
    }

    #[test]
    fn tcp_streams_send_without_delay() {
        let l = os_tcp_listen_vec(Text::from("127.0.0.1:0")).unwrap();
        let c = os_tcp_connect_vec(l[1].clone(), after(5000))
            .unwrap()
            .unwrap();
        let a = os_tcp_accept_vec(n(&l[0]), after(5000)).unwrap().unwrap();
        for stream in [&c[0], &a[0]] {
            match take(n(stream)) {
                Some(Socket::Tcp(s)) => assert!(s.nodelay().unwrap()),
                _ => panic!("not a TCP stream"),
            }
        }
        os_tcp_unlisten(n(&l[0]));
    }

    #[test]
    fn echo_with_peer_addresses() {
        let l = os_tcp_listen_vec(Text::from("127.0.0.1:0")).unwrap();
        let bound = l[1].to_string();
        let client = std::thread::spawn(move || {
            let c = os_tcp_connect_vec(Text::from(bound), after(5000))
                .unwrap()
                .unwrap();
            os_tcp_write_vec(n(&c[0]), b"ping".to_vec(), None)
                .unwrap()
                .unwrap();
            os_tcp_shutdown(n(&c[0]), 1).unwrap();
            let back = os_tcp_read_vec(n(&c[0]), 16, after(5000)).unwrap().unwrap();
            os_tcp_close(n(&c[0]));
            (c[1].to_string(), back)
        });
        let s = os_tcp_accept_vec(n(&l[0]), after(5000)).unwrap().unwrap();
        let got = os_tcp_read_vec(n(&s[0]), 2, None).unwrap().unwrap();
        assert_eq!(got, b"pi");
        let rest = os_tcp_read_vec(n(&s[0]), 16, None).unwrap().unwrap();
        assert_eq!(rest, b"ng");
        assert!(
            os_tcp_read_vec(n(&s[0]), 16, None)
                .unwrap()
                .unwrap()
                .is_empty()
        );
        os_tcp_write_vec(n(&s[0]), b"pong".to_vec(), None)
            .unwrap()
            .unwrap();
        os_tcp_close(n(&s[0]));
        let (client_local, back) = client.join().unwrap();
        assert_eq!(back, b"pong");
        assert_eq!(s[2].to_string(), client_local);
        os_tcp_unlisten(n(&l[0]));
    }

    #[test]
    // Another test of this process may set a host whose clock stands still,
    // so the deadlines here are passed already rather than soon.
    fn deadlines_pass() {
        let l = os_tcp_listen_vec(Text::from("127.0.0.1:0")).unwrap();
        assert!(os_tcp_accept_vec(n(&l[0]), after(-1)).unwrap().is_none());
        let c = os_tcp_connect_vec(l[1].clone(), after(5000))
            .unwrap()
            .unwrap();
        // A peer that sends nothing does not hold the read past its deadline.
        assert!(os_tcp_read_vec(n(&c[0]), 8, after(-1)).unwrap().is_none());
        os_tcp_close(n(&c[0]));
        os_tcp_unlisten(n(&l[0]));
    }

    #[test]
    // A deadline already passed still takes what has already arrived, so a
    // program can check an idle connection without waiting on it.
    fn passed_deadline_takes_what_arrived() {
        let l = os_tcp_listen_vec(Text::from("127.0.0.1:0")).unwrap();
        let c = os_tcp_connect_vec(l[1].clone(), after(5000))
            .unwrap()
            .unwrap();
        let mut s = None;
        for _ in 0..500 {
            s = os_tcp_accept_vec(n(&l[0]), after(-1)).unwrap();
            if s.is_some() {
                break;
            }
            std::thread::sleep(Duration::from_millis(2));
        }
        let s = s.expect("a waiting connection is accepted past the deadline");
        os_tcp_write_vec(n(&c[0]), b"hi".to_vec(), after(-1))
            .unwrap()
            .unwrap();
        let mut got = None;
        for _ in 0..500 {
            got = os_tcp_read_vec(n(&s[0]), 8, after(-1)).unwrap();
            if got.is_some() {
                break;
            }
            std::thread::sleep(Duration::from_millis(2));
        }
        assert_eq!(got.unwrap(), b"hi");
        assert!(os_tcp_read_vec(n(&s[0]), 8, after(-1)).unwrap().is_none());
        os_tcp_close(n(&c[0]));
        let mut end = None;
        for _ in 0..500 {
            end = os_tcp_read_vec(n(&s[0]), 8, after(-1)).unwrap();
            if end.is_some() {
                break;
            }
            std::thread::sleep(Duration::from_millis(2));
        }
        assert_eq!(end, Some(Vec::new()));
        os_tcp_close(n(&s[0]));
        os_tcp_unlisten(n(&l[0]));
    }

    #[test]
    fn shutdown_from_another_thread_wakes_a_read() {
        let l = os_tcp_listen_vec(Text::from("127.0.0.1:0")).unwrap();
        let c = os_tcp_connect_vec(l[1].clone(), None).unwrap().unwrap();
        let id = n(&c[0]);
        let reader = std::thread::spawn(move || os_tcp_read_vec(id, 8, None).ok());
        std::thread::sleep(Duration::from_millis(50));
        os_tcp_shutdown(id, 0).unwrap();
        assert_eq!(reader.join().unwrap(), Some(Some(Vec::new())));
        os_tcp_close(id);
        os_tcp_unlisten(n(&l[0]));
    }

    #[test]
    fn unlisten_from_another_thread_ends_an_accept() {
        let l = os_tcp_listen_vec(Text::from("127.0.0.1:0")).unwrap();
        let id = n(&l[0]);
        let waiter = std::thread::spawn(move || os_tcp_accept_vec(id, None).is_err());
        std::thread::sleep(Duration::from_millis(50));
        os_tcp_unlisten(id);
        assert!(waiter.join().unwrap());
    }

    #[cfg(unix)]
    #[test]
    fn unix_sockets() {
        let dir = std::env::temp_dir().join(format!("tauto-rt-uds-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = format!("unix:{}", dir.join("s.sock").display());
        let l = os_tcp_listen_vec(Text::from(path.as_str())).unwrap();
        assert_eq!(&*l[1], path);
        let c = os_tcp_connect_vec(Text::from(path.as_str()), None)
            .unwrap()
            .unwrap();
        let s = os_tcp_accept_vec(n(&l[0]), after(5000)).unwrap().unwrap();
        os_tcp_write_vec(n(&c[0]), b"hi".to_vec(), None)
            .unwrap()
            .unwrap();
        assert_eq!(os_tcp_read_vec(n(&s[0]), 8, None).unwrap().unwrap(), b"hi");
        os_tcp_close(n(&c[0]));
        os_tcp_close(n(&s[0]));
        os_tcp_unlisten(n(&l[0]));
        assert!(!dir.join("s.sock").exists());
        let _ = std::fs::remove_dir_all(dir);
    }
}
