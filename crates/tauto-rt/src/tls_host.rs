//! TLS over the byte streams of `tcp_*` (`tls_*` in `std/builtin/os.taut`),
//! answered with [`crate::tls`] when the `tls` feature is on. A session is a
//! number into a table of this process, like a stream of [`crate::tcp`]:
//! `tls_accept` and `tls_connect` take the stream's socket out of that table,
//! so its number no longer names a stream, whether the handshake succeeds or
//! not. Deadlines are the nanoseconds of `monotonic_clock`, and a deadline
//! that passes is `Ok(None)`, as for the streams.
//!
//! Without the feature each request fails, saying the build has no TLS.

use crate::Text;
use crate::stdlib::Bytes;

/// The texts of an established session: its number, the ALPN protocol
/// (empty for none) and, on a server, the SNI name the client sent (empty for
/// none); and the peer's leaf certificate as DER (empty for none).
pub type Established = (Vec<Text>, Vec<u8>);

#[cfg(feature = "tls")]
pub use with_tls::*;

#[cfg(not(feature = "tls"))]
pub use without_tls::*;

#[cfg(not(feature = "tls"))]
mod without_tls {
    use super::*;

    fn absent<T>() -> Result<T, Text> {
        Err(Text::from("this build of the host has no TLS"))
    }

    pub fn os_tls_accept_vec(
        _stream: u64,
        _names: Vec<Text>,
        _pems: Vec<Bytes>,
        _alpn: Vec<Text>,
        _client_roots: Bytes,
        _deadline: Option<i64>,
    ) -> Result<Option<Established>, Text> {
        absent()
    }

    pub fn os_tls_connect_vec(
        _stream: u64,
        _server_name: Text,
        _roots: u64,
        _pems: Vec<Bytes>,
        _alpn: Vec<Text>,
        _deadline: Option<i64>,
    ) -> Result<Option<Established>, Text> {
        absent()
    }

    pub fn os_tls_read(_id: u64, _max: u64, _deadline: Option<i64>) -> Result<Option<Bytes>, Text> {
        absent()
    }

    pub fn os_tls_write(
        _id: u64,
        _bytes: Bytes,
        _deadline: Option<i64>,
    ) -> Result<Option<()>, Text> {
        absent()
    }

    pub fn os_tls_send(
        _id: u64,
        _bytes: Bytes,
        _deadline: Option<i64>,
    ) -> Result<Option<u64>, Text> {
        absent()
    }

    pub fn os_tls_shutdown(_id: u64, _how: u64) -> Result<(), Text> {
        absent()
    }

    pub fn os_tls_close(_id: u64) {}

    pub fn drop_sessions() {}
}

#[cfg(feature = "tls")]
mod with_tls {
    use super::*;
    use crate::tcp::{self, Socket};
    use crate::tls::{self, ClientOptions, Roots, ServerCert, ServerOptions, TlsStream};
    use std::collections::HashMap;
    use std::io::{self, ErrorKind, Read, Write};
    use std::net::Shutdown;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, Mutex};
    use std::time::Duration;

    /// How long a read holds its session before it lets a write in: a read
    /// that waits for the peer does not keep a write in another task waiting.
    const READ_SLICE: Duration = Duration::from_millis(10);

    struct Session {
        /// Dropped before the sockets, so its registration with the
        /// reactor's poller ends while the descriptor is still `ctl`'s.
        ready: tcp::Ready,
        tls: Mutex<TlsStream<Socket>>,
        /// Another handle to the socket, to shut it down without waiting for
        /// a read or write that holds the session.
        ctl: Socket,
        /// Raised by a shutdown of reading: reads see the end.
        read_shut: AtomicBool,
        /// Raised by close: a wait in another task stops at its next look.
        closed: AtomicBool,
    }

    #[derive(Default)]
    struct Table {
        sessions: HashMap<u64, Arc<Session>>,
        next: u64,
    }

    static TABLE: Mutex<Option<Table>> = Mutex::new(None);

    fn with<T>(f: impl FnOnce(&mut Table) -> T) -> T {
        let mut guard = TABLE.lock().unwrap_or_else(|e| e.into_inner());
        f(guard.get_or_insert_with(Table::default))
    }

    fn session(id: u64) -> Result<Arc<Session>, Text> {
        with(|t| t.sessions.get(&id).cloned())
            .ok_or_else(|| Text::from(format!("no TLS session {id}")))
    }

    fn lock(s: &Session) -> std::sync::MutexGuard<'_, TlsStream<Socket>> {
        s.tls.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn failed(e: impl std::fmt::Display) -> Text {
        Text::from(e.to_string())
    }

    fn left(deadline: Option<i64>) -> Option<Duration> {
        deadline.map(|d| {
            let now = crate::stdlib::os_monotonic_ns();
            Duration::from_nanos(d.saturating_sub(now).max(0) as u64)
        })
    }

    fn waited(e: &io::Error) -> bool {
        matches!(
            e.kind(),
            ErrorKind::WouldBlock | ErrorKind::TimedOut | ErrorKind::Interrupted
        )
    }

    fn texts(items: Vec<Text>) -> Vec<String> {
        items.iter().map(|t| t.to_string()).collect()
    }

    fn alpn(items: Vec<Text>) -> Vec<Vec<u8>> {
        items.iter().map(|t| t.as_bytes().to_vec()).collect()
    }

    fn take(stream: u64) -> Result<Socket, Text> {
        tcp::take(stream).ok_or_else(|| {
            Text::from(format!(
                "no stream {stream}, or another task is reading or writing it"
            ))
        })
    }

    /// Runs the handshake by the deadline, then puts the session in the table.
    fn establish(
        mut t: TlsStream<Socket>,
        deadline: Option<i64>,
    ) -> Result<Option<Established>, Text> {
        while t.conn.is_handshaking() {
            let wait = match left(deadline) {
                Some(d) if d.is_zero() => return Ok(None),
                other => other,
            };
            t.sock.set_read_timeout(wait).map_err(failed)?;
            t.sock.set_write_timeout(wait).map_err(failed)?;
            match t.conn.complete_io(&mut t.sock) {
                Ok(_) => {}
                Err(e) if waited(&e) => {}
                Err(e) => return Err(Text::from(format!("TLS handshake: {e}"))),
            }
        }
        let ctl = t.sock.try_clone().map_err(failed)?;
        let protocol = t
            .alpn()
            .map(|p| String::from_utf8_lossy(p).into_owned())
            .unwrap_or_default();
        let sni = t.server_name().unwrap_or_default().to_owned();
        let peer = t.peer_certificate().map(<[u8]>::to_vec).unwrap_or_default();
        let id = with(|table| {
            let id = table.next;
            table.next += 1;
            table.sessions.insert(
                id,
                Arc::new(Session {
                    ready: tcp::Ready::default(),
                    tls: Mutex::new(t),
                    ctl,
                    read_shut: AtomicBool::new(false),
                    closed: AtomicBool::new(false),
                }),
            );
            id
        });
        Ok(Some((
            vec![
                Text::from(id.to_string()),
                Text::from(protocol),
                Text::from(sni),
            ],
            peer,
        )))
    }

    /// Answers a client's handshake on a stream. `names` holds each
    /// certificate's SNI names joined by `,` (empty for the default), and
    /// `pems` each certificate's chain and then its key; `client_roots`
    /// (empty for none) asks for a client certificate these roots sign.
    pub fn os_tls_accept_vec(
        stream: u64,
        names: Vec<Text>,
        pems: Vec<Bytes>,
        alpn_ids: Vec<Text>,
        client_roots: Bytes,
        deadline: Option<i64>,
    ) -> Result<Option<Established>, Text> {
        if pems.len() != names.len() * 2 {
            return Err(Text::from("each certificate needs its chain and its key"));
        }
        let certs = texts(names)
            .into_iter()
            .zip(pems.chunks(2))
            .map(|(names, pair)| ServerCert {
                names: names
                    .split(',')
                    .filter(|n| !n.is_empty())
                    .map(str::to_owned)
                    .collect(),
                chain_pem: pair[0].to_vec(),
                key_pem: pair[1].to_vec(),
            })
            .collect();
        let options = ServerOptions {
            certs,
            alpn: alpn(alpn_ids),
            client_roots: (!client_roots.is_empty()).then(|| client_roots.to_vec()),
        };
        let config = tls::server_config(&options).map_err(Text::from)?;
        let t = tls::server(config, take(stream)?).map_err(Text::from)?;
        establish(t, deadline)
    }

    /// Starts a handshake with `server_name` on a stream. `roots` is 0 for
    /// the system's, 1 for the system's and the CAs, 2 for the CAs alone;
    /// `pems` holds the CAs, the client certificate's chain and its key (each
    /// empty for none).
    pub fn os_tls_connect_vec(
        stream: u64,
        server_name: Text,
        roots: u64,
        pems: Vec<Bytes>,
        alpn_ids: Vec<Text>,
        deadline: Option<i64>,
    ) -> Result<Option<Established>, Text> {
        let [cas, chain, key] = <[Bytes; 3]>::try_from(pems)
            .map_err(|_| Text::from("the roots, the client chain and the client key"))?;
        let roots = match roots {
            0 => Roots::System,
            1 => Roots::SystemAnd(cas.to_vec()),
            _ => Roots::Only(cas.to_vec()),
        };
        let options = ClientOptions {
            roots,
            client_cert: (!chain.is_empty()).then(|| (chain.to_vec(), key.to_vec())),
            alpn: alpn(alpn_ids),
        };
        let config = tls::client_config(&options).map_err(Text::from)?;
        let t = tls::client(config, &server_name, take(stream)?).map_err(Text::from)?;
        establish(t, deadline)
    }

    /// Up to `max` bytes, as soon as any are decrypted; none at the peer's
    /// close_notify or after reading was shut down. A stream that ends
    /// without close_notify is an error.
    pub fn os_tls_read_vec(
        id: u64,
        max: u64,
        deadline: Option<i64>,
    ) -> Result<Option<Vec<u8>>, Text> {
        let s = session(id)?;
        let mut buf = vec![0; max.min(1 << 20) as usize];
        if buf.is_empty() {
            return Ok(Some(buf));
        }
        loop {
            if s.closed.load(Ordering::Acquire) || s.read_shut.load(Ordering::Acquire) {
                return Ok(Some(Vec::new()));
            }
            let wait = match left(deadline) {
                Some(d) if d.is_zero() => return Ok(None),
                Some(d) => d.min(READ_SLICE),
                None => READ_SLICE,
            };
            let mut t = lock(&s);
            let t = &mut *t;
            match t.conn.reader().read(&mut buf) {
                Ok(n) => {
                    buf.truncate(n);
                    return Ok(Some(buf));
                }
                Err(e) if e.kind() == ErrorKind::WouldBlock => {}
                Err(_) if s.read_shut.load(Ordering::Acquire) => return Ok(Some(Vec::new())),
                Err(e) if e.kind() == ErrorKind::UnexpectedEof => {
                    return Err(Text::from(
                        "the peer closed the stream without close_notify; the data may be cut short",
                    ));
                }
                Err(e) => return Err(failed(e)),
            }
            t.sock.set_read_timeout(Some(wait)).map_err(failed)?;
            match t.conn.read_tls(&mut t.sock) {
                Ok(_) => {
                    if let Err(e) = t.conn.process_new_packets() {
                        // Tell the peer why, as far as it will listen.
                        let _ = t.conn.write_tls(&mut t.sock);
                        return Err(failed(e));
                    }
                }
                Err(e) if waited(&e) => {}
                Err(_) if s.read_shut.load(Ordering::Acquire) => return Ok(Some(Vec::new())),
                Err(e) => return Err(failed(e)),
            }
        }
    }

    fn flush(
        t: &mut TlsStream<Socket>,
        s: &Session,
        deadline: Option<i64>,
    ) -> Result<Option<()>, Text> {
        while t.conn.wants_write() {
            if s.closed.load(Ordering::Acquire) {
                return Err(Text::from("the stream was closed"));
            }
            let wait = match left(deadline) {
                Some(d) if d.is_zero() => return Ok(None),
                other => other,
            };
            t.sock.set_write_timeout(wait).map_err(failed)?;
            match t.conn.write_tls(&mut t.sock) {
                Ok(_) => {}
                Err(e) if waited(&e) => {}
                Err(e) => return Err(failed(e)),
            }
        }
        Ok(Some(()))
    }

    /// Writes all of `bytes`. `Ok(None)` when the deadline passes first; some
    /// of the bytes may have been sent by then.
    pub fn os_tls_write_vec(
        id: u64,
        bytes: Vec<u8>,
        deadline: Option<i64>,
    ) -> Result<Option<()>, Text> {
        let s = session(id)?;
        let mut t = lock(&s);
        let mut at = 0;
        while at < bytes.len() {
            let n = t.conn.writer().write(&bytes[at..]).map_err(failed)?;
            at += n;
            if flush(&mut t, &s, deadline)?.is_none() {
                return Ok(None);
            }
        }
        // What an earlier `os_tls_send` left is sent too.
        flush(&mut t, &s, deadline)
    }

    /// The socket as a writer that does not wait: a full socket is
    /// `WouldBlock`.
    struct NoWait<'a>(&'a Socket);

    impl Write for NoWait<'_> {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            tcp::send_now(self.0, buf)
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    /// Sends the session's records that wait, as far as the socket takes
    /// them now: whether none is left.
    fn flush_now(t: &mut TlsStream<Socket>) -> Result<bool, Text> {
        while t.conn.wants_write() {
            match t.conn.write_tls(&mut NoWait(&t.sock)) {
                Ok(_) => {}
                Err(e) if e.kind() == ErrorKind::WouldBlock => return Ok(false),
                Err(e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return Err(failed(e)),
            }
        }
        Ok(true)
    }

    /// Takes what of `bytes` the session takes now and sends what the
    /// socket takes, without waiting: how many of `bytes` it took. It takes
    /// none while records of an earlier send still wait. With no bytes, it
    /// sends what waits and answers 0 once nothing is left, else 1.
    /// `Ok(None)` when nothing could go and `deadline` has passed. A host
    /// that waits on the poller (`exec::os_tls_ready`) sends a long write a
    /// piece at a time this way, so the write holds no thread.
    pub fn os_tls_send_vec(
        id: u64,
        bytes: &[u8],
        deadline: Option<i64>,
    ) -> Result<Option<u64>, Text> {
        let s = session(id)?;
        let mut t = lock(&s);
        if s.closed.load(Ordering::Acquire) {
            return Err(Text::from("the stream was closed"));
        }
        let passed = left(deadline).is_some_and(|d| d.is_zero());
        let sent = flush_now(&mut t)?;
        if bytes.is_empty() {
            return Ok(match (sent, passed) {
                (true, _) => Some(0),
                (false, true) => None,
                (false, false) => Some(1),
            });
        }
        if !sent {
            return Ok(if passed { None } else { Some(0) });
        }
        let n = t.conn.writer().write(bytes).map_err(failed)?;
        flush_now(&mut t)?;
        Ok(Some(n as u64))
    }

    pub fn os_tls_send(id: u64, bytes: Bytes, deadline: Option<i64>) -> Result<Option<u64>, Text> {
        os_tls_send_vec(id, &bytes, deadline)
    }

    #[cfg(all(unix, feature = "reactor"))]
    impl tcp::Watched for Session {
        fn ready(&self) -> &tcp::Ready {
            &self.ready
        }
        fn descriptor(&self) -> std::os::fd::BorrowedFd<'_> {
            use std::os::fd::AsFd;
            match &self.ctl {
                Socket::Tcp(c) => c.as_fd(),
                Socket::Unix(c) => c.as_fd(),
            }
        }
        fn closed(&self) -> bool {
            self.closed.load(Ordering::Acquire) || self.read_shut.load(Ordering::Acquire)
        }
        /// A read does not wait when the session already holds decrypted
        /// bytes or the peer's close, though the socket has nothing new.
        fn now(&self, write: bool) -> bool {
            if write {
                return tcp::polled(self.descriptor(), true);
            }
            // A session another task holds is read soon after.
            let Ok(mut t) = self.tls.try_lock() else {
                return true;
            };
            match t.conn.process_new_packets() {
                Ok(state) if state.plaintext_bytes_to_read() > 0 || state.peer_has_closed() => true,
                Ok(_) => {
                    drop(t);
                    tcp::polled(self.descriptor(), false)
                }
                Err(_) => true,
            }
        }
    }

    /// The wait of `exec::os_tls_ready` on the session `id`. `None` when no
    /// session has the number: the operation that follows says so.
    #[cfg(all(unix, feature = "reactor"))]
    pub(crate) fn ready(id: u64, write: bool, deadline: Option<i64>) -> Option<tcp::Wait> {
        let s = with(|t| t.sessions.get(&id).cloned())?;
        Some(tcp::wait(s, write, deadline, false))
    }

    pub fn os_tls_read(id: u64, max: u64, deadline: Option<i64>) -> Result<Option<Bytes>, Text> {
        os_tls_read_vec(id, max, deadline).map(|b| b.map(Into::into))
    }

    pub fn os_tls_write(id: u64, bytes: Bytes, deadline: Option<i64>) -> Result<Option<()>, Text> {
        os_tls_write_vec(id, bytes.to_vec(), deadline)
    }

    /// Ends reading (0), writing (1) or both (2). Ending writing sends
    /// close_notify first, so the peer sees a clean end; ending reading wakes
    /// a read waiting in another task.
    pub fn os_tls_shutdown(id: u64, how: u64) -> Result<(), Text> {
        let s = session(id)?;
        if how != 1 {
            s.read_shut.store(true, Ordering::Release);
            s.ready.wake();
        }
        if how != 0 {
            let mut t = lock(&s);
            t.conn.send_close_notify();
            flush(&mut t, &s, None)?;
        }
        let how = match how {
            0 => Shutdown::Read,
            1 => Shutdown::Write,
            _ => Shutdown::Both,
        };
        match s.ctl.shutdown(how) {
            Err(e) if e.kind() == ErrorKind::NotConnected => Ok(()),
            r => r.map_err(failed),
        }
    }

    /// Sends close_notify when no other task holds the session, then closes
    /// the socket: a wait on it in another task ends, and the number no
    /// longer names it. Closing one closed already does nothing.
    pub fn os_tls_close(id: u64) {
        let Some(s) = with(|t| t.sessions.remove(&id)) else {
            return;
        };
        if let Ok(mut t) = s.tls.try_lock() {
            let t = &mut *t;
            t.conn.send_close_notify();
            let _ = t.sock.set_write_timeout(Some(READ_SLICE));
            while t.conn.wants_write() && t.conn.write_tls(&mut t.sock).is_ok() {}
            let _ = t.sock.flush();
        }
        s.closed.store(true, Ordering::Release);
        s.ready.wake();
        let _ = s.ctl.shutdown(Shutdown::Both);
    }

    /// Closes every session, as `tauto dev` does between runs: a read or write
    /// waiting on one ends.
    pub fn drop_sessions() {
        for (_, s) in with(|t| std::mem::take(&mut t.sessions)) {
            s.closed.store(true, Ordering::Release);
            s.ready.wake();
            let _ = s.ctl.shutdown(Shutdown::Both);
        }
    }
}
