//! Programs the run starts and goes on with while they run (`proc_spawn` and
//! its companions in `std/prelude/Os.taut`): a table of children by number,
//! as `tcp` keeps streams. Reading takes a deadline, a value of
//! `monotonic_clock`; a wait whose deadline passes first answers `None`.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{Receiver, RecvTimeoutError, channel};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

use crate::Text;
use crate::stdlib::Bytes;

/// What a child's standard stream is: 0 a pipe to this run, 1 the run's own.
fn stdio(mode: u64, input: bool) -> Stdio {
    match (mode, input) {
        (1, _) => Stdio::inherit(),
        _ => Stdio::piped(),
    }
}

/// What a pipe's reader thread gave: bytes, or an end (an empty chunk).
struct Pipe {
    chunks: Mutex<Receiver<Vec<u8>>>,
    /// Bytes a read left over when it asked for fewer than the chunk held.
    rest: Mutex<Vec<u8>>,
}

fn pump<R: Read + Send + 'static>(mut from: R) -> Pipe {
    let (tx, rx) = channel();
    std::thread::spawn(move || {
        let mut buf = vec![0; 1 << 16];
        loop {
            match from.read(&mut buf) {
                Ok(0) | Err(_) => {
                    let _ = tx.send(Vec::new());
                    return;
                }
                Ok(n) => {
                    if tx.send(buf[..n].to_vec()).is_err() {
                        return;
                    }
                }
            }
        }
    });
    Pipe {
        chunks: Mutex::new(rx),
        rest: Mutex::new(Vec::new()),
    }
}

struct Started {
    child: Mutex<Child>,
    stdin: Mutex<Option<ChildStdin>>,
    stdout: Option<Pipe>,
    stderr: Option<Pipe>,
}

#[derive(Default)]
struct Table {
    children: HashMap<u64, Arc<Started>>,
    next: u64,
}

fn table() -> &'static Mutex<Table> {
    static TABLE: OnceLock<Mutex<Table>> = OnceLock::new();
    TABLE.get_or_init(Mutex::default)
}

fn with<T>(f: impl FnOnce(&mut Table) -> T) -> T {
    f(&mut table().lock().unwrap_or_else(|e| e.into_inner()))
}

fn find(id: u64) -> Result<Arc<Started>, Text> {
    with(|t| t.children.get(&id).cloned()).ok_or_else(|| Text::from("no such program"))
}

/// The time left before a deadline (`monotonic_clock` nanoseconds); `None`
/// waits as long as it takes.
fn left(deadline: Option<i64>) -> Option<Duration> {
    deadline.map(|d| {
        let now = crate::stdlib::os_monotonic_ns();
        Duration::from_nanos((d - now).max(0) as u64)
    })
}

/// Starts a program. `modes` are the standard input's, output's and error's
/// (0 a pipe, 1 the run's own). What `stdin` holds is written to a piped
/// input first, which then stays open. The number of the child.
pub fn os_child_spawn_vec(
    program: Text,
    args: Vec<Text>,
    dir: Text,
    env: Vec<Text>,
    stdin: Bytes,
    modes: Vec<Text>,
) -> Result<Vec<Text>, Text> {
    let mode = |i: usize| modes.get(i).and_then(|m| m.parse().ok()).unwrap_or(0);
    let (m_in, m_out, m_err) = (mode(0), mode(1), mode(2));
    let program = crate::stdlib::run_program(&program);
    let mut command = Command::new(&program);
    command
        .args(args.iter().map(|a| a.to_string()))
        .stdin(stdio(m_in, true))
        .stdout(stdio(m_out, false))
        .stderr(stdio(m_err, false));
    for pair in env.chunks(2) {
        if let [k, v] = pair {
            command.env(k.to_string(), v.to_string());
        }
    }
    if !dir.is_empty() {
        command.current_dir(dir.to_string());
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        // Its own group, so Ctrl-C at the terminal reaches this run alone
        // and the run decides what happens to the child.
        command.process_group(0);
    }
    let mut child = command
        .spawn()
        .map_err(|e| Text::from(format!("{program}: {e}")))?;
    // The outputs are read before the input is written: a child that writes
    // much before it reads all its input does not wait on a full pipe.
    let stdout = child.stdout.take().map(pump);
    let stderr = child.stderr.take().map(pump);
    let mut stdin_pipe = child.stdin.take();
    if let Some(pipe) = stdin_pipe.as_mut() {
        if !stdin.to_vec().is_empty() {
            pipe.write_all(&stdin.to_vec())
                .map_err(|e| Text::from(e.to_string()))?;
        }
    }
    let started = Started {
        stdout,
        stderr,
        stdin: Mutex::new(stdin_pipe),
        child: Mutex::new(child),
    };
    let id = with(|t| {
        t.next += 1;
        let id = t.next;
        t.children.insert(id, Arc::new(started));
        id
    });
    Ok(vec![Text::from(id.to_string())])
}

/// Up to `max` bytes of a child's standard output (`which` 1) or error (2),
/// as soon as any arrive; none at the end. `Ok(None)` when the deadline
/// passes first. A stream that is not a pipe reads as already ended.
pub fn os_child_read_vec(
    id: u64,
    which: u64,
    max: u64,
    deadline: Option<i64>,
) -> Result<Option<Vec<u8>>, Text> {
    let started = find(id)?;
    let Some(pipe) = (if which == 2 {
        &started.stderr
    } else {
        &started.stdout
    }) else {
        return Ok(Some(Vec::new()));
    };
    let max = max.min(1 << 20) as usize;
    if max == 0 {
        return Ok(Some(Vec::new()));
    }
    let mut rest = pipe.rest.lock().unwrap_or_else(|e| e.into_inner());
    if rest.is_empty() {
        let chunks = pipe.chunks.lock().unwrap_or_else(|e| e.into_inner());
        let got = match left(deadline) {
            None => chunks.recv().map_err(|_| RecvTimeoutError::Disconnected),
            Some(d) => chunks.recv_timeout(d),
        };
        match got {
            Ok(chunk) => *rest = chunk,
            Err(RecvTimeoutError::Timeout) => return Ok(None),
            Err(RecvTimeoutError::Disconnected) => return Ok(Some(Vec::new())),
        }
        if rest.is_empty() {
            // The end: the sender is gone, so every later read ends too.
            return Ok(Some(Vec::new()));
        }
    }
    let n = rest.len().min(max);
    let out: Vec<u8> = rest.drain(..n).collect();
    Ok(Some(out))
}

/// `os_child_read_vec` as `Bytes`, as the prelude's extern takes it.
pub fn os_child_read(
    id: u64,
    which: u64,
    max: u64,
    deadline: Option<i64>,
) -> Result<Option<Bytes>, Text> {
    os_child_read_vec(id, which, max, deadline).map(|b| b.map(Into::into))
}

/// Writes all of `bytes` to a child's standard input.
pub fn os_child_write(id: u64, bytes: Bytes) -> Result<(), Text> {
    let started = find(id)?;
    let mut stdin = started.stdin.lock().unwrap_or_else(|e| e.into_inner());
    match stdin.as_mut() {
        Some(pipe) => pipe
            .write_all(&bytes.to_vec())
            .and_then(|()| pipe.flush())
            .map_err(|e| Text::from(e.to_string())),
        None => Err(Text::from("the standard input is closed")),
    }
}

/// Closes a child's standard input, so it reads an end.
pub fn os_child_close_stdin(id: u64) -> Result<(), Text> {
    let started = find(id)?;
    started
        .stdin
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .take();
    Ok(())
}

/// Waits for a child to end: empty when a signal ended it, else its exit
/// code. `Ok(None)` when the deadline passes first.
pub fn os_child_wait_vec(id: u64, deadline: Option<i64>) -> Result<Option<Vec<Text>>, Text> {
    let started = find(id)?;
    let start = Instant::now();
    loop {
        let status = started
            .child
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .try_wait()
            .map_err(|e| Text::from(e.to_string()))?;
        if let Some(status) = status {
            return Ok(Some(match status.code() {
                Some(code) => vec![Text::from(code.to_string())],
                None => Vec::new(),
            }));
        }
        if left(deadline).is_some_and(|d| d.is_zero()) {
            return Ok(None);
        }
        // A short sleep, backing off to 20 ms, as a wait on a process has no
        // portable wake-up that also takes a deadline.
        let waited = start.elapsed().as_millis().min(20) as u64;
        std::thread::sleep(Duration::from_millis(1 + waited / 2));
    }
}

/// Ends a child that still runs and forgets its number. A read or wait on
/// it in another task fails or ends.
pub fn os_child_close(id: u64) {
    if let Some(started) = with(|t| t.children.remove(&id)) {
        let mut child = started.child.lock().unwrap_or_else(|e| e.into_inner());
        if matches!(child.try_wait(), Ok(None)) {
            let _ = child.kill();
        }
        let _ = child.wait();
    }
}
