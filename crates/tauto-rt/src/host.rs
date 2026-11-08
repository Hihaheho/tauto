//! Who answers the standard effects that reach the top of the program
//! (`docs/design/host-effects.md`): the `os_*` functions of [`crate::stdlib`]
//! ask the [`Host`] of the process, after the permission check.
//!
//! On a target with an operating system (and on `wasm32-wasip1`, whose WASI
//! host gives the standard library its files, clocks and streams) the host is
//! [`System`]. On `wasm32-unknown-unknown` there is no system to ask: the host
//! is [`Absent`] until the embedder (a page's glue code) installs its own with
//! [`set`]. The absent host answers no request; nothing reaches the outside
//! that the embedder did not wire up.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};

/// Why the host did not answer a request. The kind is the variant and what
/// it names is its fields, so a caller tells failures apart without reading
/// text; the text in [`HostError::Io`] is the operating system's own.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostError {
    /// This build has no host for the request: the embedder installs one
    /// with [`set`].
    Absent { what: &'static str },
    /// The operating system's refusal, as it words it.
    Io(String),
    /// A directory entry whose name is not UTF-8.
    NotUtf8 { name: String },
    /// No new temporary directory could be made.
    NoTempDir,
    /// The program could not be started.
    Spawn { program: String, error: String },
    /// A path for [`Host::read_bytes_under`] that is not names under the
    /// root.
    NotUnder { path: String },
}

/// The components of a path under a root: relative names joined by `/`,
/// none empty, `.` or `..`, and no NUL.
pub fn under_parts(path: &str) -> Result<Vec<&str>, HostError> {
    let parts: Vec<&str> = path.split('/').collect();
    if path.contains('\0')
        || parts
            .iter()
            .any(|p| p.is_empty() || *p == "." || *p == "..")
    {
        return Err(HostError::NotUnder {
            path: path.to_string(),
        });
    }
    Ok(parts)
}

/// Opens each component from the one before with `O_NOFOLLOW`, so the read
/// stays under `root` whatever is renamed or linked meanwhile.
#[cfg(unix)]
pub fn read_bytes_under(root: &str, path: &str) -> Result<Vec<u8>, HostError> {
    use rustix::fs::{Mode, OFlags, openat};
    use std::io::Read;
    let parts = under_parts(path)?;
    let mut at = std::os::fd::OwnedFd::from(std::fs::File::open(root)?);
    if !std::fs::File::from(at.try_clone()?).metadata()?.is_dir() {
        return Err(HostError::Io(format!("{root}: not a directory")));
    }
    for (index, part) in parts.iter().enumerate() {
        let last = index + 1 == parts.len();
        let flags = OFlags::RDONLY
            | OFlags::CLOEXEC
            | OFlags::NOFOLLOW
            | OFlags::NONBLOCK
            | if last {
                OFlags::empty()
            } else {
                OFlags::DIRECTORY
            };
        at = openat(&at, *part, flags, Mode::empty())
            .map_err(|e| HostError::Io(format!("{path}: {}", std::io::Error::from(e))))?;
    }
    let mut file = std::fs::File::from(at);
    if !file.metadata()?.is_file() {
        return Err(HostError::Io(format!("{path}: not a file")));
    }
    let mut out = Vec::new();
    file.read_to_end(&mut out)?;
    Ok(out)
}

impl From<std::io::Error> for HostError {
    fn from(e: std::io::Error) -> HostError {
        HostError::Io(e.to_string())
    }
}

impl std::fmt::Display for HostError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HostError::Absent { what } => write!(
                f,
                "this build has no host for {what}: the embedder installs one with tauto_rt::host::set"
            ),
            HostError::Io(e) => f.write_str(e),
            HostError::NotUtf8 { name } => write!(f, "{name}: a name that is not UTF-8"),
            HostError::NoTempDir => f.write_str("could not make a temporary directory"),
            HostError::Spawn { program, error } => write!(f, "{program}: {error}"),
            HostError::NotUnder { path } => write!(
                f,
                "{path}: not a path of names under the root (empty, absolute, `.` or `..`)"
            ),
        }
    }
}

impl std::error::Error for HostError {}

impl From<HostError> for crate::Text {
    fn from(e: HostError) -> crate::Text {
        crate::Text::from(e.to_string())
    }
}

/// The answers of the host. A method answers only after the permission of
/// its kind covered the request: the host need not check again.
pub trait Host: Send + Sync {
    fn stdout(&self, t: &str);
    fn stderr(&self, t: &str);
    /// One line without its line break; `None` at the end.
    fn read_line(&self) -> Option<String>;
    /// Up to `max` bytes of standard input as soon as any arrive; none at
    /// its end. A host without standard input has none.
    fn read_stdin(&self, max: usize) -> Vec<u8> {
        let _ = max;
        Vec::new()
    }
    /// Writes out what standard output and error were given.
    fn flush(&self) {}
    fn read_file(&self, path: &str) -> Result<String, HostError>;
    fn write_file(&self, path: &str, contents: &str) -> Result<(), HostError>;
    /// The bytes of a file. A host that answers only text leaves this out
    /// and fails the request.
    fn read_bytes(&self, path: &str) -> Result<Vec<u8>, HostError> {
        let _ = path;
        Err(absent("fs_read_bytes"))
    }
    fn write_bytes(&self, path: &str, contents: &[u8]) -> Result<(), HostError> {
        let _ = (path, contents);
        Err(absent("fs_write_bytes"))
    }
    /// The bytes of the file at `path` under the directory `root`, never
    /// leaving it: `path` is relative and made of names (no `.` or `..`),
    /// and no component, the file included, may be a link. Each component
    /// is opened from the descriptor of the one before, so a link or a
    /// rename made meanwhile cannot lead the read outside `root`.
    fn read_bytes_under(&self, root: &str, path: &str) -> Result<Vec<u8>, HostError> {
        let _ = (root, path);
        Err(absent("fs_read_under"))
    }
    /// Makes a directory and its missing parents; one already there is fine.
    fn create_dir(&self, path: &str) -> Result<(), HostError> {
        let _ = path;
        Err(absent("fs_create_dir"))
    }
    /// The names under a directory, in byte order.
    fn list_dir(&self, path: &str) -> Result<Vec<String>, HostError> {
        let _ = path;
        Err(absent("fs_list_dir"))
    }
    /// Removes a file, or a directory and all it holds.
    fn remove(&self, path: &str) -> Result<(), HostError> {
        let _ = path;
        Err(absent("fs_remove"))
    }
    /// What is at a path (links followed): `None` when nothing is.
    fn stat(&self, path: &str) -> Result<Option<Stat>, HostError> {
        let _ = path;
        Err(absent("fs_stat"))
    }
    /// Moves a file or directory; a file at `to` is replaced.
    fn rename(&self, from: &str, to: &str) -> Result<(), HostError> {
        let _ = (from, to);
        Err(absent("fs_rename"))
    }
    /// Where the link at `path` points, without following it; `None` when what is there is not
    /// a link, or nothing is.
    fn read_link(&self, path: &str) -> Result<Option<String>, HostError> {
        let _ = path;
        Err(absent("fs_read_link"))
    }
    /// Makes a file with `contents` where nothing is: it fails when anything is there, a link
    /// (even one that points at nothing) among it, and never writes through one.
    fn create_new(&self, path: &str, contents: &[u8]) -> Result<(), HostError> {
        let _ = (path, contents);
        Err(absent("fs_write_new"))
    }
    /// Copies a file's contents to `to`, replacing a file there.
    fn copy(&self, from: &str, to: &str) -> Result<(), HostError> {
        let _ = (from, to);
        Err(absent("fs_copy"))
    }
    /// The absolute path of what exists, links followed.
    fn canonicalize(&self, path: &str) -> Result<String, HostError> {
        let _ = path;
        Err(absent("fs_canonicalize"))
    }
    /// Makes a new empty directory for temporary files; its path.
    fn temp_dir(&self) -> Result<String, HostError> {
        Err(absent("fs_temp_dir"))
    }
    /// Runs a program to its end: its exit status (`None` when a signal
    /// ended it), standard output and standard error.
    fn run(&self, process: &Process) -> Result<(Option<i32>, Vec<u8>, Vec<u8>), HostError> {
        let _ = process;
        Err(absent("proc_run"))
    }
    fn env(&self, name: &str) -> Option<String>;
    /// Milliseconds since the Unix epoch.
    fn wall_ms(&self) -> i64;
    /// Nanoseconds that never go back.
    fn monotonic_ns(&self) -> i64;
    fn sleep(&self, ms: u64);
    /// Random bits, not for secrets (the program sees the top 63).
    fn random(&self) -> u64;
    /// `n` bytes from a cryptographically secure random source.
    fn secure_random(&self, n: usize) -> Result<Vec<u8>, HostError> {
        let _ = n;
        Err(absent("secure_random"))
    }
    /// Ends the run with `code` (0 to 255).
    fn exit(&self, code: i32) -> !;
}

/// What [`Host::stat`] knows of a path: `kind` is `file`, `dir` or `other`,
/// `modified_ms` is milliseconds since the Unix epoch (0 when unknown).
pub struct Stat {
    pub kind: &'static str,
    pub size: u64,
    pub modified_ms: u64,
}

/// A program to run ([`Host::run`]): its name or path, its arguments, the
/// directory it runs in (`None`: the process's own), the variables set on
/// top of the environment, and its standard input.
pub struct Process {
    pub program: String,
    pub args: Vec<String>,
    pub dir: Option<String>,
    pub env: Vec<(String, String)>,
    pub stdin: Vec<u8>,
}

pub struct System;

impl Host for System {
    fn stdout(&self, t: &str) {
        use std::io::Write;
        let _ = std::io::stdout().write_all(t.as_bytes());
    }

    fn stderr(&self, t: &str) {
        use std::io::Write;
        let _ = std::io::stderr().write_all(t.as_bytes());
    }

    fn read_line(&self) -> Option<String> {
        use std::io::{BufRead, Write};
        let _ = std::io::stdout().flush();
        let mut line = String::new();
        match std::io::stdin().lock().read_line(&mut line) {
            Ok(0) | Err(_) => None,
            Ok(_) => {
                if line.ends_with('\n') {
                    line.pop();
                    if line.ends_with('\r') {
                        line.pop();
                    }
                }
                Some(line)
            }
        }
    }

    fn read_stdin(&self, max: usize) -> Vec<u8> {
        use std::io::{BufRead, Write};
        let _ = std::io::stdout().flush();
        let stdin = std::io::stdin();
        let mut lock = stdin.lock();
        let got = match lock.fill_buf() {
            Ok(buf) => buf[..buf.len().min(max)].to_vec(),
            Err(_) => Vec::new(),
        };
        lock.consume(got.len());
        got
    }

    fn flush(&self) {
        use std::io::Write;
        let _ = std::io::stdout().flush();
        let _ = std::io::stderr().flush();
    }

    fn read_file(&self, path: &str) -> Result<String, HostError> {
        std::fs::read_to_string(path).map_err(HostError::from)
    }

    fn write_file(&self, path: &str, contents: &str) -> Result<(), HostError> {
        std::fs::write(path, contents.as_bytes()).map_err(HostError::from)
    }

    fn read_bytes(&self, path: &str) -> Result<Vec<u8>, HostError> {
        std::fs::read(path).map_err(HostError::from)
    }

    fn write_bytes(&self, path: &str, contents: &[u8]) -> Result<(), HostError> {
        std::fs::write(path, contents).map_err(HostError::from)
    }

    fn create_dir(&self, path: &str) -> Result<(), HostError> {
        std::fs::create_dir_all(path).map_err(HostError::from)
    }

    fn list_dir(&self, path: &str) -> Result<Vec<String>, HostError> {
        let mut names = Vec::new();
        for entry in std::fs::read_dir(path).map_err(HostError::from)? {
            let name = entry.map_err(HostError::from)?.file_name();
            match name.into_string() {
                Ok(name) => names.push(name),
                Err(name) => {
                    return Err(HostError::NotUtf8 {
                        name: name.to_string_lossy().into_owned(),
                    });
                }
            }
        }
        names.sort();
        Ok(names)
    }

    fn remove(&self, path: &str) -> Result<(), HostError> {
        let meta = std::fs::symlink_metadata(path).map_err(HostError::from)?;
        if meta.is_dir() {
            std::fs::remove_dir_all(path)
        } else {
            std::fs::remove_file(path)
        }
        .map_err(HostError::from)
    }

    fn stat(&self, path: &str) -> Result<Option<Stat>, HostError> {
        let meta = match std::fs::metadata(path) {
            Ok(meta) => meta,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(HostError::from(e)),
        };
        let kind = if meta.is_dir() {
            "dir"
        } else if meta.is_file() {
            "file"
        } else {
            "other"
        };
        let modified_ms = meta
            .modified()
            .ok()
            .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
            .map_or(0, |d| d.as_millis() as u64);
        Ok(Some(Stat {
            kind,
            size: meta.len(),
            modified_ms,
        }))
    }

    fn read_bytes_under(&self, root: &str, path: &str) -> Result<Vec<u8>, HostError> {
        #[cfg(unix)]
        {
            read_bytes_under(root, path)
        }
        #[cfg(not(unix))]
        {
            under_parts(path)?;
            let _ = root;
            Err(HostError::Io(
                "fs_read_under: this system cannot open a path without following links".into(),
            ))
        }
    }

    fn rename(&self, from: &str, to: &str) -> Result<(), HostError> {
        std::fs::rename(from, to).map_err(HostError::from)
    }

    fn read_link(&self, path: &str) -> Result<Option<String>, HostError> {
        match std::fs::symlink_metadata(path) {
            Ok(meta) if meta.file_type().is_symlink() => std::fs::read_link(path)
                .map(|target| Some(target.to_string_lossy().into_owned()))
                .map_err(HostError::from),
            Ok(_) => Ok(None),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(HostError::from(e)),
        }
    }

    fn create_new(&self, path: &str, contents: &[u8]) -> Result<(), HostError> {
        use std::io::Write;
        std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .and_then(|mut file| file.write_all(contents))
            .map_err(HostError::from)
    }

    fn copy(&self, from: &str, to: &str) -> Result<(), HostError> {
        std::fs::copy(from, to).map(|_| ()).map_err(HostError::from)
    }

    fn canonicalize(&self, path: &str) -> Result<String, HostError> {
        std::fs::canonicalize(path)
            .map(|p| p.to_string_lossy().into_owned())
            .map_err(HostError::from)
    }

    fn temp_dir(&self) -> Result<String, HostError> {
        let base = std::env::temp_dir();
        for _ in 0..16 {
            let dir = base.join(format!(
                "tauto-{}-{:016x}",
                std::process::id(),
                self.random()
            ));
            match std::fs::create_dir(&dir) {
                Ok(()) => return Ok(dir.to_string_lossy().into_owned()),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(HostError::from(e)),
            }
        }
        Err(HostError::NoTempDir)
    }

    fn run(&self, process: &Process) -> Result<(Option<i32>, Vec<u8>, Vec<u8>), HostError> {
        use std::io::Write;
        use std::process::{Command, Stdio};
        let _ = std::io::stdout().flush();
        let mut command = Command::new(&process.program);
        command
            .args(&process.args)
            .envs(process.env.iter().map(|(k, v)| (k, v)))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        if let Some(dir) = &process.dir {
            command.current_dir(dir);
        }
        let mut child = command.spawn().map_err(|e| HostError::Spawn {
            program: process.program.clone(),
            error: e.to_string(),
        })?;
        // Written from another thread: a child that fills its output before
        // it reads all its input would otherwise wait on us forever.
        let mut stdin = child.stdin.take();
        let input = process.stdin.clone();
        let writer = std::thread::spawn(move || {
            if let Some(s) = stdin.as_mut() {
                let _ = s.write_all(&input);
            }
        });
        let out = child.wait_with_output().map_err(HostError::from)?;
        let _ = writer.join();
        Ok((out.status.code(), out.stdout, out.stderr))
    }

    fn env(&self, name: &str) -> Option<String> {
        std::env::var(name).ok()
    }

    fn wall_ms(&self) -> i64 {
        match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
            Ok(d) => i64::try_from(d.as_millis()).unwrap_or(i64::MAX),
            Err(e) => -i64::try_from(e.duration().as_millis()).unwrap_or(i64::MAX),
        }
    }

    fn monotonic_ns(&self) -> i64 {
        static START: OnceLock<std::time::Instant> = OnceLock::new();
        let start = START.get_or_init(std::time::Instant::now);
        i64::try_from(start.elapsed().as_nanos()).unwrap_or(i64::MAX)
    }

    fn sleep(&self, ms: u64) {
        use std::io::Write;
        let _ = std::io::stdout().flush();
        std::thread::sleep(std::time::Duration::from_millis(ms));
    }

    /// The standard library's hash keys, which the system seeds, stirred
    /// with a count and the clock.
    fn random(&self) -> u64 {
        use std::hash::{BuildHasher, Hasher};
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNT: AtomicU64 = AtomicU64::new(0);
        let mut h = std::collections::hash_map::RandomState::new().build_hasher();
        h.write_u64(COUNT.fetch_add(1, Ordering::Relaxed));
        h.write_u64(self.monotonic_ns() as u64);
        h.finish()
    }

    /// The operating system's random source. A bare
    /// `wasm32-unknown-unknown` has none, and keeps the default.
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    fn secure_random(&self, n: usize) -> Result<Vec<u8>, HostError> {
        let mut bytes = vec![0; n];
        getrandom::fill(&mut bytes).map_err(|e| HostError::Io(e.to_string()))?;
        Ok(bytes)
    }

    fn exit(&self, code: i32) -> ! {
        use std::io::Write;
        let _ = std::io::stdout().flush();
        std::process::exit(code)
    }
}

/// No host: what `wasm32-unknown-unknown` has until the embedder sets one.
/// A request that can fail fails (`Failed`, or the end of the input); one
/// that cannot is a run-time error naming the effect. Nothing is answered
/// with a made-up value, such as a clock that reads 0.
pub struct Absent;

fn absent(what: &'static str) -> HostError {
    HostError::Absent { what }
}

impl Host for Absent {
    fn stdout(&self, _: &str) {
        crate::error_here(absent("stdout").to_string())
    }

    fn stderr(&self, _: &str) {
        crate::error_here(absent("stderr").to_string())
    }

    fn read_line(&self) -> Option<String> {
        None
    }

    fn read_file(&self, _: &str) -> Result<String, HostError> {
        Err(absent("fs_read"))
    }

    fn write_file(&self, _: &str, _: &str) -> Result<(), HostError> {
        Err(absent("fs_write"))
    }

    fn env(&self, _: &str) -> Option<String> {
        None
    }

    fn wall_ms(&self) -> i64 {
        crate::error_here(absent("wall_clock").to_string())
    }

    fn monotonic_ns(&self) -> i64 {
        crate::error_here(absent("monotonic_clock").to_string())
    }

    fn sleep(&self, _: u64) {
        crate::error_here(absent("sleep").to_string())
    }

    fn random(&self) -> u64 {
        crate::error_here(absent("random").to_string())
    }

    fn exit(&self, code: i32) -> ! {
        std::panic::panic_any(Exit(code))
    }
}

/// The payload of an `exit` that has no process to end: [`crate::run_embedded`]
/// reads it as the end of the run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Exit(pub i32);

pub const HAS_SYSTEM: bool = !cfg!(all(target_family = "wasm", target_os = "unknown"));

static HOST: OnceLock<Box<dyn Host>> = OnceLock::new();
static INSTALLED: AtomicBool = AtomicBool::new(false);

/// Installs the host of the process, before the program runs; `false` if
/// one is already in place (set, or used). Calling this while a Tauto program
/// is running panics.
pub fn set(host: Box<dyn Host>) -> bool {
    crate::with_config_lock("host::set", || {
        let fresh = HOST.set(host).is_ok();
        if fresh {
            INSTALLED.store(true, Ordering::Release);
        }
        fresh
    })
}

/// Writes the report of a run that failed: to the standard error of the
/// installed host, else of the system; nowhere when there is neither.
pub(crate) fn report(text: &str) {
    if INSTALLED.load(Ordering::Acquire) {
        get().stderr(text);
    } else if HAS_SYSTEM {
        System.stderr(text);
    }
}

/// The host of the process: the one [`set`] installed, else [`System`] where
/// there is a system and [`Absent`] where there is none.
pub fn get() -> &'static dyn Host {
    HOST.get_or_init(|| {
        if HAS_SYSTEM {
            Box::new(System)
        } else {
            Box::new(Absent)
        }
    })
    .as_ref()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    /// A link anywhere on the way, the file included, stops the read; the
    /// same file without the link is read. Programs cannot make links, so
    /// this is checked here and not in a case.
    #[cfg(unix)]
    #[test]
    fn a_read_under_a_root_refuses_links() {
        let base = std::env::temp_dir().join(format!("tauto-rt-under-{}", std::process::id()));
        let root = base.join("root");
        std::fs::create_dir_all(root.join("sub")).unwrap();
        std::fs::write(root.join("sub/a.txt"), "abc").unwrap();
        std::fs::write(base.join("out.txt"), "out").unwrap();
        std::os::unix::fs::symlink(base.join("out.txt"), root.join("file-link")).unwrap();
        std::os::unix::fs::symlink(&base, root.join("dir-link")).unwrap();
        let root = root.to_str().unwrap();
        assert_eq!(read_bytes_under(root, "sub/a.txt").unwrap(), b"abc");
        assert!(read_bytes_under(root, "file-link").is_err());
        assert!(read_bytes_under(root, "dir-link/out.txt").is_err());
        assert!(matches!(
            read_bytes_under(root, "sub/../sub/a.txt"),
            Err(HostError::NotUnder { .. })
        ));
        std::fs::remove_dir_all(&base).unwrap();
    }

    static OUT: Mutex<String> = Mutex::new(String::new());

    /// An embedder's host: it keeps what the program writes, and has no
    /// files.
    struct Page;

    impl Host for Page {
        fn stdout(&self, t: &str) {
            OUT.lock().unwrap().push_str(t);
        }
        fn stderr(&self, t: &str) {
            OUT.lock().unwrap().push_str(&format!("[err]{t}"));
        }
        fn read_line(&self) -> Option<String> {
            None
        }
        fn read_file(&self, _: &str) -> Result<String, HostError> {
            Err(HostError::Io("no files on this page".into()))
        }
        fn write_file(&self, _: &str, _: &str) -> Result<(), HostError> {
            Err(HostError::Io("no files on this page".into()))
        }
        fn env(&self, _: &str) -> Option<String> {
            None
        }
        fn wall_ms(&self) -> i64 {
            7
        }
        fn monotonic_ns(&self) -> i64 {
            8
        }
        fn sleep(&self, _: u64) {}
        fn random(&self) -> u64 {
            u64::MAX
        }
        fn exit(&self, code: i32) -> ! {
            std::panic::panic_any(Exit(code))
        }
    }

    #[test]
    fn a_failure_is_told_by_its_kind_not_its_text() {
        assert_eq!(
            Absent.read_file("x"),
            Err(HostError::Absent { what: "fs_read" })
        );
        assert_eq!(
            Absent.read_bytes("x"),
            Err(HostError::Absent {
                what: "fs_read_bytes"
            })
        );
        assert!(matches!(
            System.read_file("/nonexistent/tauto-host-test"),
            Err(HostError::Io(_))
        ));
        let spawn = System.run(&Process {
            program: "/nonexistent/tauto-host-test".into(),
            args: Vec::new(),
            dir: None,
            env: Vec::new(),
            stdin: Vec::new(),
        });
        assert!(matches!(spawn, Err(HostError::Spawn { .. })));
    }

    const AT: crate::Loc = crate::Loc {
        file: "m",
        line: 1,
        col: 1,
    };

    // One test, since the host is the process's.
    #[test]
    fn an_embedded_run_asks_the_installed_host() {
        assert!(set(Box::new(Page)));
        assert!(!set(Box::new(Absent)));
        crate::permissions::set(crate::permissions::Permissions::all());
        crate::stdlib::set_args(vec!["before".into()]);
        let old_steps = crate::swap_steps(41);
        let old_budget_steps = crate::budget::STEPS.swap(37, Ordering::Relaxed);
        let ok = crate::run_embedded(Default::default(), vec!["a".into()], || {
            assert_eq!(crate::swap_steps(100), 0);
            crate::budget::STEPS.store(200, Ordering::Relaxed);
            crate::stdlib::os_print("hi".into());
            assert_eq!(crate::stdlib::os_wall_ms(), 7);
            assert_eq!(crate::stdlib::os_random(), u64::MAX >> 1);
            assert_eq!(crate::stdlib::os_args_vec(), vec![crate::Text::from("a")]);
            assert!(crate::stdlib::os_read_file("x".into()).is_err());
            crate::stdlib::os_exit(0, AT);
        });
        assert_eq!(ok, Ok(()));
        assert_eq!(crate::swap_steps(old_steps), 41);
        assert_eq!(
            crate::budget::STEPS.swap(old_budget_steps, Ordering::Relaxed),
            37
        );
        assert_eq!(
            crate::permissions::current(),
            crate::permissions::Permissions::all()
        );
        assert_eq!(
            crate::stdlib::os_args_vec(),
            vec![crate::Text::from("before")]
        );
        let assert_restored = || {
            assert_eq!(
                crate::permissions::current(),
                crate::permissions::Permissions::all()
            );
            assert_eq!(
                crate::stdlib::os_args_vec(),
                vec![crate::Text::from("before")]
            );
        };
        let failed = crate::run_embedded(Default::default(), vec![], || {
            crate::stdlib::os_exit(4, AT);
        });
        assert_eq!(failed, Err("exit 4".to_string()));
        assert_restored();
        let error = crate::run_embedded(Default::default(), vec![], || {
            crate::error_here("boom");
        });
        assert_eq!(error, Err("boom".to_string()));
        assert_restored();
        crate::set_step_limit(3);
        let limited = crate::run_embedded(Default::default(), vec![], || {
            crate::swap_steps(0);
            for _ in 0..4 {
                crate::host_tick(AT);
            }
        });
        crate::set_step_limit(0);
        assert!(limited.unwrap_err().contains("after 3 steps"));
        assert_restored();
        assert_eq!(*OUT.lock().unwrap(), "hi");

        let nested = crate::run_embedded(Default::default(), vec![], || {
            assert_eq!(
                crate::run_embedded(Default::default(), vec![], || {}),
                Err("the runtime is already in use".into())
            );
        });
        assert_eq!(nested, Ok(()));

        let original_hook = std::panic::take_hook();
        let hook_called = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let called = hook_called.clone();
        std::panic::set_hook(Box::new(move |_| {
            called.store(true, std::sync::atomic::Ordering::SeqCst);
        }));
        let panicked = crate::run_embedded(Default::default(), vec![], || {
            assert!(
                std::panic::catch_unwind(|| crate::stdlib::set_args(vec!["during".into()]))
                    .is_err()
            );
            panic!("embedded panic");
        });
        assert_eq!(panicked, Err("interrupted: embedded panic".into()));
        assert!(hook_called.load(std::sync::atomic::Ordering::SeqCst));
        assert_restored();
        std::panic::set_hook(original_hook);

        let (entered_tx, entered_rx) = std::sync::mpsc::channel();
        let (leave_tx, leave_rx) = std::sync::mpsc::channel();
        let first = std::thread::spawn(move || {
            crate::run_embedded(Default::default(), vec![], move || {
                entered_tx.send(()).unwrap();
                leave_rx.recv().unwrap();
            })
        });
        entered_rx.recv().unwrap();
        assert_eq!(
            crate::run_embedded(Default::default(), vec![], || {}),
            Err("the runtime is already in use".into())
        );
        leave_tx.send(()).unwrap();
        assert_eq!(first.join().unwrap(), Ok(()));

        crate::permissions::restore(None);
        crate::stdlib::restore_args(None);
    }
}
