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
    fn read_file(&self, path: &str) -> Result<String, String>;
    fn write_file(&self, path: &str, contents: &str) -> Result<(), String>;
    /// The bytes of a file. A host that answers only text leaves this out
    /// and fails the request.
    fn read_bytes(&self, path: &str) -> Result<Vec<u8>, String> {
        let _ = path;
        Err(absent("fs_read_bytes"))
    }
    fn write_bytes(&self, path: &str, contents: &[u8]) -> Result<(), String> {
        let _ = (path, contents);
        Err(absent("fs_write_bytes"))
    }
    /// Makes a directory and its missing parents; one already there is fine.
    fn create_dir(&self, path: &str) -> Result<(), String> {
        let _ = path;
        Err(absent("fs_create_dir"))
    }
    /// The names under a directory, in byte order.
    fn list_dir(&self, path: &str) -> Result<Vec<String>, String> {
        let _ = path;
        Err(absent("fs_list_dir"))
    }
    /// Removes a file, or a directory and all it holds.
    fn remove(&self, path: &str) -> Result<(), String> {
        let _ = path;
        Err(absent("fs_remove"))
    }
    /// What is at a path (links followed): `None` when nothing is.
    fn stat(&self, path: &str) -> Result<Option<Stat>, String> {
        let _ = path;
        Err(absent("fs_stat"))
    }
    /// Moves a file or directory; a file at `to` is replaced.
    fn rename(&self, from: &str, to: &str) -> Result<(), String> {
        let _ = (from, to);
        Err(absent("fs_rename"))
    }
    /// Copies a file's contents to `to`, replacing a file there.
    fn copy(&self, from: &str, to: &str) -> Result<(), String> {
        let _ = (from, to);
        Err(absent("fs_copy"))
    }
    /// The absolute path of what exists, links followed.
    fn canonicalize(&self, path: &str) -> Result<String, String> {
        let _ = path;
        Err(absent("fs_canonicalize"))
    }
    /// Makes a new empty directory for temporary files; its path.
    fn temp_dir(&self) -> Result<String, String> {
        Err(absent("fs_temp_dir"))
    }
    /// Runs a program to its end: its exit status (`None` when a signal
    /// ended it), standard output and standard error.
    fn run(&self, process: &Process) -> Result<(Option<i32>, Vec<u8>, Vec<u8>), String> {
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
    fn secure_random(&self, n: usize) -> Result<Vec<u8>, String> {
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

    fn read_file(&self, path: &str) -> Result<String, String> {
        std::fs::read_to_string(path).map_err(|e| e.to_string())
    }

    fn write_file(&self, path: &str, contents: &str) -> Result<(), String> {
        std::fs::write(path, contents.as_bytes()).map_err(|e| e.to_string())
    }

    fn read_bytes(&self, path: &str) -> Result<Vec<u8>, String> {
        std::fs::read(path).map_err(|e| e.to_string())
    }

    fn write_bytes(&self, path: &str, contents: &[u8]) -> Result<(), String> {
        std::fs::write(path, contents).map_err(|e| e.to_string())
    }

    fn create_dir(&self, path: &str) -> Result<(), String> {
        std::fs::create_dir_all(path).map_err(|e| e.to_string())
    }

    fn list_dir(&self, path: &str) -> Result<Vec<String>, String> {
        let mut names = Vec::new();
        for entry in std::fs::read_dir(path).map_err(|e| e.to_string())? {
            let name = entry.map_err(|e| e.to_string())?.file_name();
            match name.into_string() {
                Ok(name) => names.push(name),
                Err(name) => {
                    return Err(format!(
                        "{}: a name that is not UTF-8",
                        name.to_string_lossy()
                    ));
                }
            }
        }
        names.sort();
        Ok(names)
    }

    fn remove(&self, path: &str) -> Result<(), String> {
        let meta = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
        if meta.is_dir() {
            std::fs::remove_dir_all(path)
        } else {
            std::fs::remove_file(path)
        }
        .map_err(|e| e.to_string())
    }

    fn stat(&self, path: &str) -> Result<Option<Stat>, String> {
        let meta = match std::fs::metadata(path) {
            Ok(meta) => meta,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e.to_string()),
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

    fn rename(&self, from: &str, to: &str) -> Result<(), String> {
        std::fs::rename(from, to).map_err(|e| e.to_string())
    }

    fn copy(&self, from: &str, to: &str) -> Result<(), String> {
        std::fs::copy(from, to)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    fn canonicalize(&self, path: &str) -> Result<String, String> {
        std::fs::canonicalize(path)
            .map(|p| p.to_string_lossy().into_owned())
            .map_err(|e| e.to_string())
    }

    fn temp_dir(&self) -> Result<String, String> {
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
                Err(e) => return Err(e.to_string()),
            }
        }
        Err("could not make a temporary directory".to_string())
    }

    fn run(&self, process: &Process) -> Result<(Option<i32>, Vec<u8>, Vec<u8>), String> {
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
        let mut child = command
            .spawn()
            .map_err(|e| format!("{}: {e}", process.program))?;
        // Written from another thread: a child that fills its output before
        // it reads all its input would otherwise wait on us forever.
        let mut stdin = child.stdin.take();
        let input = process.stdin.clone();
        let writer = std::thread::spawn(move || {
            if let Some(s) = stdin.as_mut() {
                let _ = s.write_all(&input);
            }
        });
        let out = child.wait_with_output().map_err(|e| e.to_string())?;
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
    fn secure_random(&self, n: usize) -> Result<Vec<u8>, String> {
        let mut bytes = vec![0; n];
        getrandom::fill(&mut bytes).map_err(|e| e.to_string())?;
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

fn absent(what: &str) -> String {
    format!("this build has no host for {what}: the embedder installs one with tauto_rt::host::set")
}

impl Host for Absent {
    fn stdout(&self, _: &str) {
        crate::error_here(absent("stdout"))
    }

    fn stderr(&self, _: &str) {
        crate::error_here(absent("stderr"))
    }

    fn read_line(&self) -> Option<String> {
        None
    }

    fn read_file(&self, _: &str) -> Result<String, String> {
        Err(absent("fs_read"))
    }

    fn write_file(&self, _: &str, _: &str) -> Result<(), String> {
        Err(absent("fs_write"))
    }

    fn env(&self, _: &str) -> Option<String> {
        None
    }

    fn wall_ms(&self) -> i64 {
        crate::error_here(absent("wall_clock"))
    }

    fn monotonic_ns(&self) -> i64 {
        crate::error_here(absent("monotonic_clock"))
    }

    fn sleep(&self, _: u64) {
        crate::error_here(absent("sleep"))
    }

    fn random(&self) -> u64 {
        crate::error_here(absent("random"))
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
        fn read_file(&self, _: &str) -> Result<String, String> {
            Err("no files on this page".into())
        }
        fn write_file(&self, _: &str, _: &str) -> Result<(), String> {
            Err("no files on this page".into())
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
