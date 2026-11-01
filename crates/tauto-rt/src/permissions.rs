//! What a run may ask of the host (`docs/design/host-effects.md`). Standard
//! output, the clocks and the like are always allowed; the file system, the
//! environment and the network only with a permission, which may name the
//! paths, variables or hosts it covers. Reading the clipboard is denied too
//! until `--allow-clipboard`: a GUI host would otherwise hand the program
//! whatever the user last copied, passwords included.
//!
//! A GUI host may also widen `read` and `write` while the program runs, by
//! the powerbox ([`Permissions::choose`]): what the user picks in the host's
//! own file dialog, and nothing else, becomes readable or writable. The
//! program never names the path it is given; the user's act grants it.
//!
//! `--allow-div` is not about a resource the program reaches: it lets `Div`
//! (a loop or a call that may not stop) run without the host's step limit,
//! for a program whose job is not to stop, such as an event loop or a
//! server. Without it the limit stops a run that loops by mistake.

use std::path::{Component, Path, PathBuf};
use std::sync::RwLock;

/// The permissions of the kinds that need one.
pub const KINDS: [&str; 6] = ["read", "write", "env", "net", "run", "clipboard"];

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum Grant {
    /// Not given: the default.
    #[default]
    Denied,
    /// `--allow-net`: everything of the kind.
    All,
    /// `--allow-net=a.example,b.example:8080`: only these.
    Only(Vec<String>),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Permissions {
    pub read: Grant,
    pub write: Grant,
    pub env: Grant,
    pub net: Grant,
    /// Starting a program (`proc_run`), named as the program spells it. The
    /// program runs outside these permissions, so this grants all it does.
    pub run: Grant,
    /// Reading the clipboard (writing to it is always allowed, like standard
    /// output). Only `Denied` or `All`: there is nothing to name.
    pub clipboard: Grant,
    /// `--allow-div`: `Div` outside any `budget` runs without the host's
    /// step limit. Only `Denied` or `All`.
    pub div: Grant,
    /// What the user picked in the host's file dialog ([`Permissions::choose`]).
    pub chosen: Vec<Chosen>,
    /// `--allow-interactive`: what no flag covers is asked of the user at
    /// the terminal when the program reaches it ([`Permissions::check_or_ask`]),
    /// instead of the run being refused. Without a terminal it is denied.
    pub interactive: bool,
}

/// A path the user picked in the host's file dialog: the powerbox.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chosen {
    /// `read` or `write`.
    pub kind: &'static str,
    /// The path resolved when it was picked.
    pub path: PathBuf,
    /// The dialog picked a folder: what is under it is chosen too. A picked
    /// file covers that file only.
    pub folder: bool,
}

impl Permissions {
    /// Everything allowed: `--allow-all`.
    pub fn all() -> Permissions {
        Permissions {
            read: Grant::All,
            write: Grant::All,
            env: Grant::All,
            net: Grant::All,
            run: Grant::All,
            clipboard: Grant::All,
            div: Grant::All,
            chosen: Vec::new(),
            interactive: false,
        }
    }

    pub fn grant(&self, kind: &str) -> &Grant {
        match kind {
            "read" => &self.read,
            "write" => &self.write,
            "env" => &self.env,
            // A socket's address (`tcp_*`) is covered by `--allow-net` too.
            "net" | "socket" => &self.net,
            "run" => &self.run,
            "clipboard" => &self.clipboard,
            "div" => &self.div,
            _ => &Grant::Denied,
        }
    }

    fn grant_mut(&mut self, kind: &str) -> Option<&mut Grant> {
        match kind {
            "read" => Some(&mut self.read),
            "write" => Some(&mut self.write),
            "env" => Some(&mut self.env),
            "net" => Some(&mut self.net),
            "run" => Some(&mut self.run),
            "clipboard" => Some(&mut self.clipboard),
            "div" => Some(&mut self.div),
            _ => None,
        }
    }

    /// Reads one argument: `Ok(true)` when it is a permission flag
    /// (`--allow-all`, `-A`, `--allow-KIND`, `--allow-KIND=A,B`), `Ok(false)`
    /// when it is not one, `Err` when it is malformed. A later flag of the
    /// same kind widens the earlier one.
    pub fn parse_flag(&mut self, arg: &str) -> Result<bool, String> {
        if arg == "--allow-all" || arg == "-A" {
            *self = Permissions::all();
            return Ok(true);
        }
        if arg == "--allow-interactive" {
            self.interactive = true;
            return Ok(true);
        }
        let Some(rest) = arg.strip_prefix("--allow-") else {
            return Ok(false);
        };
        let (kind, list) = match rest.split_once('=') {
            Some((k, l)) => (k, Some(l)),
            None => (rest, None),
        };
        let Some(grant) = self.grant_mut(kind) else {
            return Err(format!(
                "unknown permission `{arg}`: the permissions are --allow-read, --allow-write, --allow-env, --allow-net, --allow-run, --allow-clipboard, --allow-div, --allow-all and --allow-interactive"
            ));
        };
        match list {
            None => *grant = Grant::All,
            Some(_) if kind == "clipboard" => {
                return Err(format!(
                    "`{arg}` names something, but the clipboard is one; write --allow-clipboard"
                ));
            }
            Some(_) if kind == "div" => {
                return Err(format!(
                    "`{arg}` names something, but the step limit is one; write --allow-div"
                ));
            }
            Some(list) => {
                let items: Vec<String> = list
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(str::to_string)
                    .collect();
                if items.is_empty() {
                    return Err(format!(
                        "`{arg}` names nothing; write --allow-{kind} for all"
                    ));
                }
                match grant {
                    Grant::All => {}
                    Grant::Only(old) => old.extend(items),
                    Grant::Denied => *grant = Grant::Only(items),
                }
            }
        }
        Ok(true)
    }

    /// The leading permission flags of `args`, and the arguments after them
    /// (after a `--` that ends them, if one does).
    pub fn from_args(args: &[String]) -> Result<(Permissions, Vec<String>), String> {
        let mut permissions = Permissions::default();
        let mut i = 0;
        while i < args.len() {
            if args[i] == "--" {
                i += 1;
                break;
            }
            if !permissions.parse_flag(&args[i])? {
                break;
            }
            i += 1;
        }
        Ok((permissions, args[i..].to_vec()))
    }

    /// The kinds of `needed` that no flag grants, each once: a run needing
    /// them does not start. None with `--allow-interactive`: the user is
    /// asked when the program reaches one.
    pub fn missing<'n>(&self, needed: impl IntoIterator<Item = &'n str>) -> Vec<&'n str> {
        let mut missing: Vec<&'n str> = Vec::new();
        if self.interactive {
            return missing;
        }
        for k in needed {
            if *self.grant(k) == Grant::Denied && !missing.contains(&k) {
                missing.push(k);
            }
        }
        missing
    }

    /// Whether the permission of `kind` covers `target`: a path for `read`
    /// and `write`, a variable's name for `env`, a URL for `net`, and a
    /// socket's address for `socket` (which `--allow-net` grants).
    pub fn allows(&self, kind: &str, target: &str) -> bool {
        self.check(kind, target).is_some()
    }

    /// What the host is to use for `target` when the permission of `kind`
    /// covers it, `None` when it does not. A limited `read` or `write` gives
    /// the path with its links followed, and a limited `net` the URL as the
    /// HTTP client reads it: the host acts on what was checked, not on a
    /// spelling it would read another way.
    pub fn check(&self, kind: &str, target: &str) -> Option<String> {
        self.check_flags(kind, target)
            .or_else(|| self.check_chosen(kind, target))
    }

    /// [`Permissions::check`], and with `--allow-interactive` what it does
    /// not cover asked of the user at the terminal: once, always (for the
    /// rest of the run, that file, variable or host and port), or not, which
    /// is the answer to anything else, an empty line and no terminal
    /// included. As with the powerbox, only the user's answer widens what
    /// the program may do.
    pub fn check_or_ask(&mut self, kind: &str, target: &str) -> Option<String> {
        if let Some(t) = self.check(kind, target) {
            return Some(t);
        }
        if !self.interactive || !KINDS.contains(&kind) {
            return None;
        }
        let shown = match kind {
            "read" | "write" => resolve(Path::new(target))?.to_string_lossy().into_owned(),
            "net" => {
                let (_, host, port) = parse_url(target)?;
                format!("{host}:{port}")
            }
            "clipboard" => String::new(),
            _ => target.to_string(),
        };
        let answer = ask(&format!(
            "the program asks for {kind}{}{shown}. allow? [y] once, [a] always, [N] deny: ",
            if shown.is_empty() { "" } else { " of " }
        ));
        match answer {
            Answer::Once => {}
            Answer::Always => {
                let grant = self.grant_mut(kind)?;
                if kind == "clipboard" {
                    *grant = Grant::All;
                } else {
                    match grant {
                        Grant::All => {}
                        Grant::Only(old) => old.push(shown.clone()),
                        Grant::Denied => *grant = Grant::Only(vec![shown.clone()]),
                    }
                }
            }
            Answer::Deny => return None,
        }
        match kind {
            // What was shown is what was allowed: the resolved path, or for
            // `net` the URL as the client reads it.
            "read" | "write" => Some(shown),
            "net" => parse_url(target).map(|(url, _, _)| url),
            _ => Some(target.to_string()),
        }
    }

    /// The powerbox: the user picked `path` in the host's own file dialog,
    /// so the program may `read` or `write` it (and, for a `folder`, what is
    /// under it) from now on, whatever the flags say. Only the host calls
    /// this, from the dialog's answer; the program has no way to. Gives the
    /// resolved path the host hands the program, `None` when `kind` is not
    /// `read` or `write` or the path does not resolve.
    pub fn choose(&mut self, kind: &str, path: &str, folder: bool) -> Option<String> {
        let kind = match kind {
            "read" => "read",
            "write" => "write",
            _ => return None,
        };
        let path = resolve(Path::new(path))?;
        let shown = path.to_string_lossy().into_owned();
        self.chosen.push(Chosen { kind, path, folder });
        Some(shown)
    }

    fn check_chosen(&self, kind: &str, target: &str) -> Option<String> {
        let mut chosen = self.chosen.iter().filter(|c| c.kind == kind).peekable();
        chosen.peek()?;
        // Resolved again: a link put in place after the pick does not lead
        // out of what was picked.
        let real = resolve(Path::new(target))?;
        chosen
            .any(|c| {
                if c.folder {
                    real.starts_with(&c.path)
                } else {
                    real == c.path
                }
            })
            .then(|| real.to_string_lossy().into_owned())
    }

    fn check_flags(&self, kind: &str, target: &str) -> Option<String> {
        match self.grant(kind) {
            Grant::Denied => None,
            Grant::All => Some(target.to_string()),
            Grant::Only(items) => match kind {
                "read" | "write" => {
                    let real = resolve(Path::new(target))?;
                    items
                        .iter()
                        .filter_map(|i| resolve(Path::new(i)))
                        .any(|dir| real.starts_with(dir))
                        .then(|| real.to_string_lossy().into_owned())
                }
                "env" | "run" => items
                    .iter()
                    .any(|i| i == target)
                    .then(|| target.to_string()),
                "net" => {
                    let (url, host, port) = parse_url(target)?;
                    items
                        .iter()
                        .any(|i| net_matches(i, &host, port))
                        .then_some(url)
                }
                "socket" => check_socket(items, target),
                _ => None,
            },
        }
    }
}

/// The message of a run that needs permissions it was not given.
pub fn missing_message<'n>(missing: &[&'n str]) -> String {
    let flags: Vec<String> = missing.iter().map(|k| format!("--allow-{k}")).collect();
    format!(
        "the program needs {} to run; the host denies it by default",
        flags.join(" ")
    )
}

/// `path` resolved as the system resolves it: absolute, and each part in
/// turn, a link followed before a `..` after it goes up from where the link
/// points. Past the part that exists only plain names may follow; `None`
/// when a `.` or `..` does, which the system would read against what is not
/// there yet.
fn resolve(path: &Path) -> Option<PathBuf> {
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().ok()?.join(path)
    };
    let mut at = PathBuf::from("/");
    let mut missing = false;
    for c in absolute.components() {
        match c {
            Component::Prefix(_) | Component::RootDir => {
                at = PathBuf::from(c.as_os_str());
                if let Ok(real) = at.canonicalize() {
                    at = real;
                }
            }
            Component::CurDir if !missing => {}
            Component::ParentDir if !missing => {
                at.pop();
            }
            Component::CurDir | Component::ParentDir => return None,
            Component::Normal(name) => {
                at.push(name);
                if !missing {
                    match at.canonicalize() {
                        Ok(real) => at = real,
                        Err(_) if at.symlink_metadata().is_ok() => return None,
                        Err(_) => missing = true,
                    }
                }
            }
        }
    }
    Some(at)
}

/// An `http` or `https` URL as the HTTP client reads it: its text, its host
/// and its port.
#[cfg(feature = "net")]
pub fn parse_url(text: &str) -> Option<(String, String, u16)> {
    let url = url::Url::parse(text).ok()?;
    if !matches!(url.scheme(), "http" | "https") {
        return None;
    }
    let host = url.host_str()?.to_ascii_lowercase();
    let port = url.port_or_known_default()?;
    Some((url.as_str().to_string(), host, port))
}

/// Without the HTTP client no request is made, and none is allowed.
#[cfg(not(feature = "net"))]
pub fn parse_url(_: &str) -> Option<(String, String, u16)> {
    None
}

/// A socket's address (`HOST:PORT` or `unix:PATH`) under a limited
/// `--allow-net`: `example.com` covers every port of the host,
/// `example.com:8080` one, and `unix:DIR` the sockets at or under that path,
/// resolved as `read` and `write` resolve theirs. Gives the address the host
/// is to use: the host in lower case, the path with its links followed.
fn check_socket(items: &[String], target: &str) -> Option<String> {
    use crate::tcp::Address;
    match Address::parse(target)? {
        Address::Tcp { host, port } => items
            .iter()
            .any(|i| match Address::parse(i) {
                Some(Address::Tcp { host: h, port: p }) => h == host && p == port,
                Some(Address::Unix(_)) => false,
                None => matches!(Address::parse(&format!("{i}:0")),
                    Some(Address::Tcp { host: h, .. }) if h == host),
            })
            .then(|| Address::Tcp { host, port }.text()),
        Address::Unix(path) => {
            let real = resolve(Path::new(&path))?;
            items
                .iter()
                .filter_map(|i| i.strip_prefix("unix:"))
                .filter_map(|dir| resolve(Path::new(dir)))
                .any(|dir| real.starts_with(dir))
                .then(|| format!("unix:{}", real.to_string_lossy()))
        }
    }
}

/// `example.com` covers every port of the host, `example.com:8080` one.
fn net_matches(item: &str, host: &str, port: u16) -> bool {
    let Some((_, h, p)) = parse_url(&format!("http://{item}/")) else {
        return false;
    };
    let explicit = item
        .rsplit_once(':')
        .is_some_and(|(_, p)| p.parse::<u16>().is_ok())
        && !item.ends_with(']');
    h == host && (!explicit || p == port)
}

enum Answer {
    Once,
    Always,
    Deny,
}

/// Asks at the terminal itself, not standard input: the program's own input
/// may be a pipe, which a question must not read from. No terminal denies.
fn ask(question: &str) -> Answer {
    match ask_terminal(question) {
        Some(line) => parse_answer(&line),
        None => {
            eprintln!("denied without a terminal to ask at: {question}");
            Answer::Deny
        }
    }
}

/// Writes `question` to the terminal and reads one line of answer from it,
/// never from standard input. `None` when there is no terminal to ask at, or
/// it fails; the caller takes that as a refusal.
pub fn ask_terminal(question: &str) -> Option<String> {
    #[cfg(unix)]
    {
        use std::io::{BufRead, Write};
        let tty = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open("/dev/tty")
            .ok()?;
        let mut out = &tty;
        out.write_all(question.as_bytes())
            .and_then(|_| out.flush())
            .ok()?;
        let mut line = String::new();
        std::io::BufReader::new(&tty).read_line(&mut line).ok()?;
        Some(line)
    }
    #[cfg(not(unix))]
    {
        let _ = question;
        None
    }
}

fn parse_answer(line: &str) -> Answer {
    match line.trim().to_ascii_lowercase().as_str() {
        "y" | "yes" => Answer::Once,
        "a" | "always" => Answer::Always,
        _ => Answer::Deny,
    }
}

static CURRENT: RwLock<Option<Permissions>> = RwLock::new(None);

/// Sets the permissions of the run in this process: the generated `main`
/// does it from its arguments, an embedding host before it calls `run`.
/// Calling this while a Tauto program is running panics.
pub fn set(permissions: Permissions) {
    crate::with_config_lock("permissions::set", || set_for_run(permissions));
}

pub(crate) fn set_for_run(permissions: Permissions) {
    crate::set_div_unbounded(permissions.div == Grant::All);
    *CURRENT.write().unwrap_or_else(|e| e.into_inner()) = Some(permissions);
}

pub(crate) fn snapshot() -> Option<Permissions> {
    CURRENT.read().unwrap_or_else(|e| e.into_inner()).clone()
}

pub(crate) fn restore(permissions: Option<Permissions>) {
    crate::set_div_unbounded(permissions.as_ref().is_some_and(|p| p.div == Grant::All));
    *CURRENT.write().unwrap_or_else(|e| e.into_inner()) = permissions;
}

/// The powerbox of the run ([`Permissions::choose`]): a GUI host calls it
/// with what the user picked in its file dialog.
pub fn choose(kind: &str, path: &str, folder: bool) -> Option<String> {
    CURRENT
        .write()
        .unwrap_or_else(|e| e.into_inner())
        .get_or_insert_with(Permissions::default)
        .choose(kind, path, folder)
}

/// [`Permissions::check_or_ask`] on the permissions of the run, which keep
/// what the user allowed always.
pub fn check_or_ask(kind: &str, target: &str) -> Option<String> {
    let current = current();
    if let Some(t) = current.check(kind, target) {
        return Some(t);
    }
    if !current.interactive {
        return None;
    }
    // The lock is not held while the user answers.
    let mut asking = current;
    let checked = asking.check_or_ask(kind, target);
    set_for_run(asking);
    checked
}

/// The permissions of the run; none until [`set`].
pub fn current() -> Permissions {
    CURRENT
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .clone()
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with(flags: &[&str]) -> Permissions {
        let args: Vec<String> = flags.iter().map(|s| s.to_string()).collect();
        Permissions::from_args(&args).unwrap().0
    }

    #[test]
    fn denied_by_default() {
        let p = Permissions::default();
        for kind in KINDS {
            assert!(!p.allows(kind, "x"));
        }
        assert_eq!(p.missing(["net", "read"]), ["net", "read"]);
    }

    #[test]
    fn flags_and_arguments() {
        let args: Vec<String> = ["--allow-net=a.example", "--allow-env", "--", "--allow-read"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        let (p, rest) = Permissions::from_args(&args).unwrap();
        assert_eq!(p.env, Grant::All);
        assert_eq!(p.read, Grant::Denied);
        assert_eq!(rest, ["--allow-read"]);
        assert!(Permissions::default().parse_flag("--allow-nett").is_err());
        let mut p = Permissions::default();
        assert_eq!(p.parse_flag("--allow-interactive"), Ok(true));
        assert!(p.interactive);
        assert!(p.missing(["net", "read"]).is_empty());
        assert!(Permissions::default().missing(["net"]) == ["net"]);
        assert!(Permissions::default().parse_flag("--allow-net=").is_err());
        assert_eq!(with(&["-A"]), Permissions::all());
    }

    #[test]
    #[cfg(feature = "net")]
    fn hosts() {
        let p = with(&["--allow-net=api.example.com,local.test:8080"]);
        assert!(p.allows("net", "https://api.example.com/v1?q"));
        assert!(p.allows("net", "http://API.example.com:9000/"));
        assert!(p.allows("net", "http://user@api.example.com/"));
        assert!(!p.allows("net", "https://example.com/"));
        assert!(!p.allows("net", "https://api.example.com.evil.test/"));
        assert!(p.allows("net", "http://local.test:8080/"));
        assert!(!p.allows("net", "http://local.test/"));
        assert!(!p.allows("net", "file:///etc/passwd"));
        assert!(!p.allows("net", "data:text/plain,hi"));
    }

    #[test]
    fn paths() {
        let dir = std::env::temp_dir().join(format!("tauto-perm-{}", std::process::id()));
        let inside = dir.join("in");
        std::fs::create_dir_all(&inside).unwrap();
        let p = with(&[&format!("--allow-read={}", inside.display())]);
        assert!(p.allows("read", &inside.join("a.txt").display().to_string()));
        assert!(p.allows("read", &inside.join("new/b.txt").display().to_string()));
        assert!(!p.allows("read", &inside.join("../x.txt").display().to_string()));
        assert!(!p.allows("read", &dir.join("in2/x").display().to_string()));
        assert!(!p.allows("write", &inside.join("a.txt").display().to_string()));
        #[cfg(unix)]
        {
            let outside = dir.join("out");
            std::fs::create_dir_all(&outside).unwrap();
            let _ = std::os::unix::fs::symlink(&outside, inside.join("link"));
            assert!(!p.allows("read", &inside.join("link/secret").display().to_string()));
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_socket_is_covered_by_net() {
        let dir = std::env::temp_dir().join(format!("tauto-perm-sock-{}", std::process::id()));
        let inside = dir.join("in");
        std::fs::create_dir_all(&inside).unwrap();
        let p = with(&[
            "--allow-net=local.test,Other.Test:9000,[::1]:8080",
            &format!("--allow-net=unix:{}", inside.display()),
        ]);
        assert_eq!(
            p.check("socket", "LOCAL.test:1"),
            Some("local.test:1".to_string())
        );
        assert!(p.allows("socket", "other.test:9000"));
        assert!(!p.allows("socket", "other.test:9001"));
        assert!(p.allows("socket", "[::1]:8080"));
        assert!(!p.allows("socket", "[::1]:8081"));
        assert!(!p.allows("socket", "local.test.evil:1"));
        assert!(!p.allows("socket", "local.test"));
        let sock = inside.join("a.sock").display().to_string();
        assert!(p.allows("socket", &format!("unix:{sock}")));
        assert!(!p.allows("socket", &format!("unix:{}", dir.join("b.sock").display())));
        assert!(!p.allows("socket", &format!("unix:{}/../b.sock", inside.display())));
        assert!(!with(&["--allow-read"]).allows("socket", "local.test:1"));
        assert!(with(&["--allow-net"]).allows("socket", "any.test:1"));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    #[cfg(feature = "net")]
    fn a_url_is_checked_as_the_client_reads_it() {
        let p = with(&["--allow-net=allowed.example"]);
        assert!(!p.allows("net", "http://127.0.0.1:18765\\@allowed.example/"));
        assert_eq!(
            p.check("net", "HTTP://Allowed.Example/a b"),
            Some("http://allowed.example/a%20b".to_string())
        );
    }

    #[test]
    #[cfg(unix)]
    fn a_link_then_dot_dot_goes_up_from_where_the_link_points() {
        let dir = std::env::temp_dir().join(format!("tauto-perm-up-{}", std::process::id()));
        let allowed = dir.join("allowed");
        let sub = dir.join("outside/sub");
        std::fs::create_dir_all(&allowed).unwrap();
        std::fs::create_dir_all(&sub).unwrap();
        std::fs::write(dir.join("outside/secret"), "s").unwrap();
        std::os::unix::fs::symlink(&sub, allowed.join("link")).unwrap();
        for flag in ["--allow-read", "--allow-write"] {
            let p = with(&[&format!("{flag}={}", allowed.display())]);
            let kind = &flag["--allow-".len()..];
            let through = allowed.join("link/../secret").display().to_string();
            assert_eq!(p.check(kind, &through), None, "{kind}");
            let missing = allowed
                .join("new/../../outside/secret")
                .display()
                .to_string();
            assert_eq!(p.check(kind, &missing), None, "{kind}");
            let inside = allowed.join("a.txt").display().to_string();
            assert!(p.check(kind, &inside).is_some(), "{kind}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn div_is_limited_until_allowed() {
        assert_eq!(Permissions::default().div, Grant::Denied);
        assert_eq!(with(&["--allow-div"]).div, Grant::All);
        assert_eq!(with(&["-A"]).div, Grant::All);
        assert!(Permissions::default().parse_flag("--allow-div=x").is_err());
    }

    #[test]
    fn clipboard_is_denied_until_allowed() {
        assert!(!Permissions::default().allows("clipboard", ""));
        assert!(with(&["--allow-clipboard"]).allows("clipboard", ""));
        assert!(with(&["-A"]).allows("clipboard", ""));
        assert!(
            Permissions::default()
                .parse_flag("--allow-clipboard=x")
                .is_err()
        );
        assert_eq!(Permissions::default().missing(["clipboard"]), ["clipboard"]);
    }

    #[test]
    fn the_powerbox_grants_only_what_was_picked() {
        let dir = std::env::temp_dir().join(format!("tauto-perm-box-{}", std::process::id()));
        let docs = dir.join("docs");
        std::fs::create_dir_all(&docs).unwrap();
        std::fs::write(docs.join("a.txt"), "a").unwrap();
        std::fs::write(docs.join("b.txt"), "b").unwrap();
        let a = docs.join("a.txt").display().to_string();
        let b = docs.join("b.txt").display().to_string();
        let mut p = Permissions::default();
        assert!(!p.allows("read", &a));
        assert!(p.choose("read", &a, false).is_some());
        assert!(p.allows("read", &a));
        assert!(!p.allows("write", &a));
        assert!(!p.allows("read", &b));
        assert!(!p.allows("read", &docs.join("a.txt/x").display().to_string()));
        assert!(!p.allows("read", &docs.join("a.txt/../b.txt").display().to_string()));
        assert!(
            p.choose("write", &docs.display().to_string(), true)
                .is_some()
        );
        assert!(p.allows("write", &b));
        assert!(p.allows("write", &docs.join("new.txt").display().to_string()));
        assert!(!p.allows("write", &dir.join("x").display().to_string()));
        assert!(p.choose("env", "HOME", false).is_none());
        assert!(p.choose("net", "http://a.example/", false).is_none());
        #[cfg(unix)]
        {
            let outside = dir.join("out");
            std::fs::create_dir_all(&outside).unwrap();
            std::os::unix::fs::symlink(&outside, docs.join("link")).unwrap();
            assert!(!p.allows("write", &docs.join("link/x").display().to_string()));
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn variables() {
        let p = with(&["--allow-env=HOME"]);
        assert!(p.allows("env", "HOME"));
        assert!(!p.allows("env", "PATH"));
    }

    #[test]
    fn answers() {
        assert!(matches!(parse_answer("y\n"), Answer::Once));
        assert!(matches!(parse_answer(" A \n"), Answer::Always));
        assert!(matches!(parse_answer("\n"), Answer::Deny));
        assert!(matches!(parse_answer("yess"), Answer::Deny));
    }

    #[test]
    fn not_interactive_never_asks() {
        let mut p = Permissions::default();
        assert_eq!(p.check_or_ask("env", "HOME"), None);
    }
}
