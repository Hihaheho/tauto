#![allow(clippy::ptr_arg)]
//! The standard library of the affine data (`docs/design/ownership.md`) and of
//! `Result`, `Slice` and the views (`docs/design/rust-backend.md`), in Rust. The functions that make a
//! generated type (`List`) are written by the generator.
//!
//! A function that may perform an effect with `resume 0` (`vec_index`'s
//! `out_of_bounds`) returns `Result<_, Abort>` and takes the place of the
//! call.

use crate::a::Abort;
pub use crate::ct::*;
use crate::{Loc, Op, Text, error, messages};

/// A map in the order of insertion, as the evaluator's `HashMap(K, V)` is:
/// `hashmap_into_vec` and `show` list the entries in the order they were
/// first inserted, in both. The entries stay in a `Vec` in that order; a
/// table from each key's hash to the newest entry with that hash, and a chain
/// from each entry to the previous one with the same hash, find a key in
/// O(1) on average.
#[derive(Debug, Clone)]
pub struct HashMap<K, V> {
    entries: Vec<(K, V)>,
    heads: std::collections::HashMap<u64, usize>,
    /// The previous entry with the same hash, or `NONE`.
    chain: Vec<usize>,
    state: std::hash::RandomState,
}

const NONE: usize = usize::MAX;

impl<K, V> Default for HashMap<K, V> {
    fn default() -> Self {
        HashMap {
            entries: Vec::new(),
            heads: std::collections::HashMap::new(),
            chain: Vec::new(),
            state: std::hash::RandomState::new(),
        }
    }
}

impl<K, V> HashMap<K, V> {
    pub fn iter(&self) -> impl Iterator<Item = &(K, V)> {
        self.entries.iter()
    }
}

impl<K: Eq + std::hash::Hash, V> HashMap<K, V> {
    fn hash(&self, k: &K) -> u64 {
        std::hash::BuildHasher::hash_one(&self.state, k)
    }

    fn find(&self, k: &K) -> (Option<usize>, u64) {
        let h = self.hash(k);
        let mut at = self.heads.get(&h).copied().unwrap_or(NONE);
        while at != NONE {
            if self.entries[at].0 == *k {
                return (Some(at), h);
            }
            at = self.chain[at];
        }
        (None, h)
    }
}

pub fn text_of(b: String) -> Text {
    Text::from(b)
}

pub fn buf_new() -> String {
    String::new()
}

pub fn buf_of(t: &Text) -> String {
    t.to_string()
}

pub fn buf_push(b: &mut String, t: &Text) {
    b.push_str(t);
}

pub fn buf_clone(b: &String) -> String {
    b.clone()
}

pub fn concat(a: Text, b: Text) -> Text {
    Text::from(format!("{a}{b}"))
}

pub fn vec_new<A>() -> Vec<A> {
    Vec::new()
}

pub fn vec_push<A>(v: &mut Vec<A>, x: A) {
    v.push(x);
}

pub fn vec_pop<A>(v: &mut Vec<A>) -> Option<A> {
    v.pop()
}

pub fn vec_len<A>(v: &[A]) -> u64 {
    v.len() as u64
}

pub fn slice_len<A>(v: &[A]) -> u64 {
    v.len() as u64
}

pub fn vec_as_slice<A>(v: &[A]) -> &[A] {
    v
}

pub fn vec_clear<A>(v: &mut Vec<A>) {
    v.clear();
}

pub fn vec_truncate<A>(v: &mut Vec<A>, n: u64) {
    v.truncate(usize::try_from(n).unwrap_or(usize::MAX));
}

/// `vec_index(&v, i)`: performs `out_of_bounds` when `i` is past the end.
pub fn vec_index<'a, A>(v: &'a [A], i: u64, at: Loc, op: Op) -> Result<&'a A, Abort> {
    usize::try_from(i)
        .ok()
        .and_then(|i| v.get(i))
        .ok_or_else(|| Abort {
            op,
            args: Box::new(()),
            at,
        })
}

pub fn vec_swap<A>(v: &mut [A], i: u64, j: u64, at: Loc, op: Op) -> Result<(), Abort> {
    match (usize::try_from(i), usize::try_from(j)) {
        (Ok(i), Ok(j)) if i < v.len() && j < v.len() => {
            v.swap(i, j);
            Ok(())
        }
        _ => Err(Abort {
            op,
            args: Box::new(()),
            at,
        }),
    }
}

pub fn hashmap_new<K, V>() -> HashMap<K, V> {
    HashMap::default()
}

/// `hashmap_index(&m, &k)`: performs `missing` when there is no such key.
pub fn hashmap_index<'a, K: Eq + std::hash::Hash, V>(
    m: &'a HashMap<K, V>,
    k: &K,
    at: Loc,
    op: Op,
) -> Result<&'a V, Abort> {
    hashmap_get(m, k).ok_or_else(|| Abort {
        op,
        args: Box::new(()),
        at,
    })
}

pub fn hashmap_insert<K: Eq + std::hash::Hash, V>(m: &mut HashMap<K, V>, k: K, v: V) -> Option<V> {
    match m.find(&k) {
        (Some(i), _) => Some(std::mem::replace(&mut m.entries[i].1, v)),
        (None, h) => {
            let i = m.entries.len();
            m.entries.push((k, v));
            m.chain.push(m.heads.insert(h, i).unwrap_or(NONE));
            None
        }
    }
}

pub fn hashmap_into_vec<K, V>(m: HashMap<K, V>) -> Vec<(K, V)> {
    m.entries
}

pub fn replace<A>(x: &mut A, v: A) -> A {
    std::mem::replace(x, v)
}

// `Array(A)` of the prelude: shared and read-only. `array_of_list` and
// `array_to_list` take and make a `List`, so the generator writes them.

pub type Array<A> = crate::Rc<[A]>;

pub fn vec_into_array<A>(v: Vec<A>) -> Array<A> {
    v.into()
}

pub fn array_get<A: Clone>(a: impl AsRef<[A]>, i: u64) -> Option<A> {
    usize::try_from(i)
        .ok()
        .and_then(|i| a.as_ref().get(i).cloned())
}

pub fn array_len<A>(a: impl AsRef<[A]>) -> u64 {
    a.as_ref().len() as u64
}

// `Bytes` of the prelude: shared and read-only. A slice is a window on the
// same storage, so `bytes_slice` costs no copy.

#[derive(Clone)]
pub struct Bytes {
    data: crate::Rc<[u8]>,
    start: usize,
    end: usize,
}

impl Bytes {
    pub fn as_slice(&self) -> &[u8] {
        &self.data[self.start..self.end]
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(v: Vec<u8>) -> Bytes {
        let end = v.len();
        Bytes {
            data: v.into(),
            start: 0,
            end,
        }
    }
}

impl std::ops::Deref for Bytes {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl PartialEq for Bytes {
    fn eq(&self, other: &Bytes) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Eq for Bytes {}

impl std::fmt::Debug for Bytes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bytes{:?}", self.as_slice())
    }
}

pub fn bytes_len(b: Bytes) -> u64 {
    b.len() as u64
}

pub fn bytes_get(b: Bytes, i: u64) -> Option<u8> {
    usize::try_from(i).ok().and_then(|i| b.get(i).copied())
}

/// The bytes from `start` to `end`, sharing `b`'s storage; `None` unless
/// `start <= end <= len`.
pub fn bytes_slice(b: Bytes, start: u64, end: u64) -> Option<Bytes> {
    let (Ok(s), Ok(e)) = (usize::try_from(start), usize::try_from(end)) else {
        return None;
    };
    (s <= e && e <= b.len()).then(|| Bytes {
        start: b.start + s,
        end: b.start + e,
        data: b.data,
    })
}

pub fn bytes_concat(a: Bytes, b: Bytes) -> Bytes {
    if a.is_empty() {
        return b;
    }
    if b.is_empty() {
        return a;
    }
    let mut v = Vec::with_capacity(a.len() + b.len());
    v.extend_from_slice(&a);
    v.extend_from_slice(&b);
    Bytes::from(v)
}

pub fn bytes_eq(a: Bytes, b: Bytes) -> bool {
    a == b
}

pub fn bytes_of_text(t: Text) -> Bytes {
    Bytes::from(t.as_bytes().to_vec())
}

/// The text the bytes encode, when they are well-formed UTF-8.
pub fn text_of_bytes(b: Bytes) -> Option<Text> {
    std::str::from_utf8(&b)
        .ok()
        .map(|s| Text::from(s.to_string()))
}

pub fn bytes_into_vec(b: Bytes) -> Vec<u8> {
    b.to_vec()
}

// Views: the result borrows from the argument.

pub fn vec_get<A>(v: &Vec<A>, i: u64) -> Option<&A> {
    usize::try_from(i).ok().and_then(|i| v.get(i))
}

pub fn vec_get_mut<A>(v: &mut Vec<A>, i: u64) -> Option<&mut A> {
    usize::try_from(i).ok().and_then(|i| v.get_mut(i))
}

pub fn vec_last_mut<A>(v: &mut Vec<A>) -> Option<&mut A> {
    v.last_mut()
}

pub fn slice_get<A>(v: &[A], i: u64) -> Option<&A> {
    usize::try_from(i).ok().and_then(|i| v.get(i))
}

pub fn vec_as_mut_slice<A>(v: &mut Vec<A>) -> &mut [A] {
    v.as_mut_slice()
}

pub fn hashmap_get<'a, K: Eq + std::hash::Hash, V>(m: &'a HashMap<K, V>, k: &K) -> Option<&'a V> {
    m.find(k).0.map(|i| &m.entries[i].1)
}

pub fn hashmap_get_mut<'a, K: Eq + std::hash::Hash, V>(
    m: &'a mut HashMap<K, V>,
    k: &K,
) -> Option<&'a mut V> {
    m.find(k).0.map(|i| &mut m.entries[i].1)
}

pub fn text_len(t: Text) -> u64 {
    t.len() as u64
}

pub fn text_byte(t: Text, i: u64) -> Option<u8> {
    usize::try_from(i)
        .ok()
        .and_then(|i| t.as_bytes().get(i).copied())
}

pub fn text_slice(t: Text, start: u64, end: u64) -> Option<Text> {
    match (usize::try_from(start), usize::try_from(end)) {
        (Ok(s), Ok(e)) => t.get(s..e).map(Text::from),
        _ => None,
    }
}

pub fn text_compare(a: Text, b: Text) -> i64 {
    a.as_bytes().cmp(b.as_bytes()) as i64
}

pub fn text_of_code_point(c: u32) -> Option<Text> {
    char::from_u32(c).map(|c| Text::from(c.to_string()))
}

/// The text whose UTF-8 encoding is `bytes`; `None` when they are not
/// well-formed UTF-8.
pub fn text_of_utf8_vec(bytes: Vec<u8>) -> Option<Text> {
    String::from_utf8(bytes).ok().map(Text::from)
}

pub fn text_of_i64(n: i64) -> Text {
    Text::from(n.to_string())
}

pub fn text_of_u64(n: u64) -> Text {
    Text::from(n.to_string())
}

pub fn text_of_nat(n: crate::nat::Nat) -> Text {
    Text::from(n.to_string())
}

pub fn nat_of_u64(n: u64) -> crate::nat::Nat {
    crate::nat::Nat::from_u64(n)
}

pub fn u64_of_nat(n: crate::nat::Nat, at: Loc) -> u64 {
    n.to_u64().unwrap_or_else(|| error(messages::TOO_LARGE, at))
}

macro_rules! conversion {
    ($($name:ident: $from:ty => $to:ty),* $(,)?) => {$(
        pub fn $name(n: $from, at: Loc) -> $to {
            <$to>::try_from(n).unwrap_or_else(|_| error(messages::TOO_LARGE, at))
        }
    )*};
}

conversion! {
    i64_of_i32: i32 => i64,
    i32_of_i64: i64 => i32,
    i64_of_u64: u64 => i64,
    u64_of_i64: i64 => u64,
    u64_of_u32: u32 => u64,
    u32_of_u64: u64 => u32,
    u64_of_u8: u8 => u64,
    u8_of_u64: u64 => u8,
}

macro_rules! bits {
    ($($w:ident: $and:ident $or:ident $xor:ident $shl:ident $shr:ident $rotl:ident $rotr:ident),* $(,)?) => {$(
        pub fn $and(a: $w, b: $w) -> $w { a & b }
        pub fn $or(a: $w, b: $w) -> $w { a | b }
        pub fn $xor(a: $w, b: $w) -> $w { a ^ b }
        pub fn $shl(a: $w, s: u64) -> $w { a.wrapping_shl((s % $w::BITS as u64) as u32) }
        pub fn $shr(a: $w, s: u64) -> $w { a.wrapping_shr((s % $w::BITS as u64) as u32) }
        pub fn $rotl(a: $w, s: u64) -> $w { a.rotate_left((s % $w::BITS as u64) as u32) }
        pub fn $rotr(a: $w, s: u64) -> $w { a.rotate_right((s % $w::BITS as u64) as u32) }
    )*};
}

bits! {
    u32: u32_and u32_or u32_xor u32_shl u32_shr u32_rotl u32_rotr,
    u64: u64_and u64_or u64_xor u64_shl u64_shr u64_rotl u64_rotr,
}

/// The host's answer to an unanswered `stop`: ends the run with `message`
/// as its error.
pub fn os_stop(message: Text, at: Loc) -> ! {
    error(message.to_string(), at)
}

pub fn os_print(t: Text) {
    crate::host::get().stdout(&t);
}

pub fn os_eprint(t: Text) {
    crate::host::get().stderr(&t);
}

pub fn os_read_file(path: Text) -> Result<Text, Text> {
    crate::host::get()
        .read_file(&path)
        .map(Text::from)
        .map_err(Text::from)
}

pub fn os_write_file(path: Text, contents: Text) -> Result<(), Text> {
    crate::host::get()
        .write_file(&path, &contents)
        .map_err(Text::from)
}

pub fn os_read_bytes(path: Text) -> Result<Bytes, Text> {
    crate::host::get()
        .read_bytes(&path)
        .map(Bytes::from)
        .map_err(Text::from)
}

pub fn os_write_bytes(path: Text, contents: Bytes) -> Result<(), Text> {
    crate::host::get()
        .write_bytes(&path, &contents)
        .map_err(Text::from)
}

pub fn os_create_dir(path: Text) -> Result<(), Text> {
    crate::host::get().create_dir(&path).map_err(Text::from)
}

/// The names under a directory, in byte order.
pub fn os_list_dir_vec(path: Text) -> Result<Vec<Text>, Text> {
    crate::host::get()
        .list_dir(&path)
        .map(|names| names.into_iter().map(Text::from).collect())
        .map_err(Text::from)
}

pub fn os_remove(path: Text) -> Result<(), Text> {
    crate::host::get().remove(&path).map_err(Text::from)
}

/// What is at a path: empty when nothing is, else the kind (`file`, `dir`
/// or `other`), the size and the time of the last change in milliseconds.
pub fn os_stat_vec(path: Text) -> Result<Vec<Text>, Text> {
    crate::host::get()
        .stat(&path)
        .map(|found| match found {
            None => Vec::new(),
            Some(s) => vec![
                Text::from(s.kind),
                Text::from(s.size.to_string()),
                Text::from(s.modified_ms.to_string()),
            ],
        })
        .map_err(Text::from)
}

pub fn os_move_path(from: Text, to: Text) -> Result<(), Text> {
    crate::host::get().rename(&from, &to).map_err(Text::from)
}

pub fn os_copy_file(from: Text, to: Text) -> Result<(), Text> {
    crate::host::get().copy(&from, &to).map_err(Text::from)
}

pub fn os_canonicalize(path: Text) -> Result<Text, Text> {
    crate::host::get()
        .canonicalize(&path)
        .map(Text::from)
        .map_err(Text::from)
}

/// A new temporary directory, which the run may read and write under from
/// now on: the host picked it, as the user picks a path in the powerbox
/// ([`crate::permissions::choose`]).
pub fn os_temp_dir() -> Result<Text, Text> {
    let dir = crate::host::get().temp_dir()?;
    crate::permissions::choose("read", &dir, true);
    crate::permissions::choose("write", &dir, true)
        .map(Text::from)
        .ok_or_else(|| Text::from(dir))
}

static TAUTO_PATH: std::sync::RwLock<Option<String>> = std::sync::RwLock::new(None);

/// What the program named `tauto` runs (`proc_run`): the `tauto` that runs
/// this program, which sets it. Unset, `tauto` is looked up on `PATH`.
/// Calling this while a Tauto program is running panics.
pub fn set_tauto_path(path: String) {
    crate::with_config_lock("stdlib::set_tauto_path", || {
        *TAUTO_PATH.write().unwrap_or_else(|e| e.into_inner()) = Some(path);
    });
}

pub fn run_program(program: &str) -> String {
    match &*TAUTO_PATH.read().unwrap_or_else(|e| e.into_inner()) {
        Some(path) if program == "tauto" => path.clone(),
        _ => program.to_string(),
    }
}

/// Runs a program: the exit status (empty when a signal ended it) and
/// standard error as text; and standard output. `env` is each variable's
/// name then value.
pub fn os_run_vec(
    program: Text,
    args: Vec<Text>,
    dir: Text,
    env: Vec<Text>,
    stdin: Bytes,
) -> Result<(Vec<Text>, Bytes), Text> {
    let process = crate::host::Process {
        program: run_program(&program),
        args: args.iter().map(|a| a.to_string()).collect(),
        dir: (!dir.is_empty()).then(|| dir.to_string()),
        env: env
            .chunks(2)
            .filter(|p| p.len() == 2)
            .map(|p| (p[0].to_string(), p[1].to_string()))
            .collect(),
        stdin: stdin.to_vec(),
    };
    let (status, stdout, stderr) = crate::host::get().run(&process)?;
    let status = status.map_or(String::new(), |c| c.to_string());
    Ok((
        vec![
            Text::from(status),
            Text::from(String::from_utf8_lossy(&stderr).into_owned()),
        ],
        Bytes::from(stdout),
    ))
}

/// The program's arguments: those after the permission flags
/// ([`crate::permissions::Permissions::from_args`]), as [`set_args`] left them.
pub fn os_args_vec() -> Vec<Text> {
    ARGS.read()
        .unwrap_or_else(|e| e.into_inner())
        .clone()
        .unwrap_or_else(|| std::env::args().skip(1).collect())
        .into_iter()
        .map(Text::from)
        .collect()
}

static ARGS: std::sync::RwLock<Option<Vec<String>>> = std::sync::RwLock::new(None);

/// What `argv` answers from now on.
/// Calling this while a Tauto program is running panics.
pub fn set_args(args: Vec<String>) {
    crate::with_config_lock("stdlib::set_args", || set_args_for_run(args));
}

pub(crate) fn set_args_for_run(args: Vec<String>) {
    *ARGS.write().unwrap_or_else(|e| e.into_inner()) = Some(args);
}

pub(crate) fn snapshot_args() -> Option<Vec<String>> {
    ARGS.read().unwrap_or_else(|e| e.into_inner()).clone()
}

pub(crate) fn restore_args(args: Option<Vec<String>>) {
    *ARGS.write().unwrap_or_else(|e| e.into_inner()) = args;
}

pub fn os_read_line() -> Option<Text> {
    crate::host::get().read_line().map(Text::from)
}

/// Up to `max` bytes of standard input, as soon as any arrive; none at its end.
pub fn os_read_stdin(max: u64) -> Bytes {
    Bytes::from(crate::host::get().read_stdin(max.min(1 << 24) as usize))
}

pub fn os_flush() {
    crate::host::get().flush()
}

pub fn os_env(name: Text) -> Option<Text> {
    crate::host::get().env(&name).map(Text::from)
}

pub fn os_wall_ms() -> i64 {
    crate::host::get().wall_ms()
}

pub fn os_monotonic_ns() -> i64 {
    crate::host::get().monotonic_ns()
}

pub fn os_sleep(ms: u64) {
    crate::host::get().sleep(ms);
}

/// 63 random bits (a `u64` below 2^63, which every backend holds alike), from
/// the host. Not for secrets.
pub fn os_random() -> u64 {
    crate::host::get().random() >> 1
}

pub fn os_secure_random(n: u64) -> Result<Bytes, Text> {
    let n = usize::try_from(n).map_err(|_| Text::from("too many random bytes asked for"))?;
    crate::host::get()
        .secure_random(n)
        .map(Bytes::from)
        .map_err(Text::from)
}

pub fn os_status(t: Text) -> u64 {
    t.parse().unwrap_or(0)
}

pub fn os_check(kind: Text, target: Text) -> Option<Text> {
    crate::permissions::check_or_ask(&kind, &target).map(Text::from)
}

/// An HTTP request: the status, then each header's name and value; and the
/// body as sent. A header value that is not UTF-8 fails the request rather
/// than reach the program changed.
/// With an `address` (not empty), the connection goes to that address and the
/// host of the URL is not resolved again; the `Host` header and the TLS name
/// stay the URL's host.
#[cfg(feature = "net")]
pub fn os_fetch_vec(
    method: Text,
    url: Text,
    address: Text,
    headers: Vec<Text>,
    body: Bytes,
) -> Result<(Vec<Text>, Bytes), Text> {
    let method =
        reqwest::Method::from_bytes(method.as_bytes()).map_err(|e| Text::from(e.to_string()))?;
    let mut builder = reqwest::blocking::Client::builder()
        // A redirect would reach a host the permission may not cover.
        .redirect(reqwest::redirect::Policy::none());
    if !address.is_empty() {
        let Some((_, host, port)) = crate::permissions::parse_url(&url) else {
            return Err(Text::from(format!("cannot connect to {url}")));
        };
        let ip = fixed_address(&address)?;
        let name = host
            .trim_start_matches('[')
            .trim_end_matches(']')
            .to_string();
        builder = builder.resolve(&name, std::net::SocketAddr::new(ip, port));
    }
    let client = builder.build().map_err(|e| Text::from(e.to_string()))?;
    let mut request = client.request(method, &*url);
    for pair in headers.chunks(2) {
        if let [name, value] = pair {
            request = request.header(&**name, &**value);
        }
    }
    let response = request
        .body(body.to_vec())
        .send()
        .map_err(|e| Text::from(e.to_string()))?;
    let mut out = vec![Text::from(response.status().as_u16().to_string())];
    for (name, value) in response.headers() {
        let Ok(value) = std::str::from_utf8(value.as_bytes()) else {
            return Err(Text::from(format!(
                "the value of the response header {name} is not UTF-8"
            )));
        };
        out.push(Text::from(name.as_str().to_string()));
        out.push(Text::from(value.to_string()));
    }
    let body = response.bytes().map_err(|e| Text::from(e.to_string()))?;
    Ok((out, Bytes::from(body.to_vec())))
}

/// The addresses the host of `url` resolves to, read with the parser the
/// permission check used: each once, in the order the system gave them.
#[cfg(feature = "net")]
pub fn os_resolve_vec(url: Text) -> Result<Vec<Text>, Text> {
    use std::net::ToSocketAddrs;
    let Some((_, host, _)) = crate::permissions::parse_url(&url) else {
        return Err(Text::from(format!("cannot resolve {url}")));
    };
    let host = host.trim_start_matches('[').trim_end_matches(']');
    let found = (host, 0)
        .to_socket_addrs()
        .map_err(|e| Text::from(e.to_string()))?;
    let mut out: Vec<std::net::IpAddr> = Vec::new();
    for a in found {
        if !out.contains(&a.ip()) {
            out.push(a.ip());
        }
    }
    Ok(out
        .into_iter()
        .map(|ip| Text::from(ip.to_string()))
        .collect())
}

/// The address `net_addr` connects to: an IP address as `net_resolve` gives it.
#[cfg(feature = "net")]
fn fixed_address(address: &str) -> Result<std::net::IpAddr, Text> {
    address
        .trim_start_matches('[')
        .trim_end_matches(']')
        .parse()
        .map_err(|_| Text::from(format!("not an IP address: {address}")))
}

#[cfg(not(feature = "net"))]
pub fn os_resolve_vec(_: Text) -> Result<Vec<Text>, Text> {
    Err(Text::from(
        "this build has no network: the `net` feature of tauto-rt is off".to_string(),
    ))
}

#[cfg(not(feature = "net"))]
pub fn os_fetch_vec(
    _: Text,
    _: Text,
    _: Text,
    _: Vec<Text>,
    _: Bytes,
) -> Result<(Vec<Text>, Bytes), Text> {
    Err(Text::from(
        "this build has no network: the `net` feature of tauto-rt is off".to_string(),
    ))
}

pub fn os_exit(code: i32, at: Loc) -> ! {
    if !(0..=255).contains(&code) {
        error(messages::TOO_LARGE, at);
    }
    crate::host::get().exit(code)
}

// `Ref`, `Mutex` and `Atomic` of the prelude (`Par.taut`): slots many closures
// and tasks share. A copy is a new handle on the same slot. With the `sync`
// feature (a program that starts tasks) the slots are safe to share between
// threads.

/// A mutex's content and the places in line for it (`mutex_claim`): the
/// content is empty between a take and its put, and a put hands it to the
/// first place waiting, whose signal it raises.
pub struct Line<A> {
    content: Option<A>,
    waiting: std::collections::VecDeque<crate::signal::Signal>,
    handed: Vec<(crate::signal::Signal, A)>,
}

impl<A> Line<A> {
    fn new(v: A) -> Line<A> {
        Line {
            content: Some(v),
            waiting: std::collections::VecDeque::new(),
            handed: Vec::new(),
        }
    }

    fn claim(&mut self) -> crate::signal::Signal {
        let s = crate::signal::Signal::new();
        match self.content.take() {
            Some(v) if self.waiting.is_empty() => {
                self.handed.push((s.clone(), v));
                s.raise();
            }
            content => {
                self.content = content;
                self.waiting.push_back(s.clone());
            }
        }
        s
    }

    fn put(&mut self, v: A) {
        match self.waiting.pop_front() {
            Some(s) => {
                self.handed.push((s.clone(), v));
                s.raise();
            }
            None => self.content = Some(v),
        }
    }

    fn take_claimed(&mut self, s: &crate::signal::Signal) -> A {
        let i = self
            .handed
            .iter()
            .position(|(h, _)| h.same(s))
            .expect("tauto: a mutex's content taken before it was handed");
        self.handed.swap_remove(i).1
    }
}

#[cfg(not(feature = "sync"))]
mod cells {
    use super::Line;
    use crate::signal::Signal;
    use std::cell::{Cell, RefCell};
    use std::rc::Rc;

    pub struct Ref<A>(Rc<RefCell<A>>);

    impl<A> Clone for Ref<A> {
        fn clone(&self) -> Self {
            Ref(self.0.clone())
        }
    }

    pub fn ref_new<A>(v: A) -> Ref<A> {
        Ref(Rc::new(RefCell::new(v)))
    }

    pub fn ref_get<A: Clone>(r: Ref<A>) -> A {
        r.0.borrow().clone()
    }

    /// Reads the slot in place, for what needs no copy of the value.
    pub fn ref_with<A, R>(r: &Ref<A>, f: impl FnOnce(&A) -> R) -> R {
        f(&r.0.borrow())
    }

    pub fn ref_set<A>(r: Ref<A>, v: A) {
        *r.0.borrow_mut() = v;
    }

    pub struct Weak<A>(std::rc::Weak<RefCell<A>>);

    impl<A> Clone for Weak<A> {
        fn clone(&self) -> Self {
            Weak(self.0.clone())
        }
    }

    pub fn weak_of<A>(r: Ref<A>) -> Weak<A> {
        Weak(Rc::downgrade(&r.0))
    }

    pub fn weak_get<A>(w: Weak<A>) -> Option<Ref<A>> {
        w.0.upgrade().map(Ref)
    }

    pub struct Mutex<A>(Rc<RefCell<Line<A>>>);

    impl<A> Clone for Mutex<A> {
        fn clone(&self) -> Self {
            Mutex(self.0.clone())
        }
    }

    pub fn mutex_new<A>(v: A) -> Mutex<A> {
        Mutex(Rc::new(RefCell::new(Line::new(v))))
    }

    pub fn mutex_claim<A>(m: Mutex<A>) -> Signal {
        m.0.borrow_mut().claim()
    }

    pub fn mutex_take_claimed<A>(m: Mutex<A>, s: Signal) -> A {
        m.0.borrow_mut().take_claimed(&s)
    }

    pub fn mutex_put<A>(m: Mutex<A>, v: A) {
        m.0.borrow_mut().put(v);
    }

    /// A locked mutex's content (`MutexGuard` of `Par.taut`): handed back to
    /// the mutex when the guard is dropped.
    pub struct MutexGuard<A> {
        mutex: Mutex<A>,
        content: Option<A>,
    }

    impl<A> Drop for MutexGuard<A> {
        fn drop(&mut self) {
            if let Some(v) = self.content.take() {
                mutex_put(self.mutex.clone(), v);
            }
        }
    }

    pub fn mutexguard_claimed<A>(m: Mutex<A>, s: Signal) -> MutexGuard<A> {
        let content = mutex_take_claimed(m.clone(), s);
        MutexGuard {
            mutex: m,
            content: Some(content),
        }
    }

    pub fn mutexguard_get<A>(g: &MutexGuard<A>) -> &A {
        g.content
            .as_ref()
            .expect("tauto: a mutex guard holds its content")
    }

    pub fn mutexguard_get_mut<A>(g: &mut MutexGuard<A>) -> &mut A {
        g.content
            .as_mut()
            .expect("tauto: a mutex guard holds its content")
    }

    #[derive(Clone)]
    pub struct Atomic(Rc<Cell<u64>>);

    pub fn atomic_new(n: u64) -> Atomic {
        Atomic(Rc::new(Cell::new(n)))
    }

    pub fn atomic_load(a: Atomic) -> u64 {
        a.0.get()
    }

    pub fn atomic_store(a: Atomic, n: u64) {
        a.0.set(n);
    }

    pub fn atomic_fetch_add(a: Atomic, n: u64) -> u64 {
        let old = a.0.get();
        a.0.set(old.wrapping_add(n));
        old
    }
}

#[cfg(feature = "sync")]
mod cells {
    use super::Line;
    use crate::signal::Signal;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::{Arc, Mutex as Lock, MutexGuard as LockGuard, PoisonError};

    /// A lock that a panic in another thread does not poison: the value is
    /// still there, as a language without poisoning would have it.
    fn lock<T>(m: &Lock<T>) -> LockGuard<'_, T> {
        m.lock().unwrap_or_else(PoisonError::into_inner)
    }

    pub struct Ref<A>(Arc<Lock<A>>);

    impl<A> Clone for Ref<A> {
        fn clone(&self) -> Self {
            Ref(self.0.clone())
        }
    }

    pub fn ref_new<A>(v: A) -> Ref<A> {
        Ref(Arc::new(Lock::new(v)))
    }

    pub fn ref_get<A: Clone>(r: Ref<A>) -> A {
        lock(&r.0).clone()
    }

    /// Reads the slot in place, for what needs no copy of the value.
    pub fn ref_with<A, R>(r: &Ref<A>, f: impl FnOnce(&A) -> R) -> R {
        f(&lock(&r.0))
    }

    pub fn ref_set<A>(r: Ref<A>, v: A) {
        *lock(&r.0) = v;
    }

    pub struct Weak<A>(std::sync::Weak<Lock<A>>);

    impl<A> Clone for Weak<A> {
        fn clone(&self) -> Self {
            Weak(self.0.clone())
        }
    }

    pub fn weak_of<A>(r: Ref<A>) -> Weak<A> {
        Weak(Arc::downgrade(&r.0))
    }

    pub fn weak_get<A>(w: Weak<A>) -> Option<Ref<A>> {
        w.0.upgrade().map(Ref)
    }

    pub struct Mutex<A>(Arc<Lock<Line<A>>>);

    impl<A> Clone for Mutex<A> {
        fn clone(&self) -> Self {
            Mutex(self.0.clone())
        }
    }

    pub fn mutex_new<A>(v: A) -> Mutex<A> {
        Mutex(Arc::new(Lock::new(Line::new(v))))
    }

    pub fn mutex_claim<A>(m: Mutex<A>) -> Signal {
        lock(&m.0).claim()
    }

    pub fn mutex_take_claimed<A>(m: Mutex<A>, s: Signal) -> A {
        lock(&m.0).take_claimed(&s)
    }

    pub fn mutex_put<A>(m: Mutex<A>, v: A) {
        lock(&m.0).put(v);
    }

    /// A locked mutex's content (`MutexGuard` of `Par.taut`): handed back to
    /// the mutex when the guard is dropped.
    pub struct MutexGuard<A> {
        mutex: Mutex<A>,
        content: Option<A>,
    }

    impl<A> Drop for MutexGuard<A> {
        fn drop(&mut self) {
            if let Some(v) = self.content.take() {
                mutex_put(self.mutex.clone(), v);
            }
        }
    }

    pub fn mutexguard_claimed<A>(m: Mutex<A>, s: Signal) -> MutexGuard<A> {
        let content = mutex_take_claimed(m.clone(), s);
        MutexGuard {
            mutex: m,
            content: Some(content),
        }
    }

    pub fn mutexguard_get<A>(g: &MutexGuard<A>) -> &A {
        g.content
            .as_ref()
            .expect("tauto: a mutex guard holds its content")
    }

    pub fn mutexguard_get_mut<A>(g: &mut MutexGuard<A>) -> &mut A {
        g.content
            .as_mut()
            .expect("tauto: a mutex guard holds its content")
    }

    #[derive(Clone)]
    pub struct Atomic(Arc<AtomicU64>);

    pub fn atomic_new(n: u64) -> Atomic {
        Atomic(Arc::new(AtomicU64::new(n)))
    }

    pub fn atomic_load(a: Atomic) -> u64 {
        a.0.load(Ordering::SeqCst)
    }

    pub fn atomic_store(a: Atomic, n: u64) {
        a.0.store(n, Ordering::SeqCst);
    }

    pub fn atomic_fetch_add(a: Atomic, n: u64) -> u64 {
        a.0.fetch_add(n, Ordering::SeqCst)
    }
}

pub use crate::exec::{
    Pending, os_offload, os_sleep_pending, pending_is_ready, pending_ready, pending_signal,
    pending_take,
};
#[cfg(feature = "sync")]
pub use crate::exec::{pending_spawn, pending_spawn_o};
pub use crate::signal::Signal;
pub use cells::*;

/// The stream requests generated code calls by name (`std/prelude/Os.taut`);
/// the others give a `List` and are wrapped by the generated crate.
pub use crate::child::{os_child_close, os_child_close_stdin, os_child_read, os_child_write};
pub use crate::tcp::{os_tcp_close, os_tcp_read, os_tcp_shutdown, os_tcp_unlisten, os_tcp_write};
pub use crate::tls_host::{os_tls_close, os_tls_read, os_tls_shutdown, os_tls_write};

#[cfg(all(test, feature = "net"))]
mod net_tests {
    use super::*;
    use std::io::{Read, Write};

    /// `net_addr` reaches the address it names, with the URL's host in the
    /// request, though the host name resolves nowhere.
    #[test]
    fn a_fixed_address_is_reached_without_resolving_the_host() {
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
            String::from_utf8_lossy(&seen).into_owned()
        });
        let url = format!("http://pinned.invalid:{port}/");
        let out = os_fetch_vec(
            Text::from("GET"),
            Text::from(url),
            Text::from("127.0.0.1"),
            Vec::new(),
            Bytes::from(Vec::new()),
        )
        .unwrap();
        assert_eq!((&*out.0[0], &*out.1), ("200", &b"ok"[..]));
        let request = server.join().unwrap().to_ascii_lowercase();
        assert!(
            request.contains(&format!("host: pinned.invalid:{port}")),
            "{request}"
        );
    }

    #[test]
    fn an_address_must_be_an_ip_address() {
        let err = os_fetch_vec(
            Text::from("GET"),
            Text::from("http://example.com/"),
            Text::from("example.org"),
            Vec::new(),
            Bytes::from(Vec::new()),
        )
        .unwrap_err();
        assert!(err.contains("not an IP address"), "{err}");
    }
}
