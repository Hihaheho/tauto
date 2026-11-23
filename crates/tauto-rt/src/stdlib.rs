#![allow(clippy::ptr_arg)]
//! The standard library of the affine data (`docs/design/ownership.md`) and of
//! `Result`, `Slice` and the views (`docs/design/rust-backend.md`), in Rust. The functions that make a
//! generated type (`List`) are written by the generator.

pub type SynDeclaration = crate::identity::DeclRef;

pub fn syn_same_declaration(a: SynDeclaration, b: SynDeclaration) -> bool {
    a == b
}

/// The eliminator (`::ind`) of the inductive type `d`, by its declaration: the
/// same reference the checker gives the type's induction principle.
pub fn syn_eliminator(d: SynDeclaration) -> SynDeclaration {
    d.generated(crate::identity::Generation::Induction)
}

pub use crate::ct::*;
use crate::{Loc, Op, Text, error, messages};

pub fn text_of(b: String) -> Text {
    Text::from(b)
}

/// A buffer starts with room for a short text, so that building one does not
/// grow it several times over.
pub fn buf_new() -> String {
    String::with_capacity(64)
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
    let mut s = String::with_capacity(a.len() + b.len());
    s.push_str(&a);
    s.push_str(&b);
    Text::from(s)
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

// A scoped region is `region::Region` and a counted one `region::RcRegion`
// (`std/builtin/region.taut`). The generator makes a region of the std
// `BumpPolicy` a bump region (`region_bump`, `rcregion_bump`); a region of any
// other policy puts its values on the heap, and the policy's state is dropped.

pub use crate::region::{Place, Placed, RcPlace, RcPlaced, RcRegion, Region};

pub fn region_new<S>(_s: S) -> Region {
    Region::heap()
}

fn bytes(x: &crate::nat::Nat) -> usize {
    x.to_u64()
        .and_then(|x| usize::try_from(x).ok())
        .unwrap_or(usize::MAX)
}

/// A bump region whose first chunk has `size` bytes, growing by `step`.
pub fn region_bump(size: &crate::nat::Nat, step: &crate::nat::Nat) -> Region {
    Region::bump(bytes(size), bytes(step))
}

pub fn region_place<T>(r: &Region) -> Place<T> {
    r.place()
}

pub fn rcregion_new<S>(_s: S) -> RcRegion {
    RcRegion::heap()
}

/// A counted bump region whose first chunk has `size` bytes, growing by
/// `step`.
pub fn rcregion_bump(size: &crate::nat::Nat, step: &crate::nat::Nat) -> RcRegion {
    RcRegion::bump(bytes(size), bytes(step))
}

pub fn rcregion_place<T>(r: RcRegion) -> RcPlace<T> {
    r.place()
}

pub fn rcplace_heap<T>() -> RcPlace<T> {
    RcPlace::heap()
}

pub fn vec_clear<A>(v: &mut Vec<A>) {
    v.clear();
}

pub fn vec_truncate<A>(v: &mut Vec<A>, n: u64) {
    v.truncate(usize::try_from(n).unwrap_or(usize::MAX));
}

/// `vec_swap_within(&mut v, i, j)`: swaps when both are in `v`, and says
/// whether it did.
pub fn vec_swap_within<A>(v: &mut [A], i: u64, j: u64) -> bool {
    match (usize::try_from(i), usize::try_from(j)) {
        (Ok(i), Ok(j)) if i < v.len() && j < v.len() => {
            v.swap(i, j);
            true
        }
        _ => false,
    }
}

/// The native `Slots(S, M, A)` (`std/prelude/collections.taut`): `cap`
/// places for `A`, each with a copy mark `M`, and the policy's state `S`.
/// The operations are trusted: the proof arguments that make an index
/// in range and a place filled or empty are erased, and a call that breaks
/// them stops the run. An empty place holds no `A` (the runtime keeps its own
/// occupied flag), so a drop frees exactly the filled ones. `vacant` is the
/// mark `mark` returns for an index past the capacity (total in the model).
#[derive(Debug)]
pub struct Slots<S, M, A> {
    state: S,
    marks: Vec<M>,
    vacant: M,
    items: Vec<Option<A>>,
}

fn slot(i: u64, len: usize) -> usize {
    usize::try_from(i)
        .ok()
        .filter(|&i| i < len)
        .expect("Slots: index out of range")
}

/// `Slots::new(cap, s0, m0)`: `cap` empty places, every mark `m0`, state `s0`.
pub fn slots_new<S, M: Clone, A>(cap: u64, s0: S, m0: M) -> Slots<S, M, A> {
    let n = usize::try_from(cap).expect("Slots: capacity out of range");
    let mut items = Vec::new();
    items.resize_with(n, || None);
    Slots {
        state: s0,
        marks: vec![m0.clone(); n],
        vacant: m0,
        items,
    }
}

/// `Slots::copy(r, s0, m0)`: the capacity of `r`, its filled places copied,
/// every mark `m0`, state `s0`.
pub fn slots_copy<S, M: Clone, A: Clone>(r: &Slots<S, M, A>, s0: S, m0: M) -> Slots<S, M, A> {
    Slots {
        state: s0,
        marks: vec![m0.clone(); r.items.len()],
        vacant: m0,
        items: r.items.clone(),
    }
}

pub fn slots_state<S: Clone, M, A>(r: &Slots<S, M, A>) -> S {
    r.state.clone()
}

pub fn slots_mark<S, M: Clone, A>(r: &Slots<S, M, A>, i: u64) -> M {
    match usize::try_from(i).ok().filter(|&j| j < r.marks.len()) {
        Some(j) => r.marks[j].clone(),
        None => r.vacant.clone(),
    }
}

pub fn slots_cap<S, M, A>(r: &Slots<S, M, A>) -> u64 {
    r.items.len() as u64
}

pub fn slots_get<S, M, A>(r: &Slots<S, M, A>, i: u64) -> &A {
    r.items[slot(i, r.items.len())]
        .as_ref()
        .expect("Slots::get: the slot is empty")
}

pub fn slots_get_mut<S, M, A>(r: &mut Slots<S, M, A>, i: u64) -> &mut A {
    let i = slot(i, r.items.len());
    r.items[i]
        .as_mut()
        .expect("Slots::get_mut: the slot is empty")
}

/// Fills slot `i` with `x`, sets its mark to `m`, and the state to `t`.
pub fn slots_put<S, M, A>(r: &mut Slots<S, M, A>, i: u64, m: M, x: A, t: S) {
    let i = slot(i, r.items.len());
    r.items[i] = Some(x);
    r.marks[i] = m;
    r.state = t;
}

/// Empties slot `i`, returning its value, sets its mark to `m`, and the state to `t`.
pub fn slots_take<S, M, A>(r: &mut Slots<S, M, A>, i: u64, m: M, t: S) -> A {
    let i = slot(i, r.items.len());
    let x = r.items[i].take().expect("Slots::take: the slot is empty");
    r.marks[i] = m;
    r.state = t;
    x
}

/// Keeps the first `cap` places as they are, dropping the filled ones
/// beyond; a new place is empty with mark `m0`. The state becomes `t`.
pub fn slots_resize<S, M: Clone, A>(r: &mut Slots<S, M, A>, cap: u64, m0: M, t: S) {
    let n = usize::try_from(cap).expect("Slots: capacity out of range");
    r.items.resize_with(n, || None);
    r.marks.resize(n, m0.clone());
    r.vacant = m0;
    r.state = t;
}

pub fn replace<A>(x: &mut A, v: A) -> A {
    std::mem::replace(x, v)
}

// `Array(A)` of the prelude: shared; `array_set` writes the only reference
// in place and copies a shared one. `array_of_list` and
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

/// The array with the element at `i` replaced by `x`; `a` itself when `i`
/// is past the end. The only reference to an array is written in place;
/// a shared one is copied first.
pub fn array_set<A: Clone>(mut a: Array<A>, i: u64, x: A) -> Array<A> {
    let Some(i) = usize::try_from(i).ok().filter(|&i| i < a.len()) else {
        return a;
    };
    match crate::Rc::get_mut(&mut a) {
        Some(items) => items[i] = x,
        None => {
            let mut items = a.to_vec();
            items[i] = x;
            a = items.into();
        }
    }
    a
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

/// The first index from `start` before `end` whose byte is `c`; `end` when
/// there is none. One search over the slice: no index is checked byte by byte.
pub fn bytes_find(b: Bytes, c: u64, start: u64, end: u64) -> u64 {
    let Ok(c) = u8::try_from(c) else { return end };
    let s = usize::try_from(start).unwrap_or(usize::MAX);
    let e = usize::try_from(end).unwrap_or(usize::MAX).min(b.len());
    if s >= e {
        return end;
    }
    b[s..e]
        .iter()
        .position(|&x| x == c)
        .map_or(end, |p| (s + p) as u64)
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

pub fn text_len(t: &Text) -> u64 {
    t.len() as u64
}

pub fn text_byte(t: &Text, i: u64) -> Option<u8> {
    usize::try_from(i)
        .ok()
        .and_then(|i| t.as_bytes().get(i).copied())
}

pub fn text_slice(t: &Text, start: u64, end: u64) -> Option<Text> {
    match (usize::try_from(start), usize::try_from(end)) {
        (Ok(s), Ok(e)) => t.get(s..e).map(Text::from),
        _ => None,
    }
}

pub fn text_compare(a: &Text, b: &Text) -> i64 {
    a.as_bytes().cmp(b.as_bytes()) as i64
}

/// `t` as `{:?}` writes it, without the quotes: what `Debug` of a `Text`
/// writes between them.
pub fn escape_debug(t: &str) -> String {
    let s = format!("{t:?}");
    s[1..s.len() - 1].to_string()
}

pub fn text_escape_debug(t: &Text) -> Text {
    Text::from(escape_debug(&t))
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
    i64_of_i8: i8 => i64,
    i64_of_i16: i16 => i64,
    i8_of_i64: i64 => i8,
    i16_of_i64: i64 => i16,
    u64_of_u16: u16 => u64,
    u16_of_u64: u64 => u16,
    i64_of_i32: i32 => i64,
    i32_of_i64: i64 => i32,
    i64_of_u64: u64 => i64,
    u64_of_i64: i64 => u64,
    u64_of_u32: u32 => u64,
    u32_of_u64: u64 => u32,
    u64_of_u8: u8 => u64,
    u64_of_uhost: u64 => u64,
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

/// `a + b`, `a - b` and `a * b` modulo `2^64`: the machine's wrapping arithmetic.
pub fn u64_wrapping_add(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}
pub fn u64_wrapping_sub(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
}
pub fn u64_wrapping_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
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
/// or `other`), the size, the time of the last change in milliseconds, and
/// `1` when the owner may execute it, else `0`.
pub fn os_stat_vec(path: Text) -> Result<Vec<Text>, Text> {
    crate::host::get()
        .stat(&path)
        .map(|found| match found {
            None => Vec::new(),
            Some(s) => vec![
                Text::from(s.kind),
                Text::from(s.size.to_string()),
                Text::from(s.modified_ms.to_string()),
                Text::from(if s.executable { "1" } else { "0" }),
            ],
        })
        .map_err(Text::from)
}

/// Where the link at `path` points: empty when what is there is not a link; see
/// [`crate::host::Host::read_link`].
pub fn os_read_link_vec(path: Text) -> Result<Vec<Text>, Text> {
    crate::host::get()
        .read_link(&path)
        .map(|found| found.map(Text::from).into_iter().collect())
        .map_err(Text::from)
}

/// A file made where nothing is; see [`crate::host::Host::create_new`].
pub fn os_write_new(path: Text, contents: Text) -> Result<(), Text> {
    crate::host::get()
        .create_new(&path, contents.as_bytes())
        .map_err(Text::from)
}

/// The names of the environment variables; see [`crate::host::Host::env_names`].
pub fn os_env_names_vec() -> Vec<Text> {
    crate::host::get()
        .env_names()
        .into_iter()
        .map(Text::from)
        .collect()
}

/// Takes the lock on a file; see [`crate::host::Host::lock`].
pub fn os_lock(path: Text) -> Result<u64, Text> {
    crate::host::get()
        .lock(&path)
        .map_err(|e| Text::from(e.to_string()))
}

/// Lets go of a lock; see [`crate::host::Host::unlock`].
pub fn os_unlock(id: u64) {
    crate::host::get().unlock(id)
}

/// Sets who may write and execute a path; see [`crate::host::Host::set_mode`].
pub fn os_set_mode(path: Text, readonly: bool, executable: bool) -> Result<(), Text> {
    crate::host::get()
        .set_mode(&path, readonly, executable)
        .map_err(Text::from)
}

pub fn os_move_path(from: Text, to: Text) -> Result<(), Text> {
    crate::host::get().rename(&from, &to).map_err(Text::from)
}

pub fn os_copy_file(from: Text, to: Text) -> Result<(), Text> {
    crate::host::get().copy(&from, &to).map_err(Text::from)
}

/// The contents of `path` under `root`, as UTF-8; see
/// [`crate::host::Host::read_bytes_under`].
pub fn os_read_under(root: Text, path: Text) -> Result<Text, Text> {
    let bytes = crate::host::get().read_bytes_under(&root, &path)?;
    String::from_utf8(bytes)
        .map(Text::from)
        .map_err(|_| Text::from(format!("{path}: not UTF-8")))
}

/// The bytes of `path` under `root`.
pub fn os_read_bytes_under(root: Text, path: Text) -> Result<Bytes, Text> {
    crate::host::get()
        .read_bytes_under(&root, &path)
        .map(Bytes::from)
        .map_err(Text::from)
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
/// this program, which sets it, or names it in `TAUTO_EXE` when this program
/// is a binary `tauto run` started. Unset, `tauto` is looked up on `PATH`
/// like any other program.
/// Calling this while a Tauto program is running panics.
pub fn set_tauto_path(path: String) {
    crate::with_config_lock("stdlib::set_tauto_path", || {
        *TAUTO_PATH.write().unwrap_or_else(|e| e.into_inner()) = Some(path);
    });
}

/// The file a program name runs. Every backend resolves it the same way: a
/// name with a directory in it is used as spelled; a bare name is searched
/// for on this run's own `PATH`, whatever environment the program is given,
/// which stays exactly as given. (The system would search a child's `PATH`
/// when it has one and a built-in `/bin:/usr/bin` when it has none, so the
/// same call would find different programs by what it passes.) A name
/// nothing on `PATH` answers is left as spelled, so the system refuses it.
pub fn run_program(program: &str) -> String {
    if program == "tauto" {
        let set = TAUTO_PATH.read().unwrap_or_else(|e| e.into_inner()).clone();
        let named = set.or_else(|| std::env::var("TAUTO_EXE").ok().filter(|p| !p.is_empty()));
        if let Some(path) = named {
            return path;
        }
    }
    resolve_on_path(program, std::env::var_os("PATH").as_deref())
        .map_or_else(|| program.to_string(), |p| p.to_string_lossy().into_owned())
}

/// The first file named `program` in a directory of `path` that can run, for a
/// bare name; `None` for a name with a directory in it or a name not found.
pub fn resolve_on_path(
    program: &str,
    path: Option<&std::ffi::OsStr>,
) -> Option<std::path::PathBuf> {
    if program.is_empty() || program.contains(['/', std::path::MAIN_SEPARATOR]) {
        return None;
    }
    std::env::split_paths(path?)
        .filter(|dir| !dir.as_os_str().is_empty())
        .map(|dir| dir.join(program))
        .find(|file| runnable(file))
}

fn runnable(file: &std::path::Path) -> bool {
    let Ok(meta) = std::fs::metadata(file) else {
        return false;
    };
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        meta.is_file() && meta.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        meta.is_file()
    }
}

/// Runs a program: the exit status (empty when a signal ended it) and
/// standard error as text; and standard output. `env` is each variable's
/// name then value: the program's whole environment.
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

pub fn os_on_shutdown(s: Signal) {
    crate::shutdown::register(s)
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

/// The word of the host as an unsigned integer of `bits`, below `2^bits`.
fn uhost_fit(n: Option<u128>, what: &str) -> u64 {
    let bits = crate::host::get().host_bits();
    match n {
        Some(n) if bits >= 64 || n < (1u128 << bits) => n as u64,
        _ => crate::error_here(format!("`{what}` does not fit a word of {bits} bits")),
    }
}

/// The operations of `uhost` that carry a proof in Tauto and so check
/// nothing here: the result fits, and each is one machine operation.
pub fn uhost_succ_below(a: u64) -> u64 {
    a.wrapping_add(1)
}

pub fn uhost_pred_nz(a: u64) -> u64 {
    a.wrapping_sub(1)
}

pub fn uhost_add_within(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

pub fn uhost_sub(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
}

pub fn uhost_of_u64_below(x: u64) -> u64 {
    x
}

pub fn os_uhost_add(a: u64, b: u64) -> u64 {
    uhost_fit(Some(u128::from(a) + u128::from(b)), "uhost +")
}

pub fn os_uhost_sub(a: u64, b: u64) -> u64 {
    uhost_fit(u128::from(a).checked_sub(u128::from(b)), "uhost -")
}

pub fn os_uhost_mul(a: u64, b: u64) -> u64 {
    uhost_fit(Some(u128::from(a) * u128::from(b)), "uhost *")
}

pub fn os_uhost_of_u64(x: u64) -> u64 {
    uhost_fit(Some(u128::from(x)), "uhost of u64")
}

pub fn os_host_bits() -> u64 {
    crate::host::get().host_bits()
}

pub fn os_hash_seed_k0() -> u64 {
    crate::host::get().hash_seed().0
}

pub fn os_hash_seed_k1() -> u64 {
    crate::host::get().hash_seed().1
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

pub fn os_entry_vec(what: Text, args: Vec<Text>) -> Vec<Text> {
    let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
    crate::entry::call(&what, &args)
        .into_iter()
        .map(Text::from)
        .collect()
}

pub fn os_check(kind: Text, target: Text) -> Option<Text> {
    crate::permissions::check_or_ask(&kind, &target).map(Text::from)
}

/// The client of a request to `url`, connected to `address` if it is not
/// empty: the `Host` header and the TLS name stay the URL's host.
#[cfg(feature = "net")]
pub(crate) fn http_client(url: &str, address: &str) -> Result<reqwest::blocking::Client, Text> {
    let mut builder = reqwest::blocking::Client::builder()
        // A redirect would reach a host the permission may not cover.
        .redirect(reqwest::redirect::Policy::none());
    if !address.is_empty() {
        let Some((_, host, port)) = crate::permissions::parse_url(url) else {
            return Err(Text::from(format!("cannot connect to {url}")));
        };
        let ip = fixed_address(address)?;
        let name = host
            .trim_start_matches('[')
            .trim_end_matches(']')
            .to_string();
        builder = builder.resolve(&name, std::net::SocketAddr::new(ip, port));
    }
    builder.build().map_err(|e| Text::from(e.to_string()))
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
    let client = http_client(&url, &address)?;
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

// `Ref`, `Mutex` and `Atomic` of the prelude (`par.taut`): slots many closures
// and tasks share. A copy is a new handle on the same slot. With the `sync`
// feature (a program that starts tasks) the slots are safe to share between
// threads.

/// A mutex's content and the places in line for it (`mutex_claim`): the
/// content is empty between a take and its put, and a put hands it to the
/// first place waiting, whose signal it raises.
pub struct Line<A> {
    content: Option<A>,
    handed: Vec<(crate::signal::Signal, A)>,
    gate: std::sync::Arc<Gate>,
}

/// The part of a mutex that does not hold the content: the places waiting,
/// the task that took the content while it has it, and whether that task
/// failed first (then taking from the mutex fails). Apart from `Line`, so a
/// failed task can poison the mutex without knowing the content's type.
#[derive(Default)]
pub struct Gate(std::sync::Mutex<GateState>);

#[derive(Default)]
struct GateState {
    waiting: std::collections::VecDeque<crate::signal::Signal>,
    taker: Option<usize>,
    poisoned: bool,
}

const POISONED: &str = "the Mutex is poisoned: a task that held its content failed";

impl Gate {
    fn state(&self) -> std::sync::MutexGuard<'_, GateState> {
        self.0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn check(&self) {
        if self.state().poisoned {
            std::panic::panic_any(crate::TautoError {
                message: POISONED.into(),
                at: None,
            });
        }
    }

    pub(crate) fn poisoned(&self) -> bool {
        self.state().poisoned
    }

    /// The running task has the content now: its failure poisons the mutex.
    #[cfg(feature = "sync")]
    fn taken(self: &std::sync::Arc<Self>) {
        let weak = std::sync::Arc::downgrade(self) as std::sync::Weak<dyn crate::exec::Poison>;
        let id = crate::exec::note_taken(weak);
        self.state().taker = id;
    }
}

#[cfg(feature = "sync")]
impl crate::exec::Poison for Gate {
    fn poison(&self, task: usize) {
        let mut g = self.state();
        if g.taker == Some(task) {
            g.poisoned = true;
            for s in g.waiting.drain(..) {
                s.raise();
            }
        }
    }
}

impl<A> Line<A> {
    fn new(v: A) -> Line<A> {
        Line {
            content: Some(v),
            handed: Vec::new(),
            gate: Default::default(),
        }
    }

    fn claim(&mut self) -> crate::signal::Signal {
        self.gate.check();
        let s = crate::signal::Signal::new();
        let mut g = self.gate.state();
        match self.content.take() {
            Some(v) if g.waiting.is_empty() => {
                self.handed.push((s.clone(), v));
                s.raise();
            }
            content => {
                self.content = content;
                g.waiting.push_back(s.clone());
            }
        }
        s
    }

    fn put(&mut self, v: A) {
        let mut g = self.gate.state();
        g.taker = None;
        match g.waiting.pop_front() {
            Some(s) => {
                self.handed.push((s.clone(), v));
                s.raise();
            }
            None => self.content = Some(v),
        }
    }

    /// Leaves the place `s`: the content if it was handed there already.
    fn withdraw(&mut self, s: &crate::signal::Signal) -> Option<A> {
        self.gate.check();
        {
            let mut g = self.gate.state();
            if let Some(i) = g.waiting.iter().position(|w| w.same(s)) {
                g.waiting.remove(i);
                return None;
            }
        }
        let i = self.handed.iter().position(|(h, _)| h.same(s))?;
        let v = self.handed.swap_remove(i).1;
        #[cfg(feature = "sync")]
        self.gate.taken();
        Some(v)
    }

    fn take_claimed(&mut self, s: &crate::signal::Signal) -> A {
        self.gate.check();
        let i = self
            .handed
            .iter()
            .position(|(h, _)| h.same(s))
            .expect("tauto: a mutex's content taken before it was handed");
        let v = self.handed.swap_remove(i).1;
        #[cfg(feature = "sync")]
        self.gate.taken();
        v
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

    pub fn mutex_withdraw<A>(m: Mutex<A>, s: Signal) -> Option<A> {
        m.0.borrow_mut().withdraw(&s)
    }

    /// A locked mutex's content (`MutexGuard` of `par.taut`): handed back to
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

    pub fn mutex_withdraw<A>(m: Mutex<A>, s: Signal) -> Option<A> {
        lock(&m.0).withdraw(&s)
    }

    /// A locked mutex's content (`MutexGuard` of `par.taut`): handed back to
    /// the mutex when the guard is dropped.
    pub struct MutexGuard<A> {
        mutex: Mutex<A>,
        content: Option<A>,
    }

    impl<A> Drop for MutexGuard<A> {
        // A task that fails leaves the content out: its mutex is poisoned.
        fn drop(&mut self) {
            if let Some(v) = self.content.take()
                && !std::thread::panicking()
                && !lock(&self.mutex.0).gate.poisoned()
            {
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
    Pending, os_offload, os_sleep_pending, os_tcp_ready, os_tls_ready, pending_is_ready,
    pending_ready, pending_signal, pending_take,
};
#[cfg(feature = "sync")]
pub use crate::exec::{pending_spawn, pending_spawn_o};
pub use crate::signal::{
    Signal, signal_either, signal_fresh, signal_is_raised, signal_listen, signal_raise,
};
pub use cells::*;

/// The stream requests generated code calls by name (`std/builtin/os.taut`);
/// the others give a `List` and are wrapped by the generated crate.
pub use crate::child::{os_child_close, os_child_close_stdin, os_child_read, os_child_write};
pub use crate::http::{os_http_close, os_http_read, os_http_write};
pub use crate::tcp::{
    os_tcp_close, os_tcp_read, os_tcp_send, os_tcp_shutdown, os_tcp_unlisten, os_tcp_write,
};
pub use crate::tls_host::{os_tls_close, os_tls_read, os_tls_send, os_tls_shutdown, os_tls_write};

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

// The source capability and its read-only view share a flag at run time.
pub type CancelSource = Signal;

#[cfg(test)]
mod tests {
    use super::resolve_on_path;
    use std::ffi::OsString;

    // Not in the test suite: a case cannot set the `PATH` of the run that
    // holds it, and this is the one place the search is told which to use.
    #[cfg(unix)]
    #[test]
    fn a_bare_name_is_searched_on_the_given_path_in_order() {
        use std::os::unix::fs::PermissionsExt;
        let root = std::env::temp_dir().join(format!("tauto-resolve-{}", std::process::id()));
        let (a, b) = (root.join("a"), root.join("b"));
        std::fs::create_dir_all(&a).unwrap();
        std::fs::create_dir_all(&b).unwrap();
        let make = |dir: &std::path::Path, name: &str, mode: u32| {
            let f = dir.join(name);
            std::fs::write(&f, "").unwrap();
            std::fs::set_permissions(&f, std::fs::Permissions::from_mode(mode)).unwrap();
        };
        make(&a, "plain", 0o644);
        make(&a, "tool", 0o755);
        make(&b, "tool", 0o755);
        make(&b, "plain", 0o755);
        let path = std::env::join_paths([&a, &b]).unwrap();
        let find = |n: &str| resolve_on_path(n, Some(path.as_os_str()));
        assert_eq!(find("tool"), Some(a.join("tool")));
        // A file that cannot run is passed over.
        assert_eq!(find("plain"), Some(b.join("plain")));
        assert_eq!(find("absent"), None);
        // A name with a directory in it is not searched for.
        assert_eq!(find("a/tool"), None);
        assert_eq!(resolve_on_path("tool", None), None);
        assert_eq!(resolve_on_path("tool", Some(&OsString::from(""))), None);
        std::fs::remove_dir_all(&root).unwrap();
    }
}
