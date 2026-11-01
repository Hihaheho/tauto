//! [`tauto_analyzer::Workspace`] for a browser: the same checker, both
//! kernels included, compiled to WebAssembly (`build.sh`). Files live only in
//! the workspace: the host gives each file's text with `set_text` (an
//! absolute path such as `/game/Level1.tauto`), and nothing is read from or
//! written to a disk.
//!
//! Each argument is UTF-8 the host writes into memory it takes with `alloc`.
//! Each call answers a length (four bytes, little endian) and that many bytes
//! of JSON, which the host gives back with `release`:
//!
//! - `set_text(path, text)`: `{"ok":true}`.
//! - `goals(path)`: `{"ok":{"report":R,"holes":[H…],"library":[L…]}}`, as
//!   `tauto check --json`, `tauto goals --json` and `tauto library --json`.
//! - `try_fill(path, hole, expr)` and `fill(…)`: `{"ok":A}`, as
//!   `tauto try --json`; `fill` keeps the candidate as the file's text when
//!   it is accepted.
//! - `suggest(path, hole, limit)`: `{"ok":[C…]}`, as `tauto suggest --json`
//!   without `--verify` (the candidates are not checked; `try_fill` does that).
//!
//! An error is `{"err":"…"}`.

#[cfg(target_arch = "wasm32")]
mod rand;

use std::{cell::RefCell, mem::ManuallyDrop, path::Path};

use tauto::report::{Json, find_hole};
use tauto_analyzer::{Workspace, lemma_search};

thread_local! {
    // Never dropped: the workspace's sessions are in another thread-local,
    // which may be gone first when a thread ends. Every entry point reaches
    // the workspace first, so the messages are shown in English from there.
    static WS: RefCell<ManuallyDrop<Workspace>> = RefCell::new({
        tauto_messages::install();
        ManuallyDrop::new(Workspace::new())
    });
}

/// `len` bytes the host fills.
#[unsafe(no_mangle)]
pub extern "C" fn alloc(len: usize) -> *mut u8 {
    let mut buf = Vec::<u8>::with_capacity(len.max(1));
    let ptr = buf.as_mut_ptr();
    std::mem::forget(buf);
    ptr
}

/// Gives back what `alloc` or a call handed out.
///
/// # Safety
/// `ptr` and `len` are what `alloc` was given, or `4 +` the length a call answered.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn release(ptr: *mut u8, len: usize) {
    drop(unsafe { Vec::from_raw_parts(ptr, 0, len.max(1)) });
}

fn read<'a>(ptr: *const u8, len: usize) -> &'a str {
    std::str::from_utf8(unsafe { std::slice::from_raw_parts(ptr, len) }).unwrap_or("")
}

fn answer(result: Result<Json, String>) -> *mut u8 {
    let json = match result {
        Ok(v) => Json::Obj(vec![("ok", v)]),
        Err(e) => Json::Obj(vec![("err", Json::Str(e))]),
    }
    .render();
    let mut out = (json.len() as u32).to_le_bytes().to_vec();
    out.extend_from_slice(json.as_bytes());
    // Exactly as long as it is, so that `release` gets its size back.
    Box::into_raw(out.into_boxed_slice()).cast()
}

/// # Safety
/// Each pointer and length is memory from `alloc` that the host filled.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn set_text(
    path: *const u8,
    path_len: usize,
    text: *const u8,
    text_len: usize,
) -> *mut u8 {
    let (path, text) = (read(path, path_len), read(text, text_len));
    WS.with(|ws| ws.borrow_mut().set_text(Path::new(path), text.to_string()));
    answer(Ok(Json::Bool(true)))
}

/// # Safety
/// As [`set_text`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn goals(path: *const u8, path_len: usize) -> *mut u8 {
    answer(goals_json(read(path, path_len)))
}

/// # Safety
/// As [`set_text`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn try_fill(
    path: *const u8,
    path_len: usize,
    hole: *const u8,
    hole_len: usize,
    expr: *const u8,
    expr_len: usize,
) -> *mut u8 {
    answer(attempt(
        read(path, path_len),
        read(hole, hole_len),
        read(expr, expr_len),
        false,
    ))
}

/// # Safety
/// As [`set_text`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fill(
    path: *const u8,
    path_len: usize,
    hole: *const u8,
    hole_len: usize,
    expr: *const u8,
    expr_len: usize,
) -> *mut u8 {
    answer(attempt(
        read(path, path_len),
        read(hole, hole_len),
        read(expr, expr_len),
        true,
    ))
}

/// # Safety
/// As [`set_text`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn suggest(
    path: *const u8,
    path_len: usize,
    hole: *const u8,
    hole_len: usize,
    limit: usize,
) -> *mut u8 {
    answer(suggest_json(
        read(path, path_len),
        read(hole, hole_len),
        limit,
    ))
}

/// What `goals` answers, for a host that is not WebAssembly (tests).
pub fn goals_json(path: &str) -> Result<Json, String> {
    let path = Path::new(path);
    WS.with(|ws| {
        let (report, holes) = ws.borrow().goals(path, None)?;
        Ok(Json::Obj(vec![
            ("report", report.json()),
            (
                "holes",
                Json::Arr(holes.iter().map(|h| report.hole_json(h)).collect()),
            ),
            ("library", report.library_json()),
        ]))
    })
}

/// What `try_fill` (`keep` false) and `fill` answer.
pub fn attempt(path: &str, hole: &str, expr: &str, keep: bool) -> Result<Json, String> {
    let path = Path::new(path);
    WS.with(|ws| {
        let mut ws = ws.borrow_mut();
        let a = if keep {
            ws.fill(path, hole, expr)?
        } else {
            ws.try_fill(path, hole, expr)?
        };
        Ok(a.json())
    })
}

/// What `suggest` answers.
pub fn suggest_json(path: &str, hole: &str, limit: usize) -> Result<Json, String> {
    let path = Path::new(path);
    WS.with(|ws| {
        let report = ws.borrow().report(path)?;
        let h = find_hole(&report, path, hole)?;
        let found = lemma_search::select(&report, &h, &[], limit)?;
        let unchecked = lemma_search::Validation::unchecked();
        Ok(Json::Arr(
            found
                .iter()
                .map(|s| lemma_search::candidate_json(s, &unchecked))
                .collect(),
        ))
    })
}

/// What `set_text` does.
pub fn set_text_str(path: &str, text: &str) {
    WS.with(|ws| ws.borrow_mut().set_text(Path::new(path), text.to_string()));
}
