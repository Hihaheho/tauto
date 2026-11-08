//! What the language server (`totes/lsp`) asks the Rust analyzer. The server
//! reads the protocol, keeps track of the session and answers what needs no
//! analysis; for the rest it calls these functions, which take and give JSON
//! as text.
//!
//! The open files, the workspace that checks them and the types of each file
//! are kept here, for the thread the server runs on, until they move into the
//! server's own queries.

/// A message of this crate as text: `say!("lsp-…")`.
macro_rules! say {
    ($($t:tt)*) => {
        ::tauto_message::msg!($($t)*).to_string()
    };
}

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use serde_json::{Value, json};
use tauto_analyzer::editor::{offset_of, position_of};
use tauto_analyzer::navigate::{Navigator, Place, TypeInfo};

struct State {
    texts: HashMap<String, String>,
    workspace: tauto_analyzer::Workspace,
    types: HashMap<String, Rc<Option<TypeInfo>>>,
    root: Option<PathBuf>,
}

thread_local! {
    // Never dropped: the analyzer's own thread-locals may be gone by the time
    // this thread's are, and the process ends after the server anyway.
    static STATE: &'static RefCell<Option<State>> = Box::leak(Box::new(RefCell::new(None)));
}

fn with<R>(f: impl FnOnce(&mut State) -> R) -> R {
    STATE.with(|s| {
        let mut s = s.borrow_mut();
        let state = s.get_or_insert_with(|| {
            // The program of the file an editor shows is read again at every edit: the files
            // before it are expanded once (`docs/design/analysis-cache.md`).
            tauto::program::keep_expansions(true);
            State {
                texts: HashMap::new(),
                workspace: tauto_analyzer::Workspace::new(),
                types: HashMap::new(),
                root: None,
            }
        });
        f(state)
    })
}

/// The names of the kinds of semantic tokens, as a JSON array: the legend.
pub fn lsp_token_kinds() -> String {
    json!(tauto_analyzer::editor::KINDS).to_string()
}

/// Takes the folder of the workspace (a `file://` URI); an empty one is none.
pub fn lsp_set_root(uri: &str) -> bool {
    with(|s| s.root = (!uri.is_empty()).then(|| path_of(uri)));
    true
}

/// The file at `uri` is open with the text `text`.
pub fn lsp_set_text(uri: &str, text: &str) -> bool {
    with(|s| {
        s.texts.insert(uri.to_string(), text.to_string());
        s.workspace.set_text(&path_of(uri), text.to_string());
        // Any open file may be one another imports.
        s.types.clear();
    });
    true
}

/// The diagnostics of the file at `uri` as the open texts are now, a JSON
/// array.
pub fn lsp_diagnostics(uri: &str) -> String {
    with(|s| {
        let text = s.texts.get(uri).cloned().unwrap_or_default();
        Value::Array(diagnostics(&s.workspace, uri, &text)).to_string()
    })
}

/// The file at `uri` is closed: what is on disk stands for it again.
pub fn lsp_close(uri: &str) -> bool {
    with(|s| {
        s.texts.remove(uri);
        s.types.clear();
        if s.texts.is_empty() {
            // Nothing is open: everything kept goes, the kept kernels included.
            s.workspace = tauto_analyzer::Workspace::new();
        } else {
            s.workspace.refresh(&path_of(uri));
            s.workspace.forget(&path_of(uri));
        }
    });
    true
}

/// The answer to the request `method` about the file at `uri`, with its
/// `params` (JSON): `{"result": …}`, or `{"error": {"code": …, "message": …}}`.
/// A method this does not know is `{"unknown": true}`.
pub fn lsp_request(method: &str, uri: &str, params: &str) -> String {
    let params: Value = serde_json::from_str(params).unwrap_or(Value::Null);
    let answer = with(|s| -> Option<Result<Value, String>> {
        Some(match method {
            "textDocument/semanticTokens/full" => {
                let data = s.texts.get(uri).map_or(Vec::new(), |t| semantic(uri, t));
                Ok(json!({"data": data}))
            }
            "textDocument/codeAction" => Ok(json!(code_actions(uri, &params))),
            "textDocument/onTypeFormatting" => {
                let edits = s.texts.get(uri).map_or(Vec::new(), |t| {
                    let line = params["position"]["line"].as_u64().unwrap_or(0) as usize;
                    let col = params["position"]["character"].as_u64().unwrap_or(0) as usize;
                    let ch = params["ch"].as_str().unwrap_or("");
                    escape_on_type(t, line, col, ch).into_iter().collect()
                });
                Ok(json!(edits))
            }
            "textDocument/completion" => {
                let items = s.texts.get(uri).map_or(Vec::new(), |t| {
                    let line = params["position"]["line"].as_u64().unwrap_or(0) as usize;
                    let col = params["position"]["character"].as_u64().unwrap_or(0) as usize;
                    completion(uri, t, line, col)
                });
                Ok(json!(items))
            }
            "textDocument/hover"
            | "textDocument/definition"
            | "textDocument/references"
            | "textDocument/prepareRename"
            | "textDocument/rename" => {
                let mut ctx = Names {
                    texts: &s.texts,
                    types: &mut s.types,
                    root: s.root.as_deref(),
                };
                // A bug in finding a name answers with an error, not the end of the server.
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    ctx.request(method, uri, &params)
                }))
                .unwrap_or_else(|_| Err(say!("lsp-internal-error")))
            }
            _ => return None,
        })
    });
    match answer {
        None => json!({"unknown": true}),
        Some(Ok(result)) => json!({"result": result}),
        Some(Err(message)) => json!({"error": {"code": -32803, "message": message}}),
    }
    .to_string()
}

/// The path of a `file://` URI, with its `%XX` escapes decoded. An escape that
/// is not two hex digits is kept as written; when the decoded bytes are not
/// UTF-8, the whole path is kept as written.
fn path_of(uri: &str) -> PathBuf {
    let rest = uri.strip_prefix("file://").unwrap_or(uri);
    PathBuf::from(percent_decode(rest))
}

fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        let hex = |b: u8| (b as char).to_digit(16);
        if bytes[i] == b'%'
            && let (Some(Some(h)), Some(Some(l))) = (
                bytes.get(i + 1).map(|b| hex(*b)),
                bytes.get(i + 2).map(|b| hex(*b)),
            )
        {
            out.push((h * 16 + l) as u8);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8(out).unwrap_or_else(|_| s.to_string())
}

fn diagnostics(workspace: &tauto_analyzer::Workspace, uri: &str, text: &str) -> Vec<Value> {
    let mut out = check_diagnostics(workspace, uri, text);
    // A syntax whose registered colours could not be used is a warning at its literal.
    if let Ok((_, notes)) = tauto_analyzer::editor::dsl_tokens(&path_of(uri), text) {
        for note in notes {
            let (line, col) = position_of(text, note.start);
            let (end_line, end_col) = position_of(text, note.end);
            out.push(json!({"range": {"start": {"line": line, "character": col},
                                      "end": {"line": end_line, "character": end_col}},
                            "severity": 2, "source": "tauto", "message": note.message.to_string()}));
        }
    }
    out
}

fn check_diagnostics(workspace: &tauto_analyzer::Workspace, uri: &str, text: &str) -> Vec<Value> {
    let path = path_of(uri);
    let report = workspace.report(&path);
    let at = |line: usize, col: usize, message: &str| {
        json!({"range": {"start": {"line": line, "character": col},
                         "end": {"line": line, "character": col + 1}},
               "severity": 1, "source": "tauto", "message": message})
    };
    let report = match report {
        Ok(r) => r,
        Err(e) => {
            // A program that does not load says where, when it knows: in this
            // file it is shown there, anywhere else at the start of this one.
            let own = path.canonicalize().unwrap_or_else(|_| path.clone());
            let here = e
                .place
                .as_ref()
                .filter(|p| p.path.canonicalize().unwrap_or_else(|_| p.path.clone()) == own);
            let (line, col) = here.map_or((0, 0), |p| position_of(text, p.offset as usize));
            let message = match here {
                Some(_) => e.message.to_string(),
                None => e.to_string(),
            };
            return vec![at(line, col, &message)];
        }
    };
    let own = path.canonicalize().unwrap_or(path);
    let rendered: Value = serde_json::from_str(&report.json().render()).unwrap_or(Value::Null);
    let mut out = Vec::new();
    for e in rendered["errors"].as_array().into_iter().flatten() {
        let file = PathBuf::from(e["file"].as_str().unwrap_or(""));
        if file.canonicalize().unwrap_or(file) != own {
            continue;
        }
        let line = e["line"].as_u64().unwrap_or(1).saturating_sub(1) as usize;
        let col = e["col"].as_u64().unwrap_or(1).saturating_sub(1) as usize;
        let message = format!(
            "{}: {}",
            e["declaration"].as_str().unwrap_or(""),
            e["message"].as_str().unwrap_or("")
        );
        let mut diagnostic = at(line, col, &message);
        // A fix the check offers is an edit of the range as it was read.
        if let Some(fix) = e.get("fix") {
            let pos = |l: &str, c: &str| {
                json!({"line": fix[l].as_u64().unwrap_or(1).saturating_sub(1),
                       "character": fix[c].as_u64().unwrap_or(1).saturating_sub(1)})
            };
            diagnostic["data"] = json!({
                "title": fix["title"],
                "range": {"start": pos("line", "col"), "end": pos("end_line", "end_col")},
                "text": fix["text"],
            });
        }
        out.push(diagnostic);
    }
    out
}

/// The quick fixes of the diagnostics the client sent back: each one's edit.
fn code_actions(uri: &str, params: &Value) -> Vec<Value> {
    params["context"]["diagnostics"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|d| d["data"]["range"].is_object())
        .map(|d| {
            let fix = &d["data"];
            json!({
                "title": fix["title"],
                "kind": "quickfix",
                "diagnostics": [d],
                "edit": {"changes": {uri: [{"range": fix["range"], "newText": fix["text"]}]}},
            })
        })
        .collect()
}

fn semantic(uri: &str, text: &str) -> Vec<u32> {
    let path = path_of(uri);
    let Ok((tokens, _)) = tauto_analyzer::editor::dsl_tokens(&path, text) else {
        return Vec::new();
    };
    let mut data = Vec::new();
    let (mut last_line, mut last_col) = (0, 0);
    for t in tokens {
        let (line, col) = position_of(text, t.start);
        let (end_line, end_col) = position_of(text, t.end);
        // `dsl_tokens` splits a token over several lines; one that is left is not coloured.
        if end_line != line {
            continue;
        }
        let kind = tauto_analyzer::editor::KINDS
            .iter()
            .position(|k| *k == t.kind)
            .unwrap_or(0);
        let delta_col = if line == last_line {
            col - last_col
        } else {
            col
        };
        data.extend([
            (line - last_line) as u32,
            delta_col as u32,
            (end_col - col) as u32,
            kind as u32,
            0,
        ]);
        (last_line, last_col) = (line, col);
    }
    data
}

fn completion(uri: &str, text: &str, line: usize, col: usize) -> Vec<Value> {
    let offset = offset_of(text, line, col);
    if let Some(start) = escape_start(text, offset) {
        return escape_completion(text, start, offset);
    }
    tauto_analyzer::editor::dsl_completion(&path_of(uri), text, offset)
        .unwrap_or_default()
        .into_iter()
        .map(|t| json!({"label": t, "kind": 14}))
        .collect()
}

/// The characters after which an escape just written (`\\forall`) becomes its sign (`∀`),
/// as `documentOnTypeFormattingProvider` names them: the first, then the rest.
pub const ESCAPE_TRIGGERS: [&str; 11] = [" ", "\t", "(", ")", "[", "]", "{", "}", ",", ".", ":"];

/// Where the escape that ends at `end` begins: the byte offset of its `\\`, followed only by
/// ASCII letters up to `end`. `None` when there is none, or when the line before it is a comment
/// or within a text literal, as far as the line alone tells.
fn escape_start(text: &str, end: usize) -> Option<usize> {
    let before = text.get(..end)?;
    let name_len = before
        .bytes()
        .rev()
        .take_while(|b| b.is_ascii_alphabetic())
        .count();
    let start = end - name_len;
    if start == 0 || before.as_bytes()[start - 1] != b'\\' {
        return None;
    }
    let start = start - 1;
    let line = &before[before[..start].rfind('\n').map_or(0, |i| i + 1)..start];
    if line.contains("//") || line.matches('"').count() % 2 == 1 {
        return None;
    }
    Some(start)
}

/// The edit that turns the escape before the character `ch`, just typed so that it ends at the
/// position (`line`, `col`), into its sign.
fn escape_on_type(text: &str, line: usize, col: usize, ch: &str) -> Option<Value> {
    if !ESCAPE_TRIGGERS.contains(&ch) {
        return None;
    }
    let end = offset_of(text, line, col).checked_sub(ch.len())?;
    if text.get(end..end + ch.len()) != Some(ch) {
        return None;
    }
    let start = escape_start(text, end)?;
    let (_, sign) = tauto::fmt::ESCAPES
        .iter()
        .find(|(name, _)| *name == &text[start + 1..end])?;
    Some(json!({"range": range(text, start, end), "newText": sign}))
}

/// The signs whose escapes begin with what is written from `start` (a `\\`) to `end`, each
/// replacing it.
fn escape_completion(text: &str, start: usize, end: usize) -> Vec<Value> {
    let written = &text[start + 1..end];
    tauto::fmt::ESCAPES
        .iter()
        .filter(|(name, _)| name.starts_with(written))
        .map(|(name, sign)| {
            json!({
                "label": format!("\\{name}"),
                "kind": 21,
                "detail": sign,
                "filterText": format!("\\{name}"),
                "textEdit": {"range": range(text, start, end), "newText": sign},
            })
        })
        .collect()
}

fn range(text: &str, start: usize, end: usize) -> Value {
    let (sl, sc) = position_of(text, start);
    let (el, ec) = position_of(text, end);
    json!({"start": {"line": sl, "character": sc}, "end": {"line": el, "character": ec}})
}

/// What a request about a name needs: the open files, the types of a file
/// once loaded, and where the workspace is.
struct Names<'a> {
    texts: &'a HashMap<String, String>,
    types: &'a mut HashMap<String, Rc<Option<TypeInfo>>>,
    root: Option<&'a Path>,
}

/// The `file://` URI of `path`: every byte other than an unreserved character
/// or `/` is written as `%XX`, so that [`path_of`] gives `path` back.
fn uri_of(path: &Path) -> String {
    let mut out = String::from("file://");
    for b in path.to_string_lossy().bytes() {
        if b.is_ascii_alphanumeric() || b"-._~/".contains(&b) {
            out.push(b as char);
        } else {
            out.push_str(&format!("%{b:02X}"));
        }
    }
    out
}

impl Names<'_> {
    fn request(&mut self, method: &str, uri: &str, params: &Value) -> Result<Value, String> {
        let text = self
            .texts
            .get(uri)
            .ok_or_else(|| say!("lsp-file-not-open"))?
            .clone();
        let path = path_of(uri);
        let line = params["position"]["line"].as_u64().unwrap_or(0) as usize;
        let col = params["position"]["character"].as_u64().unwrap_or(0) as usize;
        let offset = offset_of(&text, line, col);

        // The open files stand for what is on disk.
        let open: HashMap<PathBuf, &String> = self
            .texts
            .iter()
            .map(|(u, t)| {
                let p = path_of(u);
                (p.canonicalize().unwrap_or(p), t)
            })
            .collect();
        let read = |p: &Path| -> Option<String> {
            match open.get(&p.canonicalize().unwrap_or_else(|_| p.to_path_buf())) {
                Some(t) => Some((*t).clone()),
                None => std::fs::read_to_string(p).ok(),
            }
        };
        let mut nav =
            Navigator::open(&path, &read).ok_or_else(|| say!("lsp-file-does-not-load"))?;
        let own = path.canonicalize().unwrap_or_else(|_| path.clone());
        let workspace = || {
            let dir = path.parent().unwrap_or(Path::new("."));
            tauto_analyzer::navigate::workspace_files(self.root.unwrap_or(dir))
        };
        let range = |nav: &Navigator, p: &Place| -> Value {
            let t = nav.text(&p.path).unwrap_or("");
            let (l0, c0) = position_of(t, p.span.start as usize);
            let (l1, c1) = position_of(t, p.span.end as usize);
            json!({"start": {"line": l0, "character": c0}, "end": {"line": l1, "character": c1}})
        };
        let location = |nav: &Navigator, p: &Place| -> Value {
            let target = if p.path.canonicalize().unwrap_or_else(|_| p.path.clone()) == own {
                uri.to_string()
            } else {
                uri_of(&p.path)
            };
            json!({"uri": target, "range": range(nav, p)})
        };
        // The types are made once for a text and kept until a file changes.
        let mut typed = || -> Rc<Option<TypeInfo>> {
            self.types
                .entry(uri.to_string())
                .or_insert_with(|| {
                    Rc::new(TypeInfo::build_with_source(&path, &|p| {
                        open.get(p).map(|t| Ok((*t).clone()))
                    }))
                })
                .clone()
        };

        match method {
            "textDocument/hover" => {
                let types = typed();
                Ok(match nav.hover(offset, types.as_ref().as_ref()) {
                    Some(h) => {
                        let p = Place {
                            path: own.clone(),
                            span: h.span,
                        };
                        json!({"contents": {"kind": "markdown", "value": h.contents},
                               "range": range(&nav, &p)})
                    }
                    None => Value::Null,
                })
            }
            "textDocument/definition" => {
                let mut place = nav.definition(offset, None);
                if place.is_none() {
                    let types = typed();
                    place = nav.definition(offset, types.as_ref().as_ref());
                }
                Ok(place.map_or(Value::Null, |p| location(&nav, &p)))
            }
            "textDocument/references" => {
                let with = params["context"]["includeDeclaration"]
                    .as_bool()
                    .unwrap_or(true);
                let ws = workspace();
                let places = nav.references(offset, with, &ws);
                Ok(json!(
                    places.iter().map(|p| location(&nav, p)).collect::<Vec<_>>()
                ))
            }
            "textDocument/prepareRename" => {
                let (span, name) = nav.prepare_rename(offset)?;
                let p = Place {
                    path: own.clone(),
                    span,
                };
                Ok(json!({"range": range(&nav, &p), "placeholder": name}))
            }
            _ => {
                let new_name = params["newName"]
                    .as_str()
                    .ok_or_else(|| say!("lsp-no-new-name"))?;
                let ws = workspace();
                let edits = nav.rename(offset, new_name, &ws)?;
                let mut changes: HashMap<String, Vec<Value>> = HashMap::new();
                for e in &edits {
                    let place = Place {
                        path: e.path.clone(),
                        span: e.span,
                    };
                    let target = location(&nav, &place);
                    changes
                        .entry(target["uri"].as_str().unwrap_or("").to_string())
                        .or_default()
                        .push(json!({"range": target["range"], "newText": e.text}));
                }
                Ok(json!({"changes": changes}))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{escape_completion, escape_on_type, escape_start, path_of, uri_of};
    use serde_json::json;
    use std::path::PathBuf;

    #[test]
    fn an_escape_becomes_its_sign_when_a_space_follows() {
        let text = "fn f(): Prop { \\forall x";
        let edit = escape_on_type(text, 0, 23, " ").unwrap();
        assert_eq!(edit["newText"], "∀");
        assert_eq!(
            edit["range"],
            json!({"start": {"line": 0, "character": 15}, "end": {"line": 0, "character": 22}})
        );
    }

    #[test]
    fn an_escape_after_a_sign_counts_utf16_units() {
        let text = "∀ x, \\exists(";
        let edit = escape_on_type(text, 0, 13, "(").unwrap();
        assert_eq!(edit["newText"], "∃");
        assert_eq!(edit["range"]["start"]["character"], 5);
    }

    #[test]
    fn no_edit_for_an_unknown_name_a_comment_or_a_text() {
        assert!(escape_on_type("\\foo ", 0, 5, " ").is_none());
        assert!(escape_on_type("// \\forall ", 0, 11, " ").is_none());
        assert!(escape_on_type("\"\\forall ", 0, 9, " ").is_none());
        assert!(escape_on_type("\\forallx", 0, 9, "x").is_none());
        assert!(escape_on_type("x ", 0, 2, " ").is_none());
    }

    #[test]
    fn escapes_complete_from_their_backslash() {
        let text = "a \\l";
        assert_eq!(escape_start(text, text.len()), Some(2));
        let labels: Vec<_> = escape_completion(text, 2, text.len())
            .iter()
            .map(|i| i["label"].as_str().unwrap().to_string())
            .collect();
        assert_eq!(labels, ["\\land", "\\lor", "\\llbracket"]);
        assert_eq!(escape_completion(text, 2, text.len())[0]["textEdit"]["newText"], "∧");
    }

    #[test]
    fn a_file_uri_is_percent_decoded() {
        assert_eq!(
            path_of("file:///a%20b/c.taut"),
            PathBuf::from("/a b/c.taut")
        );
        assert_eq!(
            path_of("file:///%E8%A8%BC%E6%98%8E.taut"),
            PathBuf::from("/証明.taut")
        );
        assert_eq!(path_of("file:///a%2/b%zz"), PathBuf::from("/a%2/b%zz"));
        assert_eq!(path_of("file:///%FF"), PathBuf::from("/%FF"));
    }

    #[test]
    fn a_path_round_trips_through_its_uri() {
        for p in [
            "/a b/c.taut",
            "/50%/x.taut",
            "/証明/a#b?.taut",
            "/plain/a-b_c.taut",
        ] {
            let path = PathBuf::from(p);
            let uri = uri_of(&path);
            assert!(!uri[7..].contains([' ', '#', '?']), "{uri}");
            assert_eq!(path_of(&uri), path);
        }
    }
}
