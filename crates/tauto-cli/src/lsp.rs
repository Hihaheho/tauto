//! `tauto lsp`: a language server on stdin and stdout. It reports what
//! `tauto check` finds as diagnostics, colours the text of syntax literals
//! with the tokens of their grammar, and completes the terminals the grammar
//! can go on with. On a name it shows the declaration and the type (hover), goes to the
//! declaration, lists the uses and renames (`tauto_analyzer::navigate`).

use std::collections::HashMap;
use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::rc::Rc;

use serde_json::{Value, json};
use tauto_analyzer::editor::{offset_of, position_of};
use tauto_analyzer::navigate::{Navigator, Place, TypeInfo};

pub fn command() -> ExitCode {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    match serve(&mut stdin.lock(), &mut stdout.lock()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{}", crate::i18n::t!("lsp-error", error = e.to_string()));
            ExitCode::FAILURE
        }
    }
}

fn read_message(input: &mut impl BufRead) -> std::io::Result<Option<Value>> {
    let mut length = None;
    loop {
        let mut line = String::new();
        if input.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some(n) = line.strip_prefix("Content-Length:") {
            length = n.trim().parse::<usize>().ok();
        }
    }
    let Some(length) = length else {
        return Ok(None);
    };
    let mut body = vec![0; length];
    input.read_exact(&mut body)?;
    Ok(serde_json::from_slice(&body).ok())
}

fn send(output: &mut impl Write, message: &Value) -> std::io::Result<()> {
    let body = message.to_string();
    write!(output, "Content-Length: {}\r\n\r\n{body}", body.len())?;
    output.flush()
}

/// Serves requests until `exit` or the end of input.
pub fn serve(input: &mut impl BufRead, output: &mut impl Write) -> std::io::Result<()> {
    let mut texts: HashMap<String, String> = HashMap::new();
    // Every open file is a buffer of the workspace, which checks again only
    // what an edit changed.
    let mut workspace = tauto_analyzer::Workspace::new();
    let mut types: HashMap<String, Rc<Option<TypeInfo>>> = HashMap::new();
    let mut root: Option<PathBuf> = None;
    let mut shut_down = false;
    while let Some(message) = read_message(input)? {
        let method = message["method"].as_str().unwrap_or("");
        let params = &message["params"];
        let id = message.get("id").cloned();
        let uri = params["textDocument"]["uri"]
            .as_str()
            .unwrap_or("")
            .to_string();
        let reply = |result: Value| json!({"jsonrpc": "2.0", "id": id, "result": result});
        match method {
            "initialize" => {
                root = params["workspaceFolders"][0]["uri"]
                    .as_str()
                    .or_else(|| params["rootUri"].as_str())
                    .map(path_of);
                send(
                    output,
                    &reply(json!({
                        "capabilities": {
                            "textDocumentSync": 1,
                            "completionProvider": {},
                            "codeActionProvider": {"codeActionKinds": ["quickfix"]},
                            "hoverProvider": true,
                            "definitionProvider": true,
                            "referencesProvider": true,
                            "renameProvider": {"prepareProvider": true},
                            "semanticTokensProvider": {
                                "legend": {"tokenTypes": tauto_analyzer::editor::KINDS, "tokenModifiers": []},
                                "full": true
                            }
                        },
                        "serverInfo": {"name": "tauto"}
                    })),
                )?
            }
            "shutdown" => {
                shut_down = true;
                send(output, &reply(Value::Null))?;
            }
            "exit" => {
                return if shut_down {
                    Ok(())
                } else {
                    Err(std::io::Error::other("exit before shutdown"))
                };
            }
            "textDocument/didOpen" | "textDocument/didChange" => {
                let text = params["textDocument"]["text"]
                    .as_str()
                    .or_else(|| params["contentChanges"][0]["text"].as_str());
                if let Some(text) = text {
                    texts.insert(uri.clone(), text.to_string());
                    workspace.set_text(&path_of(&uri), text.to_string());
                    // Any open file may be one another imports.
                    types.clear();
                    send(
                        output,
                        &json!({"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
                                "params": {"uri": uri, "diagnostics": diagnostics(&workspace, &uri, text)}}),
                    )?;
                }
            }
            "textDocument/didClose" => {
                texts.remove(&uri);
                workspace.refresh(&path_of(&uri));
                types.clear();
                send(
                    output,
                    &json!({"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
                            "params": {"uri": uri, "diagnostics": []}}),
                )?;
            }
            "textDocument/semanticTokens/full" => {
                let data = texts.get(&uri).map_or(Vec::new(), |t| semantic(&uri, t));
                send(output, &reply(json!({"data": data})))?;
            }
            "textDocument/codeAction" => {
                send(output, &reply(json!(code_actions(&uri, params))))?;
            }
            "textDocument/completion" => {
                let items = texts.get(&uri).map_or(Vec::new(), |t| {
                    let line = params["position"]["line"].as_u64().unwrap_or(0) as usize;
                    let col = params["position"]["character"].as_u64().unwrap_or(0) as usize;
                    completion(&uri, t, line, col)
                });
                send(output, &reply(json!(items)))?;
            }
            "textDocument/hover"
            | "textDocument/definition"
            | "textDocument/references"
            | "textDocument/prepareRename"
            | "textDocument/rename" => {
                let mut ctx = Names {
                    texts: &texts,
                    types: &mut types,
                    root: root.as_deref(),
                };
                // A bug in finding a name answers with an error, not the end of the server.
                let answer = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    ctx.request(method, &uri, params)
                }))
                .unwrap_or_else(|_| Err(crate::i18n::t!("lsp-internal-error")));
                match answer {
                    Ok(result) => send(output, &reply(result))?,
                    Err(message) => send(
                        output,
                        &json!({"jsonrpc": "2.0", "id": id,
                                "error": {"code": -32803, "message": message}}),
                    )?,
                }
            }
            _ if id.is_some() => send(
                output,
                &json!({"jsonrpc": "2.0", "id": id,
                        "error": {"code": -32601, "message": format!("unknown method {method}")}}),
            )?,
            _ => {}
        }
    }
    Ok(())
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
            let (message, offset) = match e.rsplit_once(" (byte ") {
                Some((m, n)) => (m, n.trim_end_matches(')').parse().unwrap_or(0)),
                None => (e.as_str(), 0),
            };
            let (line, col) = position_of(text, offset);
            return vec![at(line, col, message)];
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
    let Ok(tokens) = tauto_analyzer::editor::dsl_tokens(&path, text) else {
        return Vec::new();
    };
    let mut data = Vec::new();
    let (mut last_line, mut last_col) = (0, 0);
    for t in tokens {
        let (line, col) = position_of(text, t.start);
        let (end_line, end_col) = position_of(text, t.end);
        // A token over several lines is left uncoloured.
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
    tauto_analyzer::editor::dsl_completion(&path_of(uri), text, offset)
        .unwrap_or_default()
        .into_iter()
        .map(|t| json!({"label": t, "kind": 14}))
        .collect()
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
            .ok_or_else(|| crate::i18n::t!("lsp-file-not-open"))?
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
        let mut nav = Navigator::open(&path, &read)
            .ok_or_else(|| crate::i18n::t!("lsp-file-does-not-load"))?;
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
                .or_insert_with(|| Rc::new(TypeInfo::build(&path, &text)))
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
                    .ok_or_else(|| crate::i18n::t!("lsp-no-new-name"))?;
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
    use super::{path_of, uri_of};
    use std::path::PathBuf;

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
