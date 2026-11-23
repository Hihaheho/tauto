//! Inputs and expectations that tests share with the case files under `cases/`.
//!
//! A test that needs the source of a case reads it from the case file when it
//! runs, so the case file stays the only place the source is written.

use eure_document::document::node::NodeValue;
use eure_document::document::{EureDocument, NodeId};
use eure_document::value::{ObjectKey, PrimitiveValue};
use std::path::PathBuf;

/// The text at `path` in the case file `file` (relative to `cases/`).
///
/// Panics with the file and the path when either is missing: a test that asks
/// for an input the case file does not hold has nothing to check.
pub fn text(file: &str, path: &[&str]) -> String {
    let document = document(file);
    let node = path_in(&document, path)
        .unwrap_or_else(|| panic!("case file {file} has no {}", path.join(".")));
    text_of(file, &document, node, path)
}

fn document(file: &str) -> EureDocument {
    let location = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../cases")
        .join(file);
    let content = std::fs::read_to_string(&location)
        .unwrap_or_else(|e| panic!("cannot read case file {}: {e}", location.display()));
    eure_reader::parse_to_document(&content, &location)
        .unwrap_or_else(|e| panic!("cannot parse case file {file}: {e}"))
}

fn path_in(doc: &EureDocument, path: &[&str]) -> Option<NodeId> {
    let mut node = doc.get_root_id();
    for key in path {
        node = child(doc, node, key)?;
    }
    Some(node)
}

fn text_of(file: &str, doc: &EureDocument, node: NodeId, path: &[&str]) -> String {
    match doc.node(node).as_primitive() {
        Some(PrimitiveValue::Text(t)) => t.as_str().to_string(),
        _ => panic!("case file {file}: {} is not text", path.join(".")),
    }
}

fn child(doc: &EureDocument, node: NodeId, key: &str) -> Option<NodeId> {
    let NodeValue::Map(map) = &doc.node(node).content else {
        return None;
    };
    map.get_node_id(&ObjectKey::String(key.to_string()))
}

/// The `source` of the case or fixture `name`.
///
/// A fixture (`@ fixtures.<name>`) is an input that a Rust test reads and that
/// no case runs.
pub fn source(file: &str, name: &str) -> String {
    let document = document(file);
    for section in ["cases", "fixtures"] {
        if let Some(node) = path_in(&document, &[section, name, "source"]) {
            return text_of(file, &document, node, &[section, name, "source"]);
        }
    }
    panic!("case file {file} has no case or fixture {name}")
}

/// The file `input` of case `name`.
pub fn file(file: &str, name: &str, input: &str) -> String {
    text(file, &["cases", name, "files", input])
}

/// The expectation `key` of case `name`.
pub fn expected(file: &str, name: &str, key: &str) -> String {
    text(file, &["cases", name, key])
}
