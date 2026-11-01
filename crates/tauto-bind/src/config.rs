//! A crate's binding configuration, read from the text of
//! `bind/<crate>.config.eure`.

use std::collections::BTreeMap;

use eure_document::document::node::NodeValue;
use eure_document::document::{EureDocument, NodeId};
use eure_document::value::PrimitiveValue as P;
use tauto_message::msg;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Config {
    pub crate_name: String,
    /// The public items to bind, as Rust paths.
    pub items: Vec<String>,
    /// A generic function's instances: the type arguments, as written.
    pub instances: BTreeMap<String, Vec<String>>,
    /// The traits whose implementations are bound.
    pub traits: Vec<String>,
    /// A Rust path → the name it gets in tauto.
    pub rename: BTreeMap<String, String>,
}

impl Config {
    pub fn parse(text: &str, file: &str) -> Result<Config, String> {
        let doc = eure_reader::parse_to_document(text, file).map_err(|e| format!("{file}: {e}"))?;
        let fail = |m: String| format!("{file}: {m}");
        let mut out = Config::default();
        for (key, id) in map(&doc, doc.get_root_id()).map_err(fail)? {
            match key.as_str() {
                "crate" => out.crate_name = text_of(&doc, id).map_err(fail)?,
                "items" => out.items = list_of(&doc, id).map_err(fail)?,
                "traits" => out.traits = list_of(&doc, id).map_err(fail)?,
                "instances" => {
                    for (k, v) in map(&doc, id).map_err(fail)? {
                        out.instances.insert(k, list_of(&doc, v).map_err(fail)?);
                    }
                }
                "rename" => {
                    for (k, v) in map(&doc, id).map_err(fail)? {
                        out.rename.insert(k, text_of(&doc, v).map_err(fail)?);
                    }
                }
                other => return Err(fail(msg!("bind-unknown-key", key = other).to_string())),
            }
        }
        if out.crate_name.is_empty() {
            return Err(fail(msg!("bind-crate-missing").to_string()));
        }
        Ok(out)
    }
}

fn map(doc: &EureDocument, id: NodeId) -> Result<Vec<(String, NodeId)>, String> {
    match &doc.node(id).content {
        NodeValue::Map(m) => Ok(m
            .iter()
            .map(|(k, v)| (k.to_string().trim_matches('"').to_string(), *v))
            .collect()),
        NodeValue::Hole(_) => Ok(Vec::new()),
        _ => Err(msg!("bind-expected-block").to_string()),
    }
}

fn text_of(doc: &EureDocument, id: NodeId) -> Result<String, String> {
    match &doc.node(id).content {
        NodeValue::Primitive(P::Text(t)) => Ok(t.as_str().to_string()),
        _ => Err(msg!("bind-expected-text").to_string()),
    }
}

fn list_of(doc: &EureDocument, id: NodeId) -> Result<Vec<String>, String> {
    let NodeValue::Array(items) = &doc.node(id).content else {
        return Err(msg!("bind-expected-texts").to_string());
    };
    items.iter().map(|i| text_of(doc, *i)).collect()
}
