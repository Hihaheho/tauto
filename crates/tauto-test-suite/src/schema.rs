//! The schema of the case files, generated from the types the runner parses
//! them into, so it cannot drift from what the runner accepts. The committed
//! copy is `crates/tauto-test-suite/case.schema.eure`; an editor that reads
//! Eure schemas can check and complete case files with it.

use eure_document::identifier::Identifier;
use eure_document::path::PathSegment;
use eure_document::plan::{Form, LayoutPlan};
use eure_document::value::ObjectKey;
use eure_schema::SchemaDocument;
use eure_schema::write::{schema_to_document, schema_to_source_document};
use std::path::PathBuf;

pub fn path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("case.schema.eure")
}

pub fn document() -> SchemaDocument {
    SchemaDocument::of::<crate::case::Expectations>()
}

pub fn source() -> Result<String, String> {
    let schema = document();
    let doc = schema_to_document(&schema).map_err(|e| e.to_string())?;
    let mut plan = LayoutPlan::builder(doc);
    let types: Identifier = "types".parse().unwrap();
    plan.set_form_at(&[PathSegment::Extension(types.clone())], Form::BindingBlock)
        .map_err(|e| e.to_string())?;
    for name in schema.types.keys() {
        let at = [
            PathSegment::Extension(types.clone()),
            PathSegment::Value(ObjectKey::String(name.to_string())),
        ];
        plan.set_form_at(&at, Form::BindingBlock)
            .map_err(|e| e.to_string())?;
    }
    let plan = plan.build().map_err(|e| e.to_string())?;
    let source = schema_to_source_document(&schema, plan).map_err(|e| e.to_string())?;
    let mut text = eure_fmt::source::format_source_document(&source);
    if !text.ends_with('\n') {
        text.push('\n');
    }
    Ok(text)
}
