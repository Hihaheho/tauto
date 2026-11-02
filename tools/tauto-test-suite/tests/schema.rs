//! The committed case schema matches the parser's types, and every case file
//! satisfies it. `TAUTO_UPDATE_SCHEMA=1` rewrites the committed schema.
use std::path::{Path, PathBuf};
use tauto_test_suite::schema;

#[test]
fn committed_schema_is_generated() {
    let generated = schema::source().unwrap();
    if std::env::var_os("TAUTO_UPDATE_SCHEMA").is_some() {
        std::fs::write(schema::path(), &generated).unwrap();
        return;
    }
    let committed = std::fs::read_to_string(schema::path()).unwrap_or_default();
    assert!(
        committed == generated,
        "{} is out of date; rerun with TAUTO_UPDATE_SCHEMA=1",
        schema::path().display()
    );
}

fn eure_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            eure_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "eure") {
            out.push(path);
        }
    }
}

#[test]
fn every_case_file_satisfies_the_schema() {
    let schema = schema::document();
    let mut paths = Vec::new();
    eure_files(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases"),
        &mut paths,
    );
    assert!(!paths.is_empty());
    let mut failures = Vec::new();
    for path in paths {
        let text = std::fs::read_to_string(&path).unwrap();
        let doc = eure_reader::parse_to_document(&text, &path).unwrap();
        let out = eure_schema::validate::validate(&doc, &schema);
        if !out.is_valid {
            failures.push(format!("{}: {:?}", path.display(), out.errors));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn the_schema_rejects_a_misspelled_field() {
    for text in [
        "source = \"\"\nchekcs = \"ok\"\n",
        "@ cases.one\nsource = \"\"\nchekcs = \"ok\"\n",
        "@ cases.one\nsource = \"\"\ndiagnostics = [{ message => \"m\", spn => \"x\" }]\n",
    ] {
        let doc = eure_reader::parse_to_document(text, "case").unwrap();
        assert!(
            !eure_schema::validate::validate(&doc, &schema::document()).is_valid,
            "{text}"
        );
    }
}
