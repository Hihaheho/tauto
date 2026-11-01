//! The build cache: keys, publishing and explaining.

use std::collections::BTreeMap;
use std::path::PathBuf;

use tauto_cache::{Action, BlobDigest, BuildCache, Explain, Outputs};

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "tauto-cache-{name}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn verify(proof: &[u8]) -> Action {
    Action::new("verify", "text")
        .input("source", proof)
        .input("kernel", b"k1")
}

#[test]
fn the_key_does_not_depend_on_the_order_of_inputs() {
    let a = Action::new("verify", "x").input("a", b"1").input("b", b"2");
    let b = Action::new("verify", "y").input("b", b"2").input("a", b"1");
    assert_eq!(a.key(), b.key());
    assert_ne!(
        a.key(),
        Action::new("codegen", "x")
            .input("a", b"1")
            .input("b", b"2")
            .key()
    );
    // A name and a value cannot run into each other.
    assert_ne!(
        Action::new("k", "").input("ab", b"c").key(),
        Action::new("k", "").input("a", b"bc").key()
    );
}

#[test]
fn an_action_is_found_and_explained() {
    tauto_messages::install();
    let root = scratch("explain");
    let cache = BuildCache::at(root.clone());
    assert_eq!(cache.explain(&verify(b"p1")), Explain::New);

    let d = cache.put_blob(b"checked").unwrap();
    assert_eq!(d, cache.put_blob(b"checked").unwrap());
    let outputs = Outputs(BTreeMap::from([("env".to_string(), d.clone())]));
    let key = cache.put(&verify(b"p1"), &outputs).unwrap();
    assert_eq!(cache.get(&verify(b"p1")), Some(outputs));
    assert_eq!(cache.explain(&verify(b"p1")), Explain::Hit(key));

    let other = Action::new("verify", "text")
        .input("source", b"p2")
        .input("axioms", b"none");
    assert_eq!(
        cache.explain(&other),
        Explain::Changed {
            changed: vec!["source".into()],
            added: vec!["axioms".into()],
            removed: vec!["kernel".into()],
        }
    );

    // A blob that is gone or changed is not used.
    let path = cache.blob_path(&d);
    let mut p = std::fs::metadata(&path).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    p.set_readonly(false);
    std::fs::set_permissions(&path, p).unwrap();
    std::fs::write(&path, b"other").unwrap();
    assert_eq!(cache.get_blob(&d), None);
    std::fs::remove_file(&path).unwrap();
    assert_eq!(cache.get(&verify(b"p1")), None);
    assert_eq!(cache.explain(&verify(b"p1")), Explain::Lost);
    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn an_action_naming_a_missing_blob_is_not_recorded() {
    tauto_messages::install();
    let root = scratch("missing");
    let cache = BuildCache::at(root.clone());
    let outputs = Outputs(BTreeMap::from([("env".to_string(), BlobDigest::of(b"x"))]));
    assert!(cache.put(&verify(b"p"), &outputs).is_err());
    assert_eq!(cache.explain(&verify(b"p")), Explain::New);
    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn record_names_round_trip_without_separators() {
    let root = scratch("names");
    let cache = BuildCache::at(root.clone());
    let names = [
        "",
        "has spaces",
        "line\nfeed",
        "return\r",
        "日本語",
        "nul\0byte",
    ];
    let mut action = Action::new("kind\nwith separators\0", "subject");
    let digest = cache.put_blob(b"value").unwrap();
    let mut outputs = Outputs::default();
    for name in names {
        action = action.input(name, name.as_bytes());
        outputs.0.insert(name.to_string(), digest.clone());
    }
    let key = cache.put(&action, &outputs).unwrap();
    assert_eq!(cache.get(&action), Some(outputs));
    assert_eq!(cache.explain(&action), Explain::Hit(key));
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn incomplete_and_wrong_action_records_are_cache_misses() {
    let root = scratch("invalid-record");
    let cache = BuildCache::at(root.clone());
    let action = verify(b"proof");
    let key = cache.put(&action, &Outputs::default()).unwrap();
    let path = root.join("actions-v2").join(key.hex());
    let record = std::fs::read(&path).unwrap();
    for length in 0..record.len() {
        std::fs::remove_file(&path).unwrap();
        std::fs::write(&path, &record[..length]).unwrap();
        assert_eq!(cache.get(&action), None, "truncated at {length}");
    }
    let other = verify(b"different");
    std::fs::write(root.join("actions-v2").join(other.key().hex()), &record).unwrap();
    assert_eq!(cache.get(&other), None);
    let mut trailing = record;
    trailing.push(0);
    std::fs::write(&path, trailing).unwrap();
    assert_eq!(cache.get(&action), None);
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn record_versions_do_not_overwrite_each_other() {
    let root = scratch("versions");
    let cache = BuildCache::at(root.clone());
    let action = verify(b"proof");
    let legacy = root.join("actions").join(action.key().hex());
    std::fs::create_dir_all(legacy.parent().unwrap()).unwrap();
    std::fs::write(&legacy, b"legacy record").unwrap();
    assert_eq!(cache.get(&action), None);
    let outputs = Outputs::default();
    cache.put(&action, &outputs).unwrap();
    assert_eq!(cache.get(&action), Some(outputs));
    assert_eq!(std::fs::read(legacy).unwrap(), b"legacy record");
    std::fs::remove_dir_all(root).unwrap();
}
