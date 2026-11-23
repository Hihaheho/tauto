use std::path::PathBuf;

fn current() -> Vec<PathBuf> {
    let current = tauto_parse::syntax::set_search_dirs(Vec::new());
    tauto_parse::syntax::set_search_dirs(current.clone());
    current
}

#[test]
fn search_directories_restore_after_nesting_and_unwind() {
    let prior = tauto_parse::syntax::set_search_dirs(vec![PathBuf::from("outer")]);
    let outer = vec![PathBuf::from("outer")];
    let inner = vec![PathBuf::from("inner")];

    tauto_parse::syntax::with_search_dirs(inner.clone(), || {
        assert_eq!(current(), inner);
        tauto_parse::syntax::with_search_dirs(vec![PathBuf::from("nested")], || {
            assert_eq!(current(), vec![PathBuf::from("nested")]);
        });
        assert_eq!(current(), inner);
    });
    assert_eq!(current(), outer);

    let unwind = std::panic::catch_unwind(|| {
        tauto_parse::syntax::with_search_dirs(inner.clone(), || panic!("test unwind"));
    });
    assert!(unwind.is_err());
    assert_eq!(current(), outer);

    tauto_parse::syntax::set_search_dirs(prior);
}
