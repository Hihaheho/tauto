//! A proof that reads a file with `include_text!` is checked again when the
//! file changes: the file's text is part of the declaration, and so of the
//! key the proof cache keeps it under.

use tauto::check::{Kernel, Verdict, declare_prelude};

/// The verdict of the theorem `t` of `dir/main.taut`, checked with the
/// proof cache that `TAUTO_CACHE` names.
fn verdict(dir: &std::path::Path) -> Verdict {
    let loaded = tauto::program::load(&dir.join("main.taut")).unwrap();
    assert!(
        loaded.program.errors.is_empty(),
        "{:?}",
        loaded.program.errors
    );
    let mut k = Kernel::new();
    declare_prelude(&mut k).unwrap();
    k.use_cache();
    k.declare_program(&loaded.program)
        .into_iter()
        .find(|e| e.name == "t")
        .unwrap()
        .verdict
}

#[test]
fn a_proof_is_checked_again_when_a_file_it_includes_changes() {
    tauto_messages::install();
    let base = std::env::temp_dir().join(format!("tauto-include-cache-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let (dir, cache) = (base.join("src"), base.join("cache"));
    std::fs::create_dir_all(&dir).unwrap();
    // This test is the only one in its process that reads the variable.
    unsafe { std::env::set_var("TAUTO_CACHE", &cache) };
    std::fs::write(
        dir.join("main.taut"),
        r#"import std::Text
theorem t(): Eq(Text, include_text!("d.txt"), "a") { Refl }
"#,
    )
    .unwrap();
    std::fs::write(dir.join("d.txt"), "a").unwrap();
    let v = verdict(&dir);
    assert!(matches!(v, Verdict::Checked { .. }), "{v:?}");
    assert!(
        std::fs::read_dir(&cache)
            .map(|d| d.count() > 0)
            .unwrap_or(false)
    );
    // The same again, from the cache.
    let v = verdict(&dir);
    assert!(matches!(v, Verdict::Checked { .. }), "{v:?}");
    // The included file changed: the proof is checked again and no longer holds.
    std::fs::write(dir.join("d.txt"), "b").unwrap();
    let v = verdict(&dir);
    assert!(matches!(v, Verdict::Failed(_)), "{v:?}");
    let _ = std::fs::remove_dir_all(&base);
}
