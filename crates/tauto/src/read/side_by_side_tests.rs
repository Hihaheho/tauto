//! Files declared side by side declare what they declare in turn, without
//! falling back to declaring every file again in turn.

use super::*;

/// Writes `files` under a directory of its own and loads `main.taut` with
/// the files it imports.
fn load(name: &str, files: &[(&str, &str)]) -> crate::program::Loaded {
    let dir = std::env::temp_dir()
        .join("tauto-side-by-side")
        .join(format!("{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (file, text) in files {
        std::fs::write(dir.join(file), text).unwrap();
    }
    crate::program::load_with_text_in(&dir.join("main.taut"), None).unwrap()
}

/// The entries of every file declared side by side, two at a time; None
/// when the files had to be declared again in turn.
fn side_by_side(loaded: &crate::program::Loaded) -> Option<Vec<Vec<Entry>>> {
    tauto_messages::install();
    let mut kernel = Kernel::new();
    check::declare_prelude(&mut kernel).unwrap();
    let limits = time_limits(loaded).unwrap();
    declare_scheduled(&mut kernel, loaded, &limits, 2)
}

fn entry<'a>(entries: &'a [Vec<Entry>], name: &str) -> &'a Entry {
    entries
        .iter()
        .flatten()
        .find(|e| e.name.to_string().ends_with(name))
        .unwrap_or_else(|| {
            let names: Vec<String> = entries
                .iter()
                .flatten()
                .map(|e| e.name.to_string())
                .collect();
            panic!("no entry {name} among {names:?}")
        })
}

/// Two files that do not import one another each take a `&mut`, so each
/// needs the state family `Mut1`, which no file declares.
#[test]
fn two_files_that_need_the_same_state_family() {
    let file = |f: &str| {
        format!(
            "pub fn {f}(c: &mut Nat): Nat {{\n  *c := c + 1\n  c\n}}\n\
             pub fn {f}_twice(c: &mut Nat): Nat {{\n  {f}(&mut c)\n  {f}(&mut c)\n}}\n"
        )
    };
    let loaded = load(
        "state-family",
        &[
            ("a.taut", &file("bump_a")),
            ("b.taut", &file("bump_b")),
            (
                "main.taut",
                "import \"a.taut\"\nimport \"b.taut\"\npub fn n(): Nat { 0 }\n",
            ),
        ],
    );
    let entries = side_by_side(&loaded).expect("declared side by side");
    for name in ["bump_a", "bump_b", "bump_a_twice", "bump_b_twice"] {
        assert!(
            !entry(&entries, name).failed(),
            "{:?}",
            entry(&entries, name)
        );
    }
}

/// A function the kernel does not take (it calls itself outside a
/// structural match) fails in turn too, and runs as written: the files are
/// not declared again in turn for it, and it fails side by side as well.
#[test]
fn a_file_with_a_function_the_kernel_does_not_take() {
    let loaded = load(
        "calls-itself",
        &[
            (
                "up.taut",
                "pub fn up(i: Nat, n: Nat): List(Nat) {\n  \
                 if i >= n { Nil } else { Cons(i, up(i + 1, n)) }\n}\n",
            ),
            ("other.taut", "pub fn other(): Nat { 1 }\n"),
            (
                "main.taut",
                "import \"up.taut\"\nimport \"other.taut\"\npub fn n(): Nat { other() }\n",
            ),
        ],
    );
    let entries = side_by_side(&loaded).expect("declared side by side");
    assert!(entry(&entries, "up").failed());
    assert!(!entry(&entries, "other").failed());
}

/// A file names `Text` without importing `std::text`: it waits for the
/// files of the standard library, as it is declared after them in turn.
#[test]
fn a_file_waits_for_the_standard_library() {
    let loaded = load(
        "library",
        &[
            (
                "reader.taut",
                "pub struct Reader { text: Text, at: u64 }\n\
                 pub fn reader(t: Text): Reader { Reader { text: t, at: 0 } }\n",
            ),
            (
                "main.taut",
                "import std::text\nimport \"reader.taut\"\npub fn r(): Reader { reader(\"a\") }\n",
            ),
        ],
    );
    let (_, imports) = levels(&loaded).expect("levels");
    let std_root = Path::new(crate::stdlib::ROOT);
    let library: Vec<usize> = (0..loaded.files.len())
        .filter(|&i| loaded.files[i].path.starts_with(std_root))
        .collect();
    assert!(!library.is_empty());
    let reader = loaded
        .files
        .iter()
        .position(|f| f.path.ends_with("reader.taut"))
        .unwrap();
    for l in library {
        assert!(imports[reader].contains(&l), "{:?}", loaded.files[l].path);
    }
    let entries = side_by_side(&loaded).expect("declared side by side");
    for name in ["reader", "r"] {
        assert!(
            !entry(&entries, name).failed(),
            "{:?}",
            entry(&entries, name)
        );
    }
}
