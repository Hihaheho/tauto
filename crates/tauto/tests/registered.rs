//! The functions a `syntax` registers with `with fmt f, tokens g`: the layout of a literal's
//! text, and what an editor colours it as. The syntaxes are in `syntax_fixtures/registered`.

use std::path::{Path, PathBuf};

use tauto::fmt_literals::format_literals;
use tauto::registered::{Highlight, Library};
use tauto::syntax::Role;

fn dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/syntax_fixtures/registered")
}

fn read(name: &str) -> String {
    std::fs::read_to_string(dir().join(name)).expect("the fixture is there")
}

#[test]
fn a_literal_is_laid_out_by_the_function_of_its_syntax() {
    tauto_messages::install();
    let (out, warnings) = format_literals(&dir().join("main.taut"), &read("main.taut")).unwrap();
    assert_eq!(out, read("main.formatted.taut"));
    assert_eq!(warnings, Vec::<String>::new());
}

#[test]
fn laying_out_a_laid_out_file_changes_nothing() {
    tauto_messages::install();
    let formatted = read("main.formatted.taut");
    let (out, warnings) = format_literals(&dir().join("main.formatted.taut"), &formatted).unwrap();
    assert_eq!(out, formatted);
    assert_eq!(warnings, Vec::<String>::new());
}

/// A directory with the fixtures' tables and library, and `main.taut` holding `text`.
fn scratch(name: &str, text: &str) -> PathBuf {
    static COUNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let scratch = std::env::temp_dir().join(format!(
        "tauto-registered-{name}-{n}-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&scratch);
    std::fs::create_dir_all(&scratch).unwrap();
    let tables = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/syntax_fixtures/.tauto-syntax");
    std::os::unix::fs::symlink(tables, scratch.join(".tauto-syntax")).unwrap();
    std::fs::write(scratch.join("lib.taut"), read("lib.taut")).unwrap();
    let main = scratch.join("main.taut");
    std::fs::write(&main, text).unwrap();
    main
}

#[test]
fn a_syntax_without_a_fmt_function_keeps_its_literals() {
    tauto_messages::install();
    let source = r#"import "lib.taut"
import std::prelude::Macro

fn other(): outline_Doc {
  outline`a ,  1`
}
"#;
    let main = scratch("keeps", source);
    let (out, warnings) = format_literals(&main, source).unwrap();
    assert_eq!(out, source);
    assert_eq!(warnings, Vec::<String>::new());
}

fn with_library<T>(f: impl FnOnce(&Library, &tauto::program::Loaded) -> T) -> T {
    let path = dir().join("main.taut");
    let loaded = tauto::syntax::with_search_dirs(vec![dir()], || {
        tauto::program::load_with_text(&path, None)
    })
    .unwrap();
    assert_eq!(loaded.program.errors, Vec::new());
    let library = Library::open(&loaded.program, &loaded.registrations).unwrap();
    f(&library, &loaded)
}

fn tables_of(loaded: &tauto::program::Loaded, syntax: &str) -> std::rc::Rc<tauto_syntax::Tables> {
    loaded
        .literals
        .iter()
        .find(|u| u.syntax == syntax)
        .map(|u| u.tables.clone())
        .expect("a literal of the syntax")
}

fn mark(start: u32, end: u32, kind: &'static str) -> Highlight {
    Highlight { start, end, kind }
}

#[test]
fn a_tokens_function_that_reads_the_tokens_colours_the_text() {
    tauto_messages::install();
    with_library(|library, loaded| {
        let tables = tables_of(loaded, "layout");
        assert!(library.has("layout", Role::Tokens));
        let marks = library
            .highlight("layout", &tables, "ab, 12")
            .unwrap()
            .unwrap();
        assert_eq!(marks, [mark(0, 2, "function"), mark(4, 6, "number")]);
        // Text that is not finished still has its tokens.
        let marks = library
            .highlight("layout", &tables, "ab, ")
            .unwrap()
            .unwrap();
        assert_eq!(marks, [mark(0, 2, "function")]);
    });
}

#[test]
fn a_tokens_function_that_reads_the_tree_colours_by_node() {
    tauto_messages::install();
    with_library(|library, loaded| {
        let tables = tables_of(loaded, "outline");
        assert!(!library.has("outline", Role::Fmt));
        let marks = library
            .highlight("outline", &tables, "ab, 12")
            .unwrap()
            .unwrap();
        assert_eq!(marks, [mark(0, 2, "type"), mark(4, 6, "number")]);
        // A tree needs the text to be of the syntax.
        assert!(library.highlight("outline", &tables, "ab, ,").is_err());
    });
}

fn load_text(text: &str) -> Result<tauto::program::Loaded, String> {
    let main = scratch("wrong", text);
    tauto::syntax::with_search_dirs(vec![main.parent().unwrap().to_path_buf()], || {
        tauto::program::load_with_text(&main, Some(text))
    })
}

fn errors_of(text: &str) -> Vec<String> {
    load_text(text)
        .unwrap()
        .program
        .errors
        .into_iter()
        .map(|(m, _)| m)
        .collect()
}

#[test]
fn a_registered_function_must_exist_and_have_the_type_of_its_role() {
    tauto_messages::install();
    let [missing] = &errors_of(
        r#"import "lib.taut"
import std::prelude::Macro
syntax!(layout2, ```par
%start Doc
%title "layout"
%line_comment '//'
%%
Doc: Item { Comma Item };
Item: Num | Word;
Num: /[0-9]+/;
Word: /[a-z]+/;
Comma: ',';
```, with(fmt: nothing)) => struct Doc, struct Doc_Rep1, enum Item,
  fn parse
"#,
    )[..] else {
        panic!("one error")
    };
    assert!(
        missing.contains("`nothing`, the fmt function, is not defined"),
        "{missing}"
    );
    let [arity] = &errors_of(
        r#"import "lib.taut"
import std::prelude::Macro
syntax!(layout2, ```par
%start Doc
%title "layout"
%line_comment '//'
%%
Doc: Item { Comma Item };
Item: Num | Word;
Num: /[0-9]+/;
Word: /[a-z]+/;
Comma: ',';
```, with(fmt: layout_tokens)) => struct Doc, struct Doc_Rep1, enum Item,
  fn parse
"#,
    )[..] else {
        panic!("one error")
    };
    assert!(arity.contains("takes 1 arguments"), "{arity}");
    let [reads] = &errors_of(
        r#"import "lib.taut"
import std::prelude::Macro
syntax!(layout2, ```par
%start Doc
%title "layout"
%line_comment '//'
%%
Doc: Item { Comma Item };
Item: Num | Word;
Num: /[0-9]+/;
Word: /[a-z]+/;
Comma: ',';
```, with(tokens: layout_white)) => struct Doc, struct Doc_Rep1, enum Item,
  fn parse
"#,
    )[..] else {
        panic!("one error")
    };
    assert!(reads.contains("reads SynTok"), "{reads}");
    let [role] = &errors_of(
        r#"import "lib.taut"
import std::prelude::Macro
syntax!(layout2, ```par
%start Doc
%title "layout"
%line_comment '//'
%%
Doc: Item { Comma Item };
Item: Num | Word;
Num: /[0-9]+/;
Word: /[a-z]+/;
Comma: ',';
```, with(format: layout_fmt)) => struct Doc, struct Doc_Rep1, enum Item,
  fn parse
"#,
    )[..] else {
        panic!("one error")
    };
    assert!(
        role.contains("registers `fmt` and `tokens`, not `format`"),
        "{role}"
    );
    let [twice] = &errors_of(
        r#"import "lib.taut"
import std::prelude::Macro
syntax!(layout2, ```par
%start Doc
%title "layout"
%line_comment '//'
%%
Doc: Item { Comma Item };
Item: Num | Word;
Num: /[0-9]+/;
Word: /[a-z]+/;
Comma: ',';
```, with(fmt: layout_fmt, fmt: layout_fmt)) => struct Doc, struct Doc_Rep1,
  enum Item, fn parse
"#,
    )[..] else {
        panic!("one error")
    };
    assert!(twice.contains("`fmt` is registered twice"), "{twice}");
}

#[test]
fn a_registered_function_performs_no_effect_but_div() {
    tauto_messages::install();
    let errors = errors_of(
        r#"import "lib.taut"
import std::prelude::Macro
effect log(m: Text): Unit
fn noisy(ts: List(SynTok)): List(SynHighlight) ! {log} {
  perform log("x")
  Nil
}
syntax!(layout2, ```par
%start Doc
%title "layout"
%line_comment '//'
%%
Doc: Item { Comma Item };
Item: Num | Word;
Num: /[0-9]+/;
Word: /[a-z]+/;
Comma: ',';
```, with(tokens: noisy)) => struct Doc, struct Doc_Rep1, enum Item,
  fn parse
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("may perform Div only")),
        "{errors:?}"
    );
}

#[test]
fn a_function_that_changes_more_than_white_space_leaves_the_literal() {
    tauto_messages::install();
    let all = r#"import "lib.taut"
import std::prelude::Macro
fn dropping(ts: List(SynTok), width: u64): Option(Text) { Some("a") }
syntax!(layout2, ```par
%start Doc
%title "layout"
%line_comment '//'
%%
Doc: Item { Comma Item };
Item: Num | Word;
Num: /[0-9]+/;
Word: /[a-z]+/;
Comma: ',';
```, with(fmt: dropping)) => struct Doc, struct Doc_Rep1, enum Item,
  fn parse

fn use_it(): layout2.Doc {
  layout2`a, b`
}
"#;
    let main = scratch("changes", all);
    let (out, warnings) = format_literals(&main, all).unwrap();
    assert_eq!(out, all);
    assert_eq!(warnings.len(), 1, "{warnings:?}");
    assert!(
        warnings[0].contains("changes more than white space"),
        "{warnings:?}"
    );
}
