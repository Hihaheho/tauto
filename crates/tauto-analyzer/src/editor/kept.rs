//! What colouring a file made, kept for the thread while it keeps what it reads
//! (`tauto::program::keep_expansions`, an editor's server): the tokens of a file, used again
//! while its text and every input of its program are the same, and the registered functions of
//! the files before it, used again while those files and their inputs are the same
//! (`docs/design/analysis-cache.md`).

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use tauto::program::{Expanded, Inputs};
use tauto::registered::Library;

use super::tokens::Coloured;
use super::{DslNote, DslToken};

/// How many files' tokens, and how many libraries, are kept.
const KEPT: usize = 8;

type Opened = Rc<Result<Library<'static>, String>>;

struct Tokens {
    path: PathBuf,
    text: String,
    inputs: Inputs,
    tokens: Vec<DslToken>,
    notes: Vec<DslNote>,
}

thread_local! {
    static TOKENS: RefCell<Vec<Tokens>> = const { RefCell::new(Vec::new()) };
    static LIBRARIES: RefCell<Vec<(Inputs, Opened)>> = const { RefCell::new(Vec::new()) };
}

fn push<T>(kept: &mut Vec<T>, item: T) {
    if kept.len() >= KEPT {
        kept.remove(0);
    }
    kept.push(item);
}

/// The tokens of the file at `path` with the text `text`: those kept, when what they were made
/// from is the same, else what `make` makes.
pub(super) fn tokens(
    path: &Path,
    text: &str,
    make: impl FnOnce() -> Result<Coloured, String>,
) -> Result<(Vec<DslToken>, Vec<DslNote>), String> {
    if !tauto::program::keeps_expansions() {
        let made = make()?;
        return Ok((made.tokens, made.notes));
    }
    let before = TOKENS.with(|k| {
        k.borrow()
            .iter()
            .find(|t| t.path == path && t.text == text)
            .map(|t| t.inputs.clone())
    });
    if let Some(before) = before
        && tauto::program::current_inputs(path, Some(text), &before).is_ok_and(|now| now == before)
    {
        let found = TOKENS.with(|k| {
            k.borrow()
                .iter()
                .find(|t| t.path == path && t.text == text)
                .map(|t| (t.tokens.clone(), t.notes.clone()))
        });
        if let Some(found) = found {
            return Ok(found);
        }
    }
    let missed = tauto::syntax::tables_missed();
    let made = make()?;
    let result = (made.tokens.clone(), made.notes.clone());
    if tauto::syntax::tables_missed() == missed {
        TOKENS.with(|k| {
            let mut kept = k.borrow_mut();
            kept.retain(|t| t.path != path);
            push(
                &mut kept,
                Tokens {
                    path: path.to_path_buf(),
                    text: text.to_string(),
                    inputs: made.inputs,
                    tokens: made.tokens,
                    notes: made.notes,
                },
            );
        });
    }
    Ok(result)
}

/// The registered functions for the file at `path` (its text given, its program `expanded`):
/// with `own`, those of its own program; else those of the program of the files read before it.
pub(super) fn library(path: &Path, text: &str, expanded: &Expanded, own: bool) -> Opened {
    let dirs = vec![path.parent().unwrap_or(Path::new(".")).to_path_buf()];
    let open = |load: &dyn Fn() -> Result<tauto::program::Loaded, String>| {
        let loaded = tauto::syntax::with_search_dirs(dirs.clone(), load)?;
        Library::open_lenient_owned(loaded.program, &loaded.registrations)
    };
    let n = expanded.files.len().saturating_sub(1);
    if own || n == 0 {
        return Rc::new(open(&|| tauto::program::load_with_text(path, Some(text))));
    }
    let keep = tauto::program::keeps_expansions();
    let inputs = expanded.inputs.first(n);
    if keep
        && let Some(found) = LIBRARIES.with(|k| {
            k.borrow()
                .iter()
                .find(|(i, _)| *i == inputs)
                .map(|(_, l)| l.clone())
        })
    {
        return found;
    }
    let missed = tauto::syntax::tables_missed();
    let opened = Rc::new(open(&|| {
        tauto::program::load_first(path, &expanded.inputs, n)
    }));
    if keep && tauto::syntax::tables_missed() == missed {
        LIBRARIES.with(|k| {
            let mut kept = k.borrow_mut();
            kept.retain(|(i, _)| *i != inputs);
            push(&mut kept, (inputs, opened.clone()));
        });
    }
    opened
}
