//! The files a program was read from, and where a span of it is in them.

use std::path::{Path, PathBuf};

use crate::macros::SpanMap;

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: PathBuf,
    pub base: u32,
    pub text: String,
}

#[derive(Debug, Clone, Default)]
pub struct SourceMap {
    pub files: Vec<SourceFile>,
    pub spans: SpanMap,
}

impl SourceMap {
    /// A span's position as its source file, line and column, counted from 1.
    /// Macro-generated spans are followed to the source that produced them.
    pub fn locate(&self, offset: u32) -> Option<(&Path, usize, usize)> {
        locate(&self.files, &self.spans, offset)
    }
}

/// As [`SourceMap::locate`], of files and spans held apart.
pub fn locate<'a>(
    files: &'a [SourceFile],
    spans: &SpanMap,
    mut offset: u32,
) -> Option<(&'a Path, usize, usize)> {
    while let Some((written, _)) = spans.origin(offset) {
        offset = written;
    }
    let file = files.iter().rev().find(|f| f.base <= offset)?;
    // An offset past the end of its file, or inside a character, still names
    // that file: the place is read at the nearest character start before it,
    // never at a byte that would split a character.
    let at = file.text.floor_char_boundary((offset - file.base) as usize);
    let before = &file.text[..at];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    Some((&file.path, line, col))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn two_files() -> Vec<SourceFile> {
        vec![
            SourceFile {
                path: "main.taut".into(),
                base: 0,
                text: "fn main() {}\n".into(),
            },
            SourceFile {
                path: "proof.taut".into(),
                base: 100,
                text: "-- a ⊢ b\nfn f() {}\n".into(),
            },
        ]
    }

    #[test]
    fn a_span_is_placed_in_its_own_file() {
        let files = two_files();
        let at = 100 + "-- a ⊢ b\n".len() as u32 + 3;
        let (path, line, col) = locate(&files, &SpanMap::default(), at).unwrap();
        assert_eq!((path, line, col), (Path::new("proof.taut"), 2, 4));
    }

    #[test]
    fn an_offset_inside_a_character_does_not_panic() {
        let files = two_files();
        // One byte into the three bytes of '⊢'.
        let at = 100 + "-- a ".len() as u32 + 1;
        let (path, line, col) = locate(&files, &SpanMap::default(), at).unwrap();
        assert_eq!((path, line, col), (Path::new("proof.taut"), 1, 6));
    }

    #[test]
    fn an_offset_past_its_file_is_placed_at_its_end() {
        let files = two_files();
        let (path, line, _) = locate(&files, &SpanMap::default(), 50).unwrap();
        assert_eq!((path, line), (Path::new("main.taut"), 2));
    }
}
