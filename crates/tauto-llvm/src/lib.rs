//! Writes a checked program as LLVM IR, which LLVM compiles to machine
//! code (`docs/design/llvm-backend.md`).
//!
//! The input is a package with no type parameter left (`mono::specialize`),
//! in A-normal form (`anf::normalize`), with its drops written
//! (`ownership::insert`). The order of evaluation, where each value is
//! dropped and what each `match` tests are read from it; nothing here
//! decides them. `emit` gives the text of one module, or says what in the
//! program it does not write yet (`Refused`): it never writes a program in
//! part.

use std::collections::HashMap;
use std::fmt::Write;

use tauto_nir::*;

mod build;
mod func;
mod glue;
mod layout;
mod rt;

pub use rt::Sys;

/// What in a program the backend does not write yet.
#[derive(Debug, Clone, PartialEq)]
pub struct Refused(pub String);

impl std::fmt::Display for Refused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "the LLVM backend does not write {} yet", self.0)
    }
}

pub(crate) type R<T> = Result<T, Refused>;

pub(crate) fn refuse<T>(what: impl Into<String>) -> R<T> {
    Err(Refused(what.into()))
}

/// What a type's glue does to a value at an address.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Glue {
    /// Releases what the value holds.
    Drop,
    /// Makes the words copied from another value a value of its own.
    Dup,
    /// Adds the text `show` gives the value to a text being built.
    Show,
}

pub(crate) struct Module<'p> {
    pub pkg: &'p Package,
    /// The glue asked for, each once, in the order it was asked for.
    glue: Vec<(Glue, Ty)>,
    glue_ids: HashMap<(Glue, Ty), usize>,
    strings: Vec<String>,
    string_ids: HashMap<String, usize>,
    /// The texts of the literals, each held in a box of its own that the
    /// program never frees (`Module::text_box`).
    boxes: Vec<String>,
    box_ids: HashMap<String, usize>,
    /// The functions of the program's function values, by their numbers:
    /// the words they take and give, and whether they hold an environment
    /// to drop.
    pub closures: Vec<((usize, usize), bool)>,
    /// The text of each closure's function and its environment's drop.
    pub closure_defs: String,
    /// The function value of each function of the program used as one.
    pub wrappers: HashMap<InstId, usize>,
    /// The signatures function values are called at, in the order first
    /// called.
    pub calls: Vec<(usize, usize)>,
}

impl<'p> Module<'p> {
    /// The name of the glue function of a type, written once at the end.
    pub fn glue(&mut self, g: Glue, t: &Ty) -> String {
        let key = (g, t.clone());
        let id = match self.glue_ids.get(&key) {
            Some(id) => *id,
            None => {
                let id = self.glue.len();
                self.glue.push(key.clone());
                self.glue_ids.insert(key, id);
                id
            }
        };
        let kind = match g {
            Glue::Drop => "drop",
            Glue::Dup => "dup",
            Glue::Show => "show",
        };
        format!("@{kind}.{id}")
    }

    /// The name of a constant text ended with a zero byte.
    pub fn string(&mut self, s: &str) -> String {
        let id = match self.string_ids.get(s) {
            Some(id) => *id,
            None => {
                let id = self.strings.len();
                self.strings.push(s.to_string());
                self.string_ids.insert(s.to_string(), id);
                id
            }
        };
        format!("@.s{id}")
    }

    /// The name of the constant box of a literal `Text`: a box laid out as
    /// every `Text` is, whose count is 0. A count of 0 is never changed, so
    /// the box is shared by every read of the literal and never freed.
    pub fn text_box(&mut self, s: &str) -> String {
        let id = match self.box_ids.get(s) {
            Some(id) => *id,
            None => {
                let id = self.boxes.len();
                self.boxes.push(s.to_string());
                self.box_ids.insert(s.to_string(), id);
                id
            }
        };
        format!("@.t{id}")
    }
}

/// The LLVM IR of `pkg`: a module whose `main` runs the program's top
/// level, on system calls (`Sys::Linux`), with no library.
pub fn emit(pkg: &Package) -> Result<String, Refused> {
    emit_on(pkg, Sys::Linux)
}

/// The LLVM IR of `pkg` on the system `sys`. Only the runtime's system layer
/// depends on it.
pub fn emit_on(pkg: &Package, sys: Sys) -> Result<String, Refused> {
    mono::check(pkg).map_err(Refused)?;
    let Some(top) = pkg.top else {
        return refuse("a package without a top level");
    };
    let mut m = Module {
        pkg,
        glue: Vec::new(),
        glue_ids: HashMap::new(),
        strings: Vec::new(),
        string_ids: HashMap::new(),
        boxes: Vec::new(),
        box_ids: HashMap::new(),
        closures: Vec::new(),
        closure_defs: String::new(),
        wrappers: HashMap::new(),
        calls: Vec::new(),
    };
    let mut defs = String::new();
    for f in &pkg.fns {
        defs.push_str(&func::function(&mut m, f)?);
    }
    let mut done = 0;
    while done < m.glue.len() {
        let (g, t) = m.glue[done].clone();
        defs.push_str(&glue::function(&mut m, g, &t)?);
        done += 1;
    }
    defs.push_str(&m.closure_defs);
    defs.push_str(&func::dispatch(&m));
    let mut out = String::new();
    out.push_str("; Written by the Tauto LLVM backend.\n");
    out.push_str(&rt::runtime(sys));
    out.push('\n');
    out.push_str(&rt::escaped());
    out.push('\n');
    for (i, s) in m.strings.iter().enumerate() {
        let _ = writeln!(
            out,
            "@.s{i} = private unnamed_addr constant [{} x i8] c\"{}\\00\"",
            s.len() + 1,
            escape(s)
        );
    }
    for (i, s) in m.boxes.iter().enumerate() {
        let _ = writeln!(
            out,
            "@.t{i} = private unnamed_addr constant [{} x i8] c\"{}{}\\00\", align 8",
            s.len() + 17,
            box_header(s.len()),
            escape(s)
        );
    }
    out.push('\n');
    out.push_str(&defs);
    let call = match func::words_of_result(&m, &pkg.fns[top])? {
        0 => format!("call fastcc void @f{top}()"),
        1 => format!("%r = call fastcc i64 @f{top}()"),
        n => format!("%r = call fastcc [{n} x i64] @f{top}()"),
    };
    let _ = write!(
        out,
        "define i32 @rt_main() {{\nentry:\n  {call}\n  call void @rt_stdout_flush()\n  ret i32 0\n}}\n"
    );
    Ok(out)
}

/// The bytes of a text as LLVM writes a constant.
/// The first two words of a literal's box, as the bytes of the constant:
/// the count 0, then the number of bytes, least significant byte first.
fn box_header(n: usize) -> String {
    let mut out = "\\00".repeat(8);
    for b in (n as u64).to_le_bytes() {
        let _ = write!(out, "\\{b:02X}");
    }
    out
}

fn escape(s: &str) -> String {
    let mut out = String::new();
    for b in s.bytes() {
        if b.is_ascii_graphic() && b != b'"' && b != b'\\' || b == b' ' {
            out.push(b as char);
        } else {
            let _ = write!(out, "\\{b:02X}");
        }
    }
    out
}
