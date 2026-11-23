//! Extraction: the programs of the proof language as Nib. The kernel checks the files first; what it accepted is written out
//! as Nib source with its types and proofs erased:
//!
//! * a family in `Type` becomes a `enum(shared)`, its parameters generics and
//!   its proof fields dropped; a family in `Prop`, a `theorem`, an `axiom`
//!   and a `def` are dropped;
//! * a function keeps its value parameters; a type parameter becomes a
//!   generic, a proof parameter is dropped, and so is the matching argument
//!   of every call;
//! * `match x: T` loses its result type; a match on a proof keeps its one
//!   arm; a match on `Nat` or `Bool` becomes a chain of `if`s.
//!
//! A few declarations of `std/` are not written out but mapped onto Nib's
//! own types and functions (`Nat` onto `nat`, `List` onto `List`, `nat_lt`
//! onto `<`, …). Each has a definition in `std/` that the proofs use. These
//! mappings are additional semantic assumptions of extraction. The kernel
//! checks the source declarations; extraction and the runtime backend are
//! responsible for preserving their behavior in executable code.

mod dependent;
mod runtime;
mod source;

use crate::program::Standard as _;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use tauto_message::{Message, msg};

use crate::check::{Checked, CtorSite, Role, Verdict, record_sugar};
use crate::surface::print::{in_modules_text, raw};
use crate::surface::{FnDecl, InductiveDecl, MatchArm, Name, Pattern, Stmt, SurfaceTerm, TermKind};

/// Which names are the standard library's own declarations. The tables
/// below map a declaration of `std/` (or the prelude) onto Nib by its short
/// name; a declaration of the program's own files with the same name is
/// extracted from its definition, which is what the proofs were about.
pub(crate) struct StdNames {
    /// What the program's own files declare.
    own: HashSet<Name>,
    /// What the files of `std/` declare, as the program reads them.
    std: HashSet<Name>,
    /// What the prelude declares: the library prelude and the kernel's.
    prelude: HashSet<Name>,
    /// How each function declared in the sources takes its parameters:
    /// `Some(false)` is `&`, `Some(true)` is `&mut`.
    borrows: HashMap<Name, Vec<Option<bool>>>,
    /// The parameters that are shared borrows themselves: passing one on
    /// lends nothing again (a `&mut` one is lent as `&`).
    lent_params: HashSet<Name>,
}

impl StdNames {
    /// Whether a call must lend an argument a parameter takes by shared
    /// borrow. A borrow, a closure written in place, or a name that is
    /// already a shared borrow (a function or lambda parameter) is passed
    /// on as it is.
    fn lends_argument(
        &self,
        n: &Name,
        position: usize,
        total: usize,
        arg: &SurfaceTerm,
        lent_locals: &HashSet<Name>,
    ) -> bool {
        match &*arg.kind {
            TermKind::Borrow { .. } | TermKind::Lam { .. } | TermKind::BorrowLam { .. } => {
                return false;
            }
            TermKind::Var(name)
                if self.lent_params.contains(name) || lent_locals.contains(name) =>
            {
                return false;
            }
            _ => {}
        }
        let Some(borrows) = self.borrows.get(n) else {
            return false;
        };
        let Some(k) = position.checked_sub(total.saturating_sub(borrows.len())) else {
            return false;
        };
        borrows.get(k) == Some(&Some(false))
    }

    /// The standard key class has a type-only telescope in Nib. Its
    /// checked laws have no counterpart in the executable class.
    pub(crate) fn native_key_class(&self, n: &Name) -> bool {
        self.of(n) == Some("Key")
    }

    pub(crate) fn new(sources: &[(crate::program::SourceFile, Vec<Stmt>)]) -> Self {
        let mut own = HashSet::new();
        let mut std = HashSet::new();
        let mut borrows = HashMap::new();
        let mut lent_params = HashSet::new();
        fn gather(
            stmts: &[Stmt],
            out: &mut HashMap<Name, Vec<Option<bool>>>,
            params: &mut HashSet<Name>,
        ) {
            for s in stmts {
                match s {
                    Stmt::Fn(f) => {
                        for (p, b) in f.params.iter().zip(&f.borrows) {
                            if *b == Some(false) {
                                params.insert(p.clone());
                            }
                        }
                        if f.borrows.contains(&Some(false)) {
                            out.insert(f.name.clone(), f.borrows.clone());
                        }
                    }
                    Stmt::Mutual { items, .. } => gather(items, out, params),
                    _ => {}
                }
            }
        }
        for (file, stmts) in sources {
            gather(stmts, &mut borrows, &mut lent_params);
            // A file read by its path that is a copy of a file of `std/`, word
            // for word, declares what that file declares.
            let of_std = file.is_standard();
            let set = if of_std { &mut std } else { &mut own };
            set.extend(
                tauto_surface::bindings::declared_names(stmts)
                    .into_iter()
                    .cloned(),
            );
        }
        let prelude = crate::bindings::library_bindings()
            .bindings()
            .map(|(_, reference)| Name::Global(reference.clone()))
            .collect();
        StdNames {
            own,
            std,
            prelude,
            borrows,
            lent_params,
        }
    }

    fn in_std(&self, n: &Name) -> bool {
        !self.own.contains(n) && self.std.contains(n)
    }

    /// Whether a call of `n`, as the checker resolved it, is written by the
    /// mapping of the `std/` function it names. The name decides, not the
    /// spelling: the prelude's `Text::len`, a builtin of Nib, is never
    /// written by a mapping.
    fn written_by_mapping(&self, n: &Name) -> bool {
        self.in_std(n) && mapped_fn(crate::surface::qualify::short(n)).is_some()
    }

    /// The declaration of `std/` the program reads whose short name is
    /// `spelling`, when exactly one has it and it is written out as a function
    /// of its own (not by a mapping, as `Text::slice` is).
    fn declared(&self, spelling: &str) -> Option<Name> {
        use crate::surface::qualify::short;
        if mapped_fn(spelling).is_some() || nib_prelude_fn(spelling) {
            return None;
        }
        let mut found = self
            .std
            .iter()
            .filter(|n| !self.own.contains(n) && short(n) == spelling);
        let first = found.next()?;
        found.next().is_none().then(|| first.clone())
    }

    /// The short name of `n` when `n` names a declaration of the standard
    /// library: one of `std/`, or the prelude's when no file of the program
    /// declares it.
    fn of<'n>(&self, n: &'n Name) -> Option<&'n str> {
        use crate::surface::qualify::short;
        if self.own.contains(n) {
            return None;
        }
        for spelling in [
            "Star", "Zero", "Succ", "true", "false", "Nil", "Cons", "None", "Some", "Less",
            "Equal", "Greater",
        ] {
            if crate::bindings::is_library(n, spelling) {
                return Some(spelling);
            }
        }
        if self.std.contains(n) {
            return Some(short(n));
        }
        self.prelude.contains(n).then(|| short(n))
    }
}

/// Applies the constructor choices recorded by checking these occurrences.
pub(crate) fn selected_references(
    checked: &Checked,
    statements: &mut [Stmt],
) -> Result<(), String> {
    selected_references_in(checked, statements).map_err(|e| e.to_string())
}

fn selected_references_in(checked: &Checked, statements: &mut [Stmt]) -> Result<(), Message> {
    let mut choices = HashMap::new();
    for site in checked.ctor_sites.iter().filter(|site| site.expression) {
        let key = (site.occurrence, site.written.clone());
        if choices
            .insert(key, site.resolved.clone())
            .is_some_and(|prior| prior != site.resolved)
        {
            return Err(
                "one expression occurrence has incompatible checked constructor references".into(),
            );
        }
    }
    for statement in statements {
        crate::surface::walk::stmt(statement, &mut |term| {
            let id = term.id();
            if let TermKind::Var(name) = std::sync::Arc::make_mut(&mut term.kind) {
                if let Some(reference) = choices.get(&(id, name.clone())) {
                    *name = reference.clone();
                }
            }
        });
    }
    Ok(())
}

/// An unmapped constructor keeps the identity accepted for its family.
fn extracted_ctor(checked: &Checked, name: &Name) -> Option<Name> {
    checked
        .families
        .values()
        .any(|family| family.ctors.contains(name))
        .then(|| name.clone())
}

/// The Nib type a family of `std/` is extracted to.
pub const MAPPED_TYPES: &[(&str, &str)] = &[
    ("Nat", "nat"),
    ("Bool", "Bool"),
    ("Unit", "Unit"),
    ("List", "List"),
    ("Option", "Option"),
    ("Pair", "Pair"),
    ("Text", "Text"),
    ("Array", "Array"),
    ("Bytes", "Bytes"),
    ("Stack", "Vec"),
    ("Ordering", "Ordering"),
    ("Never", "Never"),
    ("UInt", "UInt"),
    ("UHost", "uhost"),
    ("SlotsModel", "Slots"),
    // `std/slots_store.taut`: the slots written out as fields; the
    // host's `Slots` is its representation.
    ("Slots", "Slots"),
    // The lent range of it (`struct &Slots`): a reference to the slots it lends.
    ("&Slots", "Slots"),
    ("SInt", "SInt"),
    ("Float", "Float"),
    ("Float32", "Float32"),
    ("Secret", "Secret"),
];

/// The parameters of a family that stay as arguments of the builtin it is
/// mapped onto; the rest are the proofs' (`SlotsModel` of `std/slots.taut`
/// takes the policy's `used` as a fourth argument, which `Slots` has no
/// place for). Empty: every parameter stays.
pub(crate) fn mapped_kept(builtin: &str) -> Vec<bool> {
    match builtin {
        "Slots" => vec![true, true, true, false],
        _ => Vec::new(),
    }
}

/// The file of `std/` whose type and functions the compiler replaces by the
/// host's representation and builtins, the type, and the functions
/// of that file that are replaced. A function written there with a body is
/// read by the kernel as written; what runs is the builtin, which no proof
/// covers, so the trust report lists each as unchecked.
pub const SWAPPED_FILE: &str = "slots_store.taut";
pub const SWAPPED_TYPE: &str = "Slots";
pub const SWAPPED_FNS: &[&str] = &[
    "Slots::new",
    "Slots::cap",
    "Slots::state",
    "Slots::mark",
    "Slots::get",
    "Slots::get_mut",
    "Slots::put",
    "Slots::take",
    "Slots::resize",
    "Slots::lend_range",
    "Slots::own_with",
    "Slots::lent_cap",
    "Slots::lent_get",
];

/// The Nib integer a family of fixed width applied to its width is:
/// `UInt(64)` is `u64`, `SInt(32)` is `i32`. `builtin` is what
/// [`mapped_type`] gives for the family (`UInt`, `SInt`); a width that Nib
/// has no integer of is `None`.
pub(crate) fn mapped_width(builtin: &str, args: &[SurfaceTerm]) -> Option<&'static str> {
    let [w] = args else { return None };
    let TermKind::Nat(w) = &*w.kind else {
        return None;
    };
    Some(match (builtin, w.as_str()) {
        ("UInt", "8") => "u8",
        ("UInt", "16") => "u16",
        ("UInt", "32") => "u32",
        ("UInt", "64") => "u64",
        ("SInt", "8") => "i8",
        ("SInt", "16") => "i16",
        ("SInt", "32") => "i32",
        ("SInt", "64") => "i64",
        _ => return None,
    })
}

/// The builtins of Nib that `builtin`, from [`mapped_type`], stands for:
/// each width's integer for a family of fixed width, else `builtin`.
pub(crate) fn mapped_natives(builtin: &'static str) -> Vec<&'static str> {
    match builtin {
        "UInt" => vec!["u8", "u16", "u32", "u64"],
        "SInt" => vec!["i8", "i16", "i32", "i64"],
        _ => vec![builtin],
    }
}

/// Whether `builtin`, from [`mapped_type`], is a family of fixed width,
/// which is a Nib integer only applied to its width ([`mapped_width`]).
pub(crate) fn is_width_family(builtin: &str) -> bool {
    matches!(builtin, "UInt" | "SInt")
}

fn mapped_type(name: &str) -> Option<&'static str> {
    MAPPED_TYPES
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, t)| *t)
}

/// A class that programs and proofs both read from the prelude
/// (`std/builtin/ord.taut`): a file does not declare it, an instance of it
/// for a type that extraction maps onto a builtin of Nib is not written
/// either (Nib's `std` has that instance), and its methods take their
/// arguments by borrow.
fn mapped_class(name: &str) -> bool {
    name == "Ord"
}

/// A class of `std/` that the prelude stands for with a class without
/// methods: `Policy` of `std/alloc.taut` and `PolicyState` of
/// `std/builtin/region.taut`, which `Region::new` asks of the state of a
/// region. Each instance of it, which the kernel checked with its laws, is
/// written as it is and once more as an instance of the prelude's class.
pub(super) fn marker_class(name: &str) -> bool {
    name == "Policy"
}

/// The prelude's class a [`marker_class`] instance is written as.
pub(super) const MARKER_PRELUDE_CLASS: &str = "PolicyState";

/// The heads mapped onto builtins of Nib whose instances of a mapped class
/// Nib's `std` declares (`std/builtin/classes.taut`).
fn std_instance_head(name: &str) -> bool {
    matches!(name, "Nat" | "Bool" | "Text")
}

/// Whether `s` is a declaration of the lent form of a type the host
/// represents (`Slots`): its `struct &T`, or its instance of `Lend`. Neither is
/// written to run: the host's reference is the lent form of the type, and what
/// the instance's functions do is the mapped functions.
pub(crate) fn lend_of_mapped(s: &Stmt, std: &StdNames) -> bool {
    match s {
        Stmt::Instance(i) => {
            i.class.as_str().rsplit("::").next() == Some("Lend")
                && head_name(&i.head).is_some_and(|n| std.of(n).and_then(mapped_type).is_some())
        }
        Stmt::Struct(d) => d.borrowed && std.of(&d.name).and_then(mapped_type).is_some(),
        _ => false,
    }
}

/// The constructor of an instance's head: `List` of `List(A)`.
/// The arguments of a call without the implicit ones written by name
/// (`f(<x: v>, a)` is `a` here): the checker records the values it fixed.
pub(crate) fn explicit_args(args: &[SurfaceTerm]) -> &[SurfaceTerm] {
    match args.split_first() {
        Some((first, rest)) if is_named_implicits(first) => rest,
        _ => args,
    }
}

/// `f(<x: v>, a)` as `f(v, a)`: the values in the order of `names`, when each
/// of them is written; otherwise the explicit arguments alone.
pub(crate) fn positional_args(args: &[SurfaceTerm], names: &[String]) -> Vec<SurfaceTerm> {
    let Some((first, rest)) = args.split_first() else {
        return Vec::new();
    };
    let TermKind::Record { fields, .. } = &*first.kind else {
        return args.to_vec();
    };
    if !is_named_implicits(first) {
        return args.to_vec();
    }
    let values: Option<Vec<SurfaceTerm>> = names
        .iter()
        .map(|n| {
            let base = match n.rsplit_once('\'') {
                Some((base, k)) if k.chars().all(|c| c.is_ascii_digit()) => base,
                _ => n.as_str(),
            };
            fields
                .iter()
                .find(|(f, _)| f == base)
                .map(|(_, v)| v.clone())
        })
        .collect();
    match values {
        Some(mut values) if values.len() == fields.len() => {
            values.extend(rest.iter().cloned());
            values
        }
        _ => rest.to_vec(),
    }
}

pub(crate) fn is_named_implicits(t: &SurfaceTerm) -> bool {
    matches!(&*t.kind, TermKind::Record { name, .. }
        if name.spelling() == Some(tauto_surface::IMPLICITS))
}

fn head_name(head: &SurfaceTerm) -> Option<&Name> {
    match &*head.kind {
        TermKind::Var(n) => Some(n),
        TermKind::App { function, .. } => head_name(function),
        _ => None,
    }
}

/// The functions of `std/` extracted to an expression of Nib: `$0`, `$1`,
/// … are the value arguments, each evaluated once (they are bound first
/// when used more than once).
pub const MAPPED_FNS: &[(&str, &str)] = &[
    ("Nat::lt", "$0 < $1"),
    ("Nat::le", "$0 <= $1"),
    ("Nat::eq", "$0 == $1"),
    ("Nat::pred", "extract_nat_sub($0, 1)"),
    ("Nat::add", "$0 + $1"),
    ("Nat::sub", "extract_nat_sub($0, $1)"),
    ("Nat::mul", "$0 * $1"),
    ("Nat::div_nz", "extract_nat_div($0, $1)"),
    ("Nat::rem_nz", "extract_nat_mod($0, $1)"),
    ("Nat::divmod", "extract_nat_divmod($0, $1, $2, $3)"),
    ("Bool::and", "$0 && $1"),
    ("Bool::or", "$0 || $1"),
    ("not", "not($0)"),
    ("Bool::eq", "$0 == $1"),
    ("Text::bytes", "extract_text_bytes($0)"),
    ("Text::len", "Nat::of_u64(Text::len(&$0))"),
    ("Text::byte", "extract_text_byte($0, $1)"),
    ("Text::all_bytes", "extract_text_all_bytes($0, $1)"),
    (
        "Text::slice",
        "Text::slice(&$0, U64::of_nat($1), U64::of_nat($2))",
    ),
    // The builtin by its full name: inside `module Text`, `concat` would
    // be the extracted `Text::concat` itself.
    ("Text::concat", "std::prelude::concat($0, $1)"),
    ("Text::concat_all", "extract_text_concat_all($0)"),
    ("Text::ordering", "extract_ordering(Text::compare(&$0, &$1))"),
    ("Text::eq", "$0 == $1"),
    // The equality the inductive derives compares the bytes; the bytes of
    // a text at run time are its UTF-8, so Nib's `==` on texts is the same.
    ("Text::beq", "$0 == $1"),
    ("Text::of_nat", "Text::of_nat($0)"),
    ("Text::of_code_point", "extract_text_of_code_point($0)"),
    (
        "Text::utf8_of_code_point",
        "extract_text_utf8_of_code_point($0)",
    ),
    ("Text::of_utf8", "extract_text_of_utf8($0)"),
    ("Array::of_list", "Array::of_list($0)"),
    ("Array::to_list", "Array::to_list($0)"),
    ("Array::get", "Array::get($0, U64::of_nat($1))"),
    ("Array::len", "Nat::of_u64(Array::len($0))"),
    ("Array::set", "Array::set($0, U64::of_nat($1), $2)"),
    ("Bytes::of_list", "Bytes::of_list($0)"),
    ("Bytes::to_list", "Bytes::to_list($0)"),
    ("Bytes::len", "Nat::of_u64(Bytes::len($0))"),
    ("Bytes::get", "Bytes::get($0, U64::of_nat($1))"),
    (
        "Bytes::find",
        "Nat::of_u64(Bytes::find($0, U64::of_nat($1), U64::of_nat($2), U64::of_nat($3)))",
    ),
    (
        "Bytes::slice",
        "Bytes::slice($0, U64::of_nat($1), U64::of_nat($2))",
    ),
    ("Bytes::concat", "Bytes::concat($0, $1)"),
    ("Bytes::eq", "Bytes::eq($0, $1)"),
    ("Bytes::of_text", "Bytes::of_text($0)"),
    ("Text::of_bytes", "Text::of_bytes($0)"),
    // `Slots` of `std/slots_store.taut`: the functions written over its
    // fields are replaced by the builtins (the swap is limited to the
    // slots type and these functions). `SWAPPED_FNS` lists them for the
    // trust report. An operation that returns the next slots is the builtin on
    // the slots taken by value; the proofs it takes are not run.
    ("Slots::new", "Slots::new($0, $1, $2)"),
    ("Slots::cap", "Slots::cap($0)"),
    ("Slots::state", "Slots::state($0)"),
    ("Slots::mark", "Slots::mark($0, $1)"),
    ("Slots::get", "Slots::get($0, $1)"),
    ("Slots::get_mut", "Slots::get_mut($0, $1)"),
    ("Slots::lend_range", "$0"),
    ("Slots::own_with", "Slots::copy($2, $0, $1)"),
    ("Slots::lent_cap", "Slots::cap($0)"),
    ("Slots::lent_get", "Slots::get($0, $1)"),
    (
        "Slots::put",
        "{ let slots_i := $1\n let slots_m := $2\n let slots_x := $3\n let slots_t := $4\n var s := $0\n Slots::put(&mut s, slots_i, slots_m, slots_x, slots_t)\n s }",
    ),
    (
        "Slots::take",
        "{ let slots_i := $1\n let slots_m := $2\n let slots_t := $3\n var s := $0\n let x := Slots::take(&mut s, slots_i, slots_m, slots_t)\n #(s, x) }",
    ),
    (
        "Slots::resize",
        "{ let slots_c := $1\n let slots_m := $2\n let slots_t := $3\n var s := $0\n Slots::resize(&mut s, slots_c, slots_m, slots_t)\n s }",
    ),
    // `SlotsModel` is `Slots`: a model operation that returns the next model is
    // the builtin on the model taken by value. The values are the policy
    // (`u`, `em`, `vac`, `cp`, `pu`, `ta`, `rc`, `fu`), then the arguments.
    (
        "SlotsModel::new",
        "{ let slots_cap := $8\n Slots::new(slots_cap, $1(slots_cap), $2) }",
    ),
    ("SlotsModel::state", "Slots::state($1)"),
    ("SlotsModel::mark_at", "Slots::mark($1, $2)"),
    ("SlotsModel::get", "Slots::get($1, $2)"),
    ("SlotsModel::get_mut", "Slots::get_mut($1, $2)"),
    (
        "SlotsModel::put",
        "{ let slots_i := $9\n let slots_m := $10\n let slots_x := $11\n let slots_t := $12\n var s := $8\n Slots::put(&mut s, slots_i, slots_m, slots_x, slots_t)\n s }",
    ),
    (
        "SlotsModel::put_m",
        "{ let slots_i := $9\n let slots_m := $10\n let slots_x := $11\n let slots_t := $12\n Slots::put($8, slots_i, slots_m, slots_x, slots_t) }",
    ),
    (
        "SlotsModel::resize_put_m",
        "{ let slots_c := $9\n let slots_t1 := $10\n let slots_i := $11\n let slots_m := $12\n let slots_x := $13\n let slots_t2 := $14\n Slots::resize($8, slots_c, $2, slots_t1)\n Slots::put($8, slots_i, slots_m, slots_x, slots_t2) }",
    ),
    (
        "SlotsModel::move_m",
        "{ let slots_i := $9\n let slots_m1 := $10\n let slots_t1 := $11\n let slots_j := $12\n let slots_m2 := $13\n let slots_t2 := $14\n let slots_x := Slots::take($8, slots_i, slots_m1, slots_t1)\n Slots::put($8, slots_j, slots_m2, slots_x, slots_t2) }",
    ),
    (
        "SlotsModel::swap_m",
        "{ let slots_i := $2\n let slots_x := $3\n let slots_m := Slots::mark($1, slots_i)\n let slots_t := Slots::state($1)\n let slots_old := Slots::take($1, slots_i, slots_m, slots_t)\n Slots::put($1, slots_i, slots_m, slots_x, slots_t)\n slots_old }",
    ),
    (
        "SlotsModel::take_m",
        "{ let slots_i := $9\n let slots_m := $10\n let slots_t := $11\n Slots::take($8, slots_i, slots_m, slots_t) }",
    ),
    (
        "SlotsModel::resize_m",
        "{ let slots_c := $9\n let slots_m := $2\n let slots_t := $10\n Slots::resize($8, slots_c, slots_m, slots_t) }",
    ),
    (
        "SlotsModel::take",
        "{ let slots_i := $9\n let slots_m := $10\n let slots_t := $11\n var s := $8\n let x := Slots::take(&mut s, slots_i, slots_m, slots_t)\n #(s, x) }",
    ),
    (
        "SlotsModel::resize",
        "{ let slots_c := $9\n let slots_m := $2\n let slots_t := $10\n var s := $8\n Slots::resize(&mut s, slots_c, slots_m, slots_t)\n s }",
    ),
    ("Stack::new", "Vec::new()"),
    ("Stack::push", "Vec::push($0, $1)"),
    ("Stack::pop", "Vec::pop($0)"),
    ("Stack::len", "Nat::of_u64(Vec::len($0))"),
    ("Stack::is_empty", "(Vec::len($0) == 0)"),
    // Nib's `Never` is below every type.
    ("Never::elim", "$0"),
    // The operators of a width (`check/machine.rs` in the kernel crate reads
    // `a + b` at `SInt(64)` as `SInt::add_or_overflow64(a, b)`) are Nib's
    // own: each performs `overflow` and `divzero` where the function does.
    ("UInt::add_or_overflow8", "$0 + $1"),
    ("UInt::sub_or_overflow8", "$0 - $1"),
    ("UInt::mul_or_overflow8", "$0 * $1"),
    ("UInt::div8", "div($0, $1)"),
    ("UInt::rem8", "mod($0, $1)"),
    ("UInt::add_or_overflow32", "$0 + $1"),
    ("UInt::sub_or_overflow32", "$0 - $1"),
    ("UInt::mul_or_overflow32", "$0 * $1"),
    ("UInt::div32", "div($0, $1)"),
    ("UInt::rem32", "mod($0, $1)"),
    ("UInt::add_or_overflow64", "$0 + $1"),
    ("UInt::sub_or_overflow64", "$0 - $1"),
    ("UInt::mul_or_overflow64", "$0 * $1"),
    ("UInt::div64", "div($0, $1)"),
    ("UInt::rem64", "mod($0, $1)"),
    ("SInt::add_or_overflow32", "$0 + $1"),
    ("SInt::sub_or_overflow32", "$0 - $1"),
    ("SInt::mul_or_overflow32", "$0 * $1"),
    ("SInt::neg_or_overflow32", "-($0)"),
    ("SInt::tdiv32", "div($0, $1)"),
    ("SInt::tmod32", "mod($0, $1)"),
    ("SInt::add_or_overflow64", "$0 + $1"),
    ("SInt::sub_or_overflow64", "$0 - $1"),
    ("SInt::mul_or_overflow64", "$0 * $1"),
    ("SInt::neg_or_overflow64", "-($0)"),
    ("SInt::tdiv64", "div($0, $1)"),
    ("SInt::tmod64", "mod($0, $1)"),
    ("SInt::mk32", "extract_i32_of_fitting($0)"),
    ("SInt::mk64", "extract_i64_of_fitting($0)"),
    ("UInt::mk8", "U8::of_u64(U64::of_nat($0))"),
    ("UInt::mk32", "U32::of_u64(U64::of_nat($0))"),
    ("UInt::mk64", "U64::of_nat($0)"),
    ("UInt::val8", "Nat::of_u64(U64::of_u8($0))"),
    ("UInt::of_decided8", "extract_u8_of_decided($0, $1)"),
    ("UInt::of_nat_checked8", "extract_u8_of_nat($0)"),
    ("UInt::add8", "$0 + $1"),
    ("UInt::sub8", "$0 - $1"),
    ("UInt::mul8", "$0 * $1"),
    ("UInt::checked_add8", "extract_u8_checked_add($0, $1)"),
    ("UInt::checked_sub8", "extract_u8_checked_sub($0, $1)"),
    ("UInt::checked_mul8", "extract_u8_checked_mul($0, $1)"),
    ("UInt::lt8", "$0 < $1"),
    ("UInt::le8", "$0 <= $1"),
    ("UInt::eq8", "$0 == $1"),
    (
        "UInt::of_nat_mod8",
        "U8::of_u64(U64::of_nat(extract_nat_mod($0, 256)))",
    ),
    (
        "UInt::wrapping_add8",
        "extract_u8_wrap(extract_u8_nat($0) + extract_u8_nat($1))",
    ),
    (
        "UInt::wrapping_sub8",
        "extract_u8_wrap(extract_u8_nat($0) + extract_u8_modulus() - extract_u8_nat($1))",
    ),
    (
        "UInt::wrapping_mul8",
        "extract_u8_wrap(extract_u8_nat($0) * extract_u8_nat($1))",
    ),
    ("UInt::val32", "Nat::of_u64(U64::of_u32($0))"),
    ("UInt::of_decided32", "extract_u32_of_decided($0, $1)"),
    ("UInt::of_nat_checked32", "extract_u32_of_nat($0)"),
    ("UInt::add32", "$0 + $1"),
    ("UInt::sub32", "$0 - $1"),
    ("UInt::mul32", "$0 * $1"),
    ("UInt::checked_add32", "extract_u32_checked_add($0, $1)"),
    ("UInt::checked_sub32", "extract_u32_checked_sub($0, $1)"),
    ("UInt::checked_mul32", "extract_u32_checked_mul($0, $1)"),
    ("UInt::lt32", "$0 < $1"),
    ("UInt::le32", "$0 <= $1"),
    ("UInt::eq32", "$0 == $1"),
    (
        "UInt::of_nat_mod32",
        "U32::of_u64(U64::of_nat(extract_nat_mod($0, 4294967296)))",
    ),
    (
        "UInt::wrapping_add32",
        "extract_u32_wrap(extract_u32_nat($0) + extract_u32_nat($1))",
    ),
    (
        "UInt::wrapping_sub32",
        "extract_u32_wrap(extract_u32_nat($0) + extract_u32_modulus() - extract_u32_nat($1))",
    ),
    (
        "UInt::wrapping_mul32",
        "extract_u32_wrap(extract_u32_nat($0) * extract_u32_nat($1))",
    ),
    ("UInt::val64", "Nat::of_u64($0)"),
    // `uhost`: the proofs of the kernel's `UHost` functions are not run, and
    // each is one machine operation (`std/prelude/Num.taut`).
    ("UHost::val", "Nat::of_u64(U64::of_uhost($0))"),
    ("UHost::zero", "UHost::of_u64_below(0)"),
    ("UHost::lt", "$0 < $1"),
    ("UHost::le", "$0 <= $1"),
    ("UHost::eq", "$0 == $1"),
    ("UHost::succ_below_proved", "UHost::succ_below($0)"),
    ("UHost::pred_nz_proved", "UHost::pred_nz($0)"),
    ("UHost::add_within_proved", "UHost::add_within($0, $1)"),
    ("UHost::sub_proved", "UHost::sub($0, $1)"),
    ("UHost::of_u64_below_proved", "UHost::of_u64_below($0)"),
    ("UHost::of_u32", "UHost::of_u64_below(U64::of_u32($0))"),
    ("UHost::to_u64", "U64::of_uhost($0)"),
    ("UInt::of_decided64", "extract_u64_of_decided($0, $1)"),
    ("UInt::of_nat_checked64", "extract_u64_of_nat($0)"),
    (
        "UInt::of_nat_mod64",
        "U64::of_nat(extract_nat_mod($0, 18446744073709551616))",
    ),
    ("UInt::add64", "$0 + $1"),
    ("UInt::sub64", "$0 - $1"),
    ("UInt::mul64", "$0 * $1"),
    ("UInt::checked_add64", "extract_u64_checked_add($0, $1)"),
    ("UInt::checked_sub64", "extract_u64_checked_sub($0, $1)"),
    ("UInt::checked_mul64", "extract_u64_checked_mul($0, $1)"),
    ("UInt::lt64", "$0 < $1"),
    ("UInt::le64", "$0 <= $1"),
    ("UInt::eq64", "$0 == $1"),
    ("UInt::wrapping_add64", "U64::wrapping_add($0, $1)"),
    ("UInt::wrapping_sub64", "U64::wrapping_sub($0, $1)"),
    ("UInt::wrapping_mul64", "U64::wrapping_mul($0, $1)"),
    ("UInt::and32", "U32::and($0, $1)"),
    ("UInt::or32", "U32::or($0, $1)"),
    ("UInt::xor32", "U32::xor($0, $1)"),
    (
        "UInt::shl32",
        "U32::shl($0, U64::of_nat(extract_nat_mod($1, 32)))",
    ),
    (
        "UInt::shr32",
        "U32::shr($0, U64::of_nat(extract_nat_mod($1, 32)))",
    ),
    (
        "UInt::rotl32",
        "U32::rotl($0, U64::of_nat(extract_nat_mod($1, 32)))",
    ),
    (
        "UInt::rotr32",
        "U32::rotr($0, U64::of_nat(extract_nat_mod($1, 32)))",
    ),
    ("UInt::and64", "U64::and($0, $1)"),
    ("UInt::or64", "U64::or($0, $1)"),
    ("UInt::xor64", "U64::xor($0, $1)"),
    (
        "UInt::shl64",
        "U64::shl($0, U64::of_nat(extract_nat_mod($1, 64)))",
    ),
    (
        "UInt::shr64",
        "U64::shr($0, U64::of_nat(extract_nat_mod($1, 64)))",
    ),
    (
        "UInt::rotl64",
        "U64::rotl($0, U64::of_nat(extract_nat_mod($1, 64)))",
    ),
    (
        "UInt::rotr64",
        "U64::rotr($0, U64::of_nat(extract_nat_mod($1, 64)))",
    ),
    // The secret words run in constant time (`docs/design/secret.md`).
    ("Ct::u8_add", "Ct::u8_add($0, $1)"),
    ("Ct::u8_sub", "Ct::u8_sub($0, $1)"),
    ("Ct::u8_mul", "Ct::u8_mul($0, $1)"),
    ("Ct::u8_and", "Ct::u8_and($0, $1)"),
    ("Ct::u8_or", "Ct::u8_or($0, $1)"),
    ("Ct::u8_xor", "Ct::u8_xor($0, $1)"),
    ("Ct::u8_eq", "Ct::u8_eq($0, $1)"),
    ("Ct::u8_lt", "Ct::u8_lt($0, $1)"),
    ("Ct::u8_not", "Ct::u8_not($0)"),
    (
        "Ct::u8_shl",
        "Ct::u8_shl($0, U64::of_nat(extract_nat_mod($1, 8)))",
    ),
    (
        "Ct::u8_shr",
        "Ct::u8_shr($0, U64::of_nat(extract_nat_mod($1, 8)))",
    ),
    (
        "Ct::u8_rotl",
        "Ct::u8_rotl($0, U64::of_nat(extract_nat_mod($1, 8)))",
    ),
    (
        "Ct::u8_rotr",
        "Ct::u8_rotr($0, U64::of_nat(extract_nat_mod($1, 8)))",
    ),
    ("Ct::u8_select", "Ct::u8_select($0, $1, $2)"),
    ("Ct::u32_add", "Ct::u32_add($0, $1)"),
    ("Ct::u32_sub", "Ct::u32_sub($0, $1)"),
    ("Ct::u32_mul", "Ct::u32_mul($0, $1)"),
    ("Ct::u32_and", "Ct::u32_and($0, $1)"),
    ("Ct::u32_or", "Ct::u32_or($0, $1)"),
    ("Ct::u32_xor", "Ct::u32_xor($0, $1)"),
    ("Ct::u32_eq", "Ct::u32_eq($0, $1)"),
    ("Ct::u32_lt", "Ct::u32_lt($0, $1)"),
    ("Ct::u32_not", "Ct::u32_not($0)"),
    (
        "Ct::u32_shl",
        "Ct::u32_shl($0, U64::of_nat(extract_nat_mod($1, 32)))",
    ),
    (
        "Ct::u32_shr",
        "Ct::u32_shr($0, U64::of_nat(extract_nat_mod($1, 32)))",
    ),
    (
        "Ct::u32_rotl",
        "Ct::u32_rotl($0, U64::of_nat(extract_nat_mod($1, 32)))",
    ),
    (
        "Ct::u32_rotr",
        "Ct::u32_rotr($0, U64::of_nat(extract_nat_mod($1, 32)))",
    ),
    ("Ct::u32_select", "Ct::u32_select($0, $1, $2)"),
    ("Ct::u64_add", "Ct::u64_add($0, $1)"),
    ("Ct::u64_sub", "Ct::u64_sub($0, $1)"),
    ("Ct::u64_mul", "Ct::u64_mul($0, $1)"),
    ("Ct::u64_and", "Ct::u64_and($0, $1)"),
    ("Ct::u64_or", "Ct::u64_or($0, $1)"),
    ("Ct::u64_xor", "Ct::u64_xor($0, $1)"),
    ("Ct::u64_eq", "Ct::u64_eq($0, $1)"),
    ("Ct::u64_lt", "Ct::u64_lt($0, $1)"),
    ("Ct::u64_not", "Ct::u64_not($0)"),
    (
        "Ct::u64_shl",
        "Ct::u64_shl($0, U64::of_nat(extract_nat_mod($1, 64)))",
    ),
    (
        "Ct::u64_shr",
        "Ct::u64_shr($0, U64::of_nat(extract_nat_mod($1, 64)))",
    ),
    (
        "Ct::u64_rotl",
        "Ct::u64_rotl($0, U64::of_nat(extract_nat_mod($1, 64)))",
    ),
    (
        "Ct::u64_rotr",
        "Ct::u64_rotr($0, U64::of_nat(extract_nat_mod($1, 64)))",
    ),
    ("Ct::u64_select", "Ct::u64_select($0, $1, $2)"),
    ("Ct::u64_mul_hi", "Ct::u64_mul_hi($0, $1)"),
    ("Ct::u64_of_u8", "Ct::u64_of_u8($0)"),
    ("Ct::u64_of_u32", "Ct::u64_of_u32($0)"),
    ("Ct::u32_of_u8", "Ct::u32_of_u8($0)"),
    ("Ct::u8_of_u32", "Ct::u8_of_u32($0)"),
    ("Ct::u8_of_u64", "Ct::u8_of_u64($0)"),
    ("Ct::u32_of_u64", "Ct::u32_of_u64($0)"),
    ("Ct::bytes_len", "Nat::of_u64(Ct::bytes_len($0))"),
    ("Ct::bytes_get", "Ct::bytes_get($0, U64::of_nat($1))"),
    ("Ct::bool_and", "Ct::bool_and($0, $1)"),
    ("Ct::bool_or", "Ct::bool_or($0, $1)"),
    ("Ct::bool_not", "Ct::bool_not($0)"),
    ("Ct::bool_select", "Ct::bool_select($0, $1, $2)"),
    ("expose", "expose($0)"),
    ("SInt::val32", "extract_i32_int($0)"),
    ("SInt::of_decided32", "extract_i32_of_decided($0, $1)"),
    ("SInt::of_int32", "extract_i32_of_int($0)"),
    ("SInt::add32", "$0 + $1"),
    ("SInt::sub32", "$0 - $1"),
    ("SInt::mul32", "$0 * $1"),
    (
        "SInt::checked_add32",
        "extract_i32_of_int(Int::add(extract_i32_int($0), extract_i32_int($1)))",
    ),
    (
        "SInt::checked_sub32",
        "extract_i32_of_int(Int::sub(extract_i32_int($0), extract_i32_int($1)))",
    ),
    (
        "SInt::checked_mul32",
        "extract_i32_of_int(Int::mul(extract_i32_int($0), extract_i32_int($1)))",
    ),
    ("SInt::lt32", "$0 < $1"),
    ("SInt::le32", "$0 <= $1"),
    ("SInt::eq32", "$0 == $1"),
    ("SInt::val64", "extract_i64_int($0)"),
    ("SInt::of_decided64", "extract_i64_of_decided($0, $1)"),
    ("SInt::of_int64", "extract_i64_of_int($0)"),
    ("SInt::add64", "$0 + $1"),
    ("SInt::sub64", "$0 - $1"),
    ("SInt::mul64", "$0 * $1"),
    (
        "SInt::checked_add64",
        "extract_i64_of_int(Int::add(extract_i64_int($0), extract_i64_int($1)))",
    ),
    (
        "SInt::checked_sub64",
        "extract_i64_of_int(Int::sub(extract_i64_int($0), extract_i64_int($1)))",
    ),
    (
        "SInt::checked_mul64",
        "extract_i64_of_int(Int::mul(extract_i64_int($0), extract_i64_int($1)))",
    ),
    ("SInt::lt64", "$0 < $1"),
    ("SInt::le64", "$0 <= $1"),
    ("SInt::eq64", "$0 == $1"),
    ("Float::raw", "Nat::of_u64(Float::bits($0))"),
    (
        "Float::of_raw",
        "Float::of_bits(U64::of_nat(extract_nat_mod($0, 18446744073709551616)))",
    ),
    ("Float::bits", "Float::bits($0)"),
    ("Float::of_bits", "Float::of_bits($0)"),
    ("Float::add", "$0 + $1"),
    ("Float::sub", "$0 - $1"),
    ("Float::mul", "$0 * $1"),
    ("Float::neg", "-$0"),
    ("Float::div", "$0 / $1"),
    ("Float::checked_div", "extract_float_checked_div($0, $1)"),
    ("Float::is_zero", "$0 == 0.0"),
    ("Float::is_infinite", "extract_float_is_infinite($0)"),
    ("Float::eq", "$0 == $1"),
    ("Float::lt", "$0 < $1"),
    ("Float::le", "$0 <= $1"),
    ("Float::of_i64", "Float::of_i64($0)"),
    ("SInt::of_float_checked64", "extract_i64_of_float_checked($0)"),
    ("Float::is_nan", "Float::is_nan($0)"),
    ("Float::abs", "Float::abs($0)"),
    ("Float::sqrt", "Float::sqrt($0)"),
    ("Float::trunc", "Float::trunc($0)"),
    ("Float::floor", "Float::floor($0)"),
    ("Float::ceil", "Float::ceil($0)"),
    ("Float::round", "Float::round($0)"),
    ("Float::cbrt", "Float::cbrt($0)"),
    ("Float::exp", "Float::exp($0)"),
    ("Float::ln", "Float::ln($0)"),
    ("Float::log2", "Float::log2($0)"),
    ("Float::log10", "Float::log10($0)"),
    ("Float::pow", "Float::pow($0, $1)"),
    ("Float::sin", "Float::sin($0)"),
    ("Float::cos", "Float::cos($0)"),
    ("Float::tan", "Float::tan($0)"),
    ("Float::asin", "Float::asin($0)"),
    ("Float::acos", "Float::acos($0)"),
    ("Float::atan", "Float::atan($0)"),
    ("Float::atan2", "Float::atan2($0, $1)"),
    ("Float::sinh", "Float::sinh($0)"),
    ("Float::cosh", "Float::cosh($0)"),
    ("Float::tanh", "Float::tanh($0)"),
    ("Text::of_float", "Text::of_float($0)"),
    ("Float::of_text", "Float::of_text($0)"),
    (
        "Float32::raw",
        "Nat::of_u64(U64::of_u32(Float32::bits($0)))",
    ),
    (
        "Float32::of_raw",
        "Float32::of_bits(U32::of_u64(U64::of_nat(extract_nat_mod($0, 4294967296))))",
    ),
    ("Float32::bits", "Float32::bits($0)"),
    ("Float32::of_bits", "Float32::of_bits($0)"),
    ("Float32::of_float", "Float32::of_float($0)"),
    ("Float::of_float32", "Float::of_float32($0)"),
    ("Float32::add", "$0 + $1"),
    ("Float32::sub", "$0 - $1"),
    ("Float32::mul", "$0 * $1"),
    ("Float32::neg", "-$0"),
    ("Float32::div", "$0 / $1"),
    (
        "Float32::checked_div",
        "extract_float32_checked_div($0, $1)",
    ),
    ("Float32::is_zero", "$0 == Float32::of_float(0.0)"),
    ("Float32::is_infinite", "extract_float32_is_infinite($0)"),
    ("Float32::eq", "$0 == $1"),
    ("Float32::lt", "$0 < $1"),
    ("Float32::le", "$0 <= $1"),
    ("Float32::is_nan", "Float32::is_nan($0)"),
    ("Float32::abs", "Float32::abs($0)"),
    ("Float32::sqrt", "Float32::sqrt($0)"),
    ("Float32::trunc", "Float32::trunc($0)"),
    ("Float32::floor", "Float32::floor($0)"),
    ("Float32::ceil", "Float32::ceil($0)"),
    ("Float32::round", "Float32::round($0)"),
    ("Float32::cbrt", "Float32::cbrt($0)"),
    ("Float32::exp", "Float32::exp($0)"),
    ("Float32::ln", "Float32::ln($0)"),
    ("Float32::log2", "Float32::log2($0)"),
    ("Float32::log10", "Float32::log10($0)"),
    ("Float32::sin", "Float32::sin($0)"),
    ("Float32::cos", "Float32::cos($0)"),
    ("Float32::tan", "Float32::tan($0)"),
    ("Float32::asin", "Float32::asin($0)"),
    ("Float32::acos", "Float32::acos($0)"),
    ("Float32::atan", "Float32::atan($0)"),
    ("Float32::sinh", "Float32::sinh($0)"),
    ("Float32::cosh", "Float32::cosh($0)"),
    ("Float32::tanh", "Float32::tanh($0)"),
    ("Float32::pow", "Float32::pow($0, $1)"),
    ("Float32::atan2", "Float32::atan2($0, $1)"),
    // A value of `Quot` is a value of its representation.
    ("Quot::mk", "$0"),
    ("Quot::lift", "$0($1)"),
    ("UInt::add_or_overflow16", "$0 + $1"),
    ("UInt::sub_or_overflow16", "$0 - $1"),
    ("UInt::mul_or_overflow16", "$0 * $1"),
    ("UInt::div16", "div($0, $1)"),
    ("UInt::rem16", "mod($0, $1)"),
    ("SInt::add_or_overflow8", "$0 + $1"),
    ("SInt::add_or_overflow16", "$0 + $1"),
    ("SInt::sub_or_overflow8", "$0 - $1"),
    ("SInt::sub_or_overflow16", "$0 - $1"),
    ("SInt::mul_or_overflow8", "$0 * $1"),
    ("SInt::mul_or_overflow16", "$0 * $1"),
    ("SInt::neg_or_overflow8", "-($0)"),
    ("SInt::neg_or_overflow16", "-($0)"),
    ("SInt::tdiv8", "div($0, $1)"),
    ("SInt::tdiv16", "div($0, $1)"),
    ("SInt::tmod8", "mod($0, $1)"),
    ("SInt::tmod16", "mod($0, $1)"),
    ("SInt::mk8", "extract_i8_of_fitting($0)"),
    ("SInt::mk16", "extract_i16_of_fitting($0)"),
    ("UInt::mk16", "U16::of_u64(U64::of_nat($0))"),
    ("UInt::val16", "Nat::of_u64(U64::of_u16($0))"),
    ("UInt::of_decided16", "extract_u16_of_decided($0, $1)"),
    ("UInt::of_nat_checked16", "extract_u16_of_nat($0)"),
    ("UInt::add16", "$0 + $1"),
    ("UInt::sub16", "$0 - $1"),
    ("UInt::mul16", "$0 * $1"),
    ("UInt::checked_add16", "extract_u16_checked_add($0, $1)"),
    ("UInt::checked_sub16", "extract_u16_checked_sub($0, $1)"),
    ("UInt::checked_mul16", "extract_u16_checked_mul($0, $1)"),
    ("UInt::lt16", "$0 < $1"),
    ("UInt::le16", "$0 <= $1"),
    ("UInt::eq16", "$0 == $1"),
    ("UInt::of_nat_mod16", "U16::of_u64(U64::of_nat(extract_nat_mod($0, 65536)))"),
    ("UInt::wrapping_add16", "extract_u16_wrap(extract_u16_nat($0) + extract_u16_nat($1))"),
    ("UInt::wrapping_sub16", "extract_u16_wrap(extract_u16_nat($0) + extract_u16_modulus() - extract_u16_nat($1))"),
    ("UInt::wrapping_mul16", "extract_u16_wrap(extract_u16_nat($0) * extract_u16_nat($1))"),
    ("SInt::val8", "extract_i8_int($0)"),
    ("SInt::val16", "extract_i16_int($0)"),
    ("SInt::of_decided8", "extract_i8_of_decided($0, $1)"),
    ("SInt::of_decided16", "extract_i16_of_decided($0, $1)"),
    ("SInt::of_int8", "extract_i8_of_int($0)"),
    ("SInt::of_int16", "extract_i16_of_int($0)"),
    ("SInt::add8", "$0 + $1"),
    ("SInt::add16", "$0 + $1"),
    ("SInt::sub8", "$0 - $1"),
    ("SInt::sub16", "$0 - $1"),
    ("SInt::mul8", "$0 * $1"),
    ("SInt::mul16", "$0 * $1"),
    ("SInt::checked_add8", "extract_i8_of_int(Int::add(extract_i8_int($0), extract_i8_int($1)))"),
    ("SInt::checked_add16", "extract_i16_of_int(Int::add(extract_i16_int($0), extract_i16_int($1)))"),
    ("SInt::checked_sub8", "extract_i8_of_int(Int::sub(extract_i8_int($0), extract_i8_int($1)))"),
    ("SInt::checked_sub16", "extract_i16_of_int(Int::sub(extract_i16_int($0), extract_i16_int($1)))"),
    ("SInt::checked_mul8", "extract_i8_of_int(Int::mul(extract_i8_int($0), extract_i8_int($1)))"),
    ("SInt::checked_mul16", "extract_i16_of_int(Int::mul(extract_i16_int($0), extract_i16_int($1)))"),
    ("SInt::lt8", "$0 < $1"),
    ("SInt::lt16", "$0 < $1"),
    ("SInt::le8", "$0 <= $1"),
    ("SInt::le16", "$0 <= $1"),
    ("SInt::eq8", "$0 == $1"),
    ("SInt::eq16", "$0 == $1"),
];

fn mapped_fn(name: &str) -> Option<&'static str> {
    MAPPED_FNS.iter().find(|(n, _)| *n == name).map(|(_, t)| *t)
}

/// The mapped functions whose names Nib's builtins already have: they get
/// no function of their own (a Nib program calls the builtin).
fn builtin_name(name: &str) -> bool {
    matches!(
        name,
        "Text::len"
            | "Text::byte"
            | "Text::slice"
            | "Text::of_code_point"
            | "Text::of_utf8"
            | "Array::of_list"
            | "Array::to_list"
            | "Array::get"
            | "Array::len"
            | "Array::set"
            | "Bytes::of_list"
            | "Bytes::to_list"
            | "Bytes::len"
            | "Bytes::get"
            | "Bytes::find"
            | "Bytes::slice"
            | "Bytes::concat"
            | "Bytes::eq"
            | "Bytes::of_text"
            | "Text::of_bytes"
            | "Float::bits"
            | "Float::of_bits"
            | "Float::of_i64"
            | "Float::is_nan"
            | "Float::abs"
            | "Float::sqrt"
            | "Float::trunc"
            | "Float::floor"
            | "Float::ceil"
            | "Float::round"
            | "Float::cbrt"
            | "Float::exp"
            | "Float::ln"
            | "Float::log2"
            | "Float::log10"
            | "Float::pow"
            | "Float::sin"
            | "Float::cos"
            | "Float::tan"
            | "Float::asin"
            | "Float::acos"
            | "Float::atan"
            | "Float::atan2"
            | "Float::sinh"
            | "Float::cosh"
            | "Float::tanh"
            | "Text::of_float"
            | "Float::of_text"
            | "Float32::bits"
            | "Float32::of_bits"
            | "Float32::of_float"
            | "Float32::is_nan"
            | "Float32::abs"
            | "Float32::sqrt"
            | "Float32::trunc"
            | "Float32::floor"
            | "Float32::ceil"
            | "Float32::round"
            | "Float32::cbrt"
            | "Float32::exp"
            | "Float32::ln"
            | "Float32::log2"
            | "Float32::log10"
            | "Float32::pow"
            | "Float32::sin"
            | "Float32::cos"
            | "Float32::tan"
            | "Float32::asin"
            | "Float32::acos"
            | "Float32::atan"
            | "Float32::atan2"
            | "Float32::sinh"
            | "Float32::cosh"
            | "Float32::tanh"
            | "Float::of_float32"
    )
}

/// The mapped functions that are written out at each call, with the places
/// they borrow (`&mut s`) as the arguments: they get no function of their own.
fn inline_only(name: &str) -> bool {
    matches!(
        name,
        "Stack::new" | "Stack::push" | "Stack::pop" | "Stack::len" | "Stack::is_empty"
            | "Slots::new" | "Slots::cap" | "Slots::state" | "Slots::mark"
            | "Slots::get" | "Slots::get_mut" | "Slots::put"
            | "Slots::take" | "Slots::resize" | "Slots::lend_range" | "Slots::own_with"
            | "Slots::lent_cap" | "Slots::lent_get"
            | "SlotsModel::new" | "SlotsModel::state" | "SlotsModel::mark_at" | "SlotsModel::get"
            | "SlotsModel::get_mut" | "SlotsModel::put"
            | "SlotsModel::take" | "SlotsModel::resize" | "SlotsModel::put_m" | "SlotsModel::take_m"
            | "SlotsModel::resize_m" | "SlotsModel::resize_put_m" | "SlotsModel::move_m" | "SlotsModel::swap_m"
    )
}

/// What every extracted program starts with: the helpers the tables use.
const HELPERS: &str = "\
// Extracted by tauto: do not edit.\n\nfn extract_nat_sub(a: nat, b: nat): nat {\n  if a < b { 0 } else { a - b }\n}\n\nfn extract_float_checked_div(a: Float, b: Float): Option(Float) {\n  if b == 0.0 { None } else { Some(a / b) }\n}\n\nfn extract_float_is_infinite(x: Float): Bool {\n  Float::abs(x) > 1.7976931348623157e308\n}\n\nfn extract_float32_checked_div(a: Float32, b: Float32): Option(Float32) {\n  if b == Float32::of_float(0.0) { None } else { Some(a / b) }\n}\n\nfn extract_float32_is_infinite(x: Float32): Bool {\n  Float::abs(Float::of_float32(x)) > 1.7976931348623157e308\n}\n\nfn extract_i64_of_float_checked(x: Float): Option(i64) {\n  let t := Float::trunc(x)\n  if t >= -9223372036854775808.0 && t < 9223372036854775808.0 { Some(I64::of_float(t)) } else { None }\n}\n\nfn extract_nat_div(a: nat, b: nat): nat {\n  if b == 0 { 0 } else { div(a, b) }\n}\n\nfn extract_nat_mod(a: nat, b: nat): nat {\n  if b == 0 { a } else { mod(a, b) }\n}\n\nfn extract_nat_divmod(a: nat, b: nat, q: nat, r: nat): nat × nat {\n  if b == 0 || r >= b {\n    #(q, r + a)\n  } else {\n    #(q + div(r + a, b), mod(r + a, b))\n  }\n}\n\n// Never called: it stands for a match on a proof with no arms. Its\n// recursion is written as `div`, so the program is also a Tauto program.\nfn extract_unreachable<A: Linear>(): A ! {div} {\n  extract_unreachable()\n}\n";

/// The helpers of the `Text` functions, written when `std/text.taut` is
/// in the program.
const TEXT_HELPERS: &str = "\nfn extract_text_byte(t: Text, i: nat): Option(nat) {\n  match Text::byte(&t, U64::of_nat(i)) {\n    Some(b) => Some(Nat::of_u64(U64::of_u8(b)))\n    None => None\n  }\n}\n\n// `Text::all_bytes`: one loop over the bytes, counting down those left so
// that it ends.
fn extract_text_all_bytes_at(t: Text, i: u64, n: u64, p: (nat) -> Bool): Bool {\n  if n == 0 {\n    true\n  } else {\n    match Text::byte(&t, i) {\n      None => true\n      Some(c) => if p(Nat::of_u64(U64::of_u8(c))) {\n        extract_text_all_bytes_at(t, i + 1, n - 1, p)\n      } else {\n        false\n      }\n    }\n  }\n}

fn extract_text_all_bytes(t: Text, p: (nat) -> Bool): Bool {\n  extract_text_all_bytes_at(t, 0, Text::len(&t), p)\n}

fn extract_text_bytes_from(t: Text, i: u64, acc: List(nat)): List(nat) {\n  if i == 0 {\n    acc\n  } else {\n    match Text::byte(&t, i - 1) {\n      Some(b) => extract_text_bytes_from(t, i - 1, Cons(Nat::of_u64(U64::of_u8(b)), acc))\n      None => acc\n    }\n  }\n}\n\nfn extract_text_bytes(t: Text): List(nat) {\n  extract_text_bytes_from(t, Text::len(&t), Nil)\n}\n\nfn extract_text_push_all(b: &mut Buf, parts: List(Text)): () {\n  match parts {\n    Nil => ()\n    Cons(part, rest) => {\n      Buf::push(&mut b, &part)\n      extract_text_push_all(&mut b, rest)\n    }\n  }\n}\n\nfn extract_text_concat_all(parts: List(Text)): Text {\n  var b := Buf::new()\n  extract_text_push_all(&mut b, parts)\n  Text::of(b)\n}\n\nfn extract_ordering(c: i64): Ordering {\n  if c < 0 { Less } else if c == 0 { Equal } else { Greater }\n}\n\nfn extract_text_of_code_point(c: nat): Option(Text) {\n  if c > 1114111 {\n    None\n  } else {\n    Text::of_code_point(U32::of_u64(U64::of_nat(c)))\n  }\n}\n\nfn extract_text_utf8_of_code_point(c: nat): Text {\n  match extract_text_of_code_point(c) {\n    Some(t) => t\n    None => \"\"\n  }\n}\n\n// The bytes are read with tail calls, which run as a loop, so a long text\n// takes no stack: built in reverse, then turned around.\nfn extract_bytes_reverse_onto(bs: List(u8), acc: List(u8)): List(u8) {\n  match bs {\n    Nil => acc\n    Cons(b, rest) => extract_bytes_reverse_onto(rest, Cons(b, acc))\n  }\n}\n\nfn extract_bytes_of_onto(bs: List(nat), acc: List(u8)): Option(List(u8)) {\n  match bs {\n    Nil => Some(extract_bytes_reverse_onto(acc, Nil))\n    Cons(b, rest) => if b > 255 {\n      None\n    } else {\n      extract_bytes_of_onto(rest, Cons(U8::of_u64(U64::of_nat(b)), acc))\n    }\n  }\n}\n\nfn extract_bytes_of(bs: List(nat)): Option(List(u8)) {\n  extract_bytes_of_onto(bs, Nil)\n}\n\nfn extract_text_of_utf8(bs: List(nat)): Option(Text) {\n  match extract_bytes_of(bs) {\n    Some(r) => Text::of_utf8(r)\n    None => None\n  }\n}\n\n// `Text::Mk(bs)`. A `Text` at run time is well-formed UTF-8, so other bytes\n// have no value to stand for, and the program stops rather than go on\n// with a wrong one. It stops through a conversion that does not fit (Nib\n// has no other way to stop without an effect), so a function value that\n// builds a text stays pure.\nfn extract_text_of_bytes(bs: List(nat)): Text {\n  match extract_text_of_utf8(bs) {\n    Some(t) => t\n    None => Text::of_u64(U64::of_u8(U8::of_u64(256)))\n  }\n}\n";

/// `std/sint.taut`'s widths: the Nib type and the range check (`fits`) the
/// helpers call. Extraction keeps those same `fits`, so the name called and
/// the name kept come from this one table.
const SINT_WIDTHS: [(&str, &str); 4] = [
    ("i8", "SInt::fits8"),
    ("i16", "SInt::fits16"),
    ("i32", "SInt::fits32"),
    ("i64", "SInt::fits64"),
];

/// The helpers of `std/sint.taut`'s mapped functions, written when it is in
/// the program: a width's value as an `Int` and back. The range is
/// `std/sint.taut`'s own `SInt::fits32` / `SInt::fits64`, extracted with it, so
/// the program decides the range by the same definition the proofs use.
fn sint_helpers() -> String {
    let mut out = String::new();
    for ((ty, module), (to_i64, of_i64)) in SINT_WIDTHS
        .into_iter()
        .zip([
            ("I64::of_i8", "I8::of_i64"),
            ("I64::of_i16", "I16::of_i64"),
            ("I64::of_i32", "I32::of_i64"),
            ("", ""),
        ])
    {
        let _ = write!(
            out,
            "\nfn extract_{ty}_int(x: {ty}): Int {{\n  let y: i64 := {to_i64}(x)\n  if y >= 0 {{ IntOfNat(Nat::of_u64(U64::of_i64(y))) }} else {{ IntNegSucc(Nat::of_u64(U64::of_i64(-(y + 1)))) }}\n}}\n\nfn extract_{ty}_of_fitting(v: Int): {ty} {{\n  match v {{\n    IntOfNat(n) => {of_i64}(I64::of_u64(U64::of_nat(n)))\n    IntNegSucc(n) => {of_i64}(-I64::of_u64(U64::of_nat(n)) - 1)\n  }}\n}}\n\nfn extract_{ty}_of_decided(v: Int, o: Bool): Option({ty}) {{\n  if o {{ Some(extract_{ty}_of_fitting(v)) }} else {{ None }}\n}}\n\nfn extract_{ty}_of_int(v: Int): Option({ty}) {{\n  if {module}(v) {{ Some(extract_{ty}_of_fitting(v)) }} else {{ None }}\n}}\n"
        );
    }
    out
}

/// The helpers of `std/uint.taut`'s mapped functions, written when it is in
/// the program. The `u64` ones keep every value they compute at most
/// `2^63` (`h` is `2^63 - 1`), since Nib's literals stop at `i64`'s maximum.
fn uint_helpers() -> String {
    let mut out = String::new();
    for (ty, max, of_nat) in [
        ("u8", "255", "U8::of_u64"),
        ("u16", "65535", "U16::of_u64"),
        ("u32", "4294967295", "U32::of_u64"),
    ] {
        let _ = write!(
            out,
            "\nfn extract_{ty}_of_decided(n: nat, o: Bool): Option({ty}) {{\n  if o {{ Some({of_nat}(U64::of_nat(n))) }} else {{ None }}\n}}\n\nfn extract_{ty}_of_nat(n: nat): Option({ty}) {{\n  if n <= {max} {{ Some({of_nat}(U64::of_nat(n))) }} else {{ None }}\n}}\n\nfn extract_{ty}_checked_add(a: {ty}, b: {ty}): Option({ty}) {{\n  if a <= {max} - b {{ Some(a + b) }} else {{ None }}\n}}\n\nfn extract_{ty}_checked_sub(a: {ty}, b: {ty}): Option({ty}) {{\n  if b <= a {{ Some(a - b) }} else {{ None }}\n}}\n\nfn extract_{ty}_checked_mul(a: {ty}, b: {ty}): Option({ty}) {{\n  if b == 0 || a <= div({max}, b) {{ Some(a * b) }} else {{ None }}\n}}\n"
        );
    }
    // `2^w`, and a width's value as a `nat` and back modulo `2^w`. Nib's
    // literals stop at `i64`'s maximum, so `2^64` is computed.
    for (ty, modulus, to_u64, of_u64) in [
        ("u8", "256", "U64::of_u8", "U8::of_u64"),
        ("u16", "65536", "U64::of_u16", "U16::of_u64"),
        ("u32", "4294967296", "U64::of_u32", "U32::of_u64"),
        ("u64", "(Nat::of_u64(9223372036854775807) + 1) * 2", "", ""),
    ] {
        let _ = write!(
            out,
            "\nfn extract_{ty}_modulus(): nat {{\n  {modulus}\n}}\n\nfn extract_{ty}_nat(x: {ty}): nat {{\n  Nat::of_u64({to_u64}(x))\n}}\n\nfn extract_{ty}_wrap(n: nat): {ty} {{\n  {of_u64}(U64::of_nat(mod(n, extract_{ty}_modulus())))\n}}\n"
        );
    }
    out.push_str(
        "\nfn extract_u64_of_decided(n: nat, o: Bool): Option(u64) {\n  if o { Some(U64::of_nat(n)) } else { None }\n}\n\nfn extract_u64_of_nat(n: nat): Option(u64) {\n  if n <= 9223372036854775807 * 2 + 1 { Some(U64::of_nat(n)) } else { None }\n}\n\n// `a + b` fits when half of it, rounded down, is at most `2^63 - 1`.\nfn extract_u64_checked_add(a: u64, b: u64): Option(u64) {\n  let h: u64 := 9223372036854775807\n  let odd := if mod(a, 2) == 1 && mod(b, 2) == 1 { 1 } else { 0 }\n  if div(a, 2) + div(b, 2) + odd <= h { Some(a + b) } else { None }\n}\n\nfn extract_u64_checked_sub(a: u64, b: u64): Option(u64) {\n  if b <= a { Some(a - b) } else { None }\n}\n\n// `a * b` fits when `a` is at most `(2^64 - 1) div b`, which is\n// `2 (h div b) + (2 (h mod b) + 1) div b` for `2 <= b <= h`.\nfn extract_u64_checked_mul(a: u64, b: u64): Option(u64) {\n  let h: u64 := 9223372036854775807\n  if a <= 1 || b <= 1 {\n    Some(a * b)\n  } else if b > h {\n    None\n  } else if a <= 2 * div(h, b) + div(2 * mod(h, b) + 1, b) {\n    Some(a * b)\n  } else {\n    None\n  }\n}\n",
    );
    out
}

/// The path the extracted declarations are read from when the program runs.
/// It is a file of no tote: its names are the ones the check resolved, so
/// another file's declaration of a prelude name never takes one over.
pub(crate) const EXTRACTED_PATH: &str = "extracted.taut";

/// Display markers around extracted Nib. Text markers carry no checking evidence.
pub const EXTRACTED_BEGIN: &str = "// tauto:extracted\n";
pub const EXTRACTED_END: &str = "// tauto:extracted-end\n";

/// Checks the files and extracts what they define, in the order checked.
/// Fails on rejected declarations, axiom dependencies, unsupported forms or
/// incomplete declarations. Unproved instance laws and proofs incomplete only
/// because they use those laws are erased and do not prevent extraction.
pub fn extract_files(roots: &[PathBuf]) -> Result<String, String> {
    tauto_parse::install();
    extract_files_in(roots).map_err(|e| e.to_string())
}

fn extract_files_in(roots: &[PathBuf]) -> Result<String, Message> {
    let input = crate::read::check_files_for_extraction(roots, None, true, false)?;
    let (text, _, _) = extract_checked(&input, false, roots)?;
    let (loaded, _) = runtime::assemble(&input, &text, roots)?;
    write_source(&loaded)
}

pub(crate) struct Extracted {
    pub loaded: crate::program::Loaded,
    pub total: HashSet<Name>,
}

fn helpers_only(text: &str) -> bool {
    text == format!(
        "{EXTRACTED_BEGIN}{}\n{EXTRACTED_END}",
        crate::fmt::format(HELPERS).unwrap_or(HELPERS.into())
    )
}

/// Original declarations have passed visibility checking. Generated nominal
/// representations retain their private fields and constructors.
fn dependent_visibility(
    loaded: &crate::program::Loaded,
    protected: &HashSet<Name>,
) -> Vec<(tauto_message::Message, tauto_parol::Span)> {
    if protected.is_empty() {
        return Vec::new();
    }
    fn open(statement: &mut Stmt, protected: &HashSet<Name>) {
        use crate::surface::Vis;
        match statement {
            Stmt::Fn(f) if !protected.contains(&f.name) => f.vis = Vis::Pub,
            Stmt::Struct(d) | Stmt::Enum(d) if !protected.contains(&d.name) => d.vis = Vis::Open,
            Stmt::Inductive(i) if !protected.contains(&i.name) => i.vis = Vis::Open,
            Stmt::Theorem(t) | Stmt::Def(t) => t.vis = Vis::Pub,
            Stmt::Effect(e) if !protected.contains(&e.name) => e.vis = Vis::Open,
            Stmt::Class(c) => c.vis = Vis::Pub,
            Stmt::Module { items, .. } | Stmt::Mutual { items, .. } => {
                items.iter_mut().for_each(|s| open(s, protected))
            }
            _ => {}
        }
    }
    let mut files = loaded.kernel_files.clone();
    for statements in &mut files {
        statements.iter_mut().for_each(|s| open(s, protected));
    }
    let (mut errors, unsure) = crate::surface::qualify::sealed_visibility_typed(
        &files,
        &crate::program::module_names(&loaded.files),
    );
    errors.extend(crate::program::sealed_by_types(
        &loaded.program,
        loaded.bindings(),
        unsure,
    ));
    errors
}

pub(crate) fn extract_tote(roots: &[PathBuf]) -> Result<Extracted, String> {
    extract_tote_in(roots).map_err(|e| e.to_string())
}

pub(crate) fn extract_tote_in(roots: &[PathBuf]) -> Result<Extracted, Message> {
    let input = crate::read::check_files_for_extraction(roots, None, true, true)?;
    extract_of_input(&input, roots)
}

/// As [`extract_tote_in`], and first what every file the roots import, other
/// than the standard library's, declares: extracted as `tauto check` extracts
/// it ([`crate::program::load_extracted_input_with_imports`]) and given to
/// `refuse`, which says whether a program `check` rejects is read on. Only
/// what the roots reach is extracted for the program itself.
pub(crate) fn extract_tote_in_checking_imports(
    roots: &[PathBuf],
    refuse: impl FnOnce(Extracted) -> Result<(), Message>,
) -> Result<Extracted, Message> {
    extract_tote_in_checking_imports_exporting(roots, &[], &[], &[], refuse)
}

/// As [`extract_tote_in_checking_imports`], and the files that declare what
/// `exports` names are read as the roots are: an `exports` entry is a function's
/// name, or `TOTE::*` for the functions of a tote of `totes`. A function a
/// host calls is extracted whether or not the program runs it. `read` are
/// files read with the roots though nothing imports them: the sources of a
/// tote a `TOTE::*` names, which count as an import would.
pub(crate) fn extract_tote_in_checking_imports_exporting(
    roots: &[PathBuf],
    read: &[PathBuf],
    exports: &[String],
    totes: &[(String, PathBuf)],
    refuse: impl FnOnce(Extracted) -> Result<(), Message>,
) -> Result<Extracted, Message> {
    // The entry is read last, as a tote's entry is.
    let mut checked = read.to_vec();
    checked.extend(roots.iter().cloned());
    let input = crate::read::check_files_for_extraction(&checked, None, true, true)?;
    let mut roots = roots.to_vec();
    for (file, stmts) in &input.sources {
        let path = crate::program::canonical_path(&file.path);
        if roots.iter().any(|r| crate::program::canonical_path(r) == path)
            || crate::program::Standard::is_standard(file)
        {
            continue;
        }
        let tote = totes
            .iter()
            .filter(|(_, dir)| path.starts_with(dir))
            .max_by_key(|(_, dir)| dir.components().count())
            .map(|(name, _)| name.as_str());
        let declares = |s: &Stmt| match s {
            Stmt::Fn(f) => exports.iter().any(|e| match e.strip_suffix("::*") {
                Some(t) => tote == Some(t) && f.vis != crate::surface::Vis::Private,
                None => f.name.as_str() == e || f.name.as_str().ends_with(&format!("::{e}")),
            }),
            _ => false,
        };
        if stmts.iter().any(declares) {
            roots.push(file.path.clone());
        }
    }
    let roots = &roots[..];
    let own: HashSet<PathBuf> = roots
        .iter()
        .map(|r| crate::program::canonical_path(r))
        .collect();
    let mut all: Vec<PathBuf> = Vec::new();
    for f in &input.loaded.files {
        let path = crate::program::canonical_path(&f.path);
        if !crate::program::Standard::is_standard(f)
            && crate::program::is_source_file(&f.path)
            && !own.contains(&path)
            && !all.contains(&path)
        {
            all.push(path);
        }
    }
    if !all.is_empty() {
        all.extend(roots.iter().cloned());
        refuse(extract_of_input(&input, &all)?)?;
    }
    extract_of_input(&input, roots)
}

fn extract_of_input(
    input: &crate::read::ExtractionInput,
    roots: &[PathBuf],
) -> Result<Extracted, Message> {
    let (text, _, total) = extract_checked(input, true, roots)?;
    let (loaded, generated) = runtime::assemble(input, &text, roots)?;
    let mut total: HashSet<_> = total.into_iter().filter(Name::is_resolved).collect();
    total.extend(generated);
    Ok(Extracted { loaded, total })
}

/// The program a command runs: every file of `files` is read and checked,
/// and only what `main` reaches is extracted, as for the files an import
/// reads. The tote's own sources are the command's library: a declaration
/// of them that `main` does not use, such as a proof, is checked but not
/// extracted.
pub(crate) fn extract_command(files: &[PathBuf], main: &Path) -> Result<Extracted, Message> {
    let input = crate::read::check_files_for_extraction(files, None, true, true)?;
    let seeds = [main.to_path_buf()];
    let (text, _, total) = extract_checked(&input, true, &seeds)?;
    let (loaded, generated) = runtime::assemble(&input, &text, &seeds)?;
    let mut total: HashSet<_> = total.into_iter().filter(Name::is_resolved).collect();
    total.extend(generated);
    Ok(Extracted { loaded, total })
}

/// As [`extract_tote_in`] of `roots`, from the kernel's check of them that
/// has been made already ([`crate::read::check_files_for_extraction`]).
pub(crate) fn extract_input(
    input: crate::read::ExtractionInput,
    roots: &[PathBuf],
) -> Result<Extracted, Message> {
    let (text, _, total) = extract_checked(&input, true, roots)?;
    let (loaded, generated) = runtime::assemble(&input, &text, roots)?;
    let mut total: HashSet<_> = total.into_iter().filter(Name::is_resolved).collect();
    total.extend(generated);
    Ok(Extracted { loaded, total })
}

/// The program [`crate::program::load_tote_in`] reads from `roots`, extracted
/// from `input`, the kernel's check of those same roots.
pub(crate) fn extract_program(
    input: &crate::read::ExtractionInput,
    roots: &[PathBuf],
) -> Result<crate::program::Loaded, Message> {
    let (text, _, total) = extract_checked(input, true, roots)?;
    crate::phases::mark("extract_text");
    let (loaded, generated) = runtime::assemble(input, &text, roots)?;
    crate::phases::mark("extract_assemble");
    let mut total: HashSet<_> = total.into_iter().filter(Name::is_resolved).collect();
    total.extend(generated);
    crate::program::load_extracted_tote(Extracted { loaded, total })
}

/// The extraction of a loaded program as `tauto extract` prints it.
pub fn extracted_source(loaded: &crate::program::Loaded) -> Result<String, String> {
    tauto_parse::install();
    write_source(loaded).map_err(|e| e.to_string())
}

pub(crate) fn write_source(loaded: &crate::program::Loaded) -> Result<String, Message> {
    let statements = loaded
        .kernel_files
        .iter()
        .flatten()
        .cloned()
        .collect::<Vec<_>>();
    let mut file_modules = crate::program::module_names(&loaded.files);
    file_modules.sort_by_key(|m| std::cmp::Reverse(m.len()));
    file_modules.dedup();
    let text = source::write(&statements, &file_modules)?;
    Ok(format!("{EXTRACTED_BEGIN}{text}\n{EXTRACTED_END}"))
}

/// An axiom of `std/float.taut` that extraction maps onto a builtin of Nib
/// (`Float::exp`, `Text::of_float`, …): a function the proofs know nothing of,
/// trusted as the mapped functions are. `Quot::sound` is a proof and is
/// erased: a quotient is extracted as its representation, which a program
/// reads only through `Quot_lift`, giving related values the same result.
fn bound_kernel_prelude() -> Result<crate::surface::Program, Message> {
    let mut program = crate::check::kernel_prelude()?;
    crate::resolve::Resolver::new(crate::bindings::library_definition_bindings())
        .statements(&mut program.stmts);
    Ok(program)
}

/// Whether `i` takes universe levels first (`inductive UBox(u: Level, A: Type(u))`).
pub(crate) fn over_levels(i: &InductiveDecl) -> bool {
    i.params.first().is_some_and(
        |(_, t)| matches!(&*t.kind, TermKind::Var(n) if crate::bindings::is_library(n, "Level")),
    )
}

fn mapped_axiom(name: &str) -> bool {
    // The axiom is named under the module of its type (`Float::exp`,
    // `Text::of_float`), after the module of its file if any.
    name == crate::check::QUOT_SOUND
        || ["Float::", "Float32::", "Text::"].iter().any(|m| {
            let f = match name.rfind(&format!("::{m}")) {
                Some(i) => &name[i + 2..],
                None => name,
            };
            f.starts_with(m) && mapped_fn(f).is_some()
        })
}

/// The declarations of the proof language in `prefix` that the kernel
/// accepts without axioms, extracted as Nib source, for a macro to call
/// while the program is read: a macro's function is executable code, and the
/// files before it are not extracted yet. What the kernel does not accept,
/// or does not read (executable code), is left out, with what depends on it.
pub(crate) fn executable_prefix(
    prefix: &[Stmt],
    standard: &HashSet<Name>,
) -> Result<Vec<Stmt>, String> {
    // Every declaration of the prefix is checked here, and a tactic asks
    // for the same prefix at each of its steps: the answer is kept by what the
    // prefix is, its statements without places and binder numbers, and the
    // references its declarations are bound to.
    const KEPT: usize = 8;
    thread_local! {
        static KEPT_PREFIXES: std::cell::RefCell<Vec<(String, Result<Vec<Stmt>, String>)>> =
            const { std::cell::RefCell::new(Vec::new()) };
    }
    let mut key = String::new();
    let mut names: Vec<&str> = standard.iter().map(|n| n.as_str()).collect();
    names.sort();
    key.push_str(&names.join(","));
    for s in prefix {
        key.push('\n');
        key.push_str(&crate::check::fingerprint(s, false));
    }
    // The declarations it makes are bound to the references of this reading of
    // the files: one read again (the files before a later file, in a whole
    // project) is bound anew, and the library is compared with it by them.
    for n in tauto_surface::bindings::declared_names(prefix) {
        key.push('\n');
        key.push_str(&format!("{n:?}"));
    }
    let key = tauto_syntax::sha256_hex(key.as_bytes());
    if let Some(found) = KEPT_PREFIXES.with(|k| {
        k.borrow()
            .iter()
            .find(|(k, _)| *k == key)
            .map(|(_, r)| r.clone())
    }) {
        return found;
    }
    let made = executable_prefix_in(prefix, standard).map_err(|e| e.to_string());
    KEPT_PREFIXES.with(|k| {
        let mut k = k.borrow_mut();
        if k.len() >= KEPT {
            let _ = k.remove(0);
        }
        k.push((key, made.clone()));
    });
    made
}

/// The statements a macro library was last declared from, and the kernel and
/// what it said as they left them.
struct DeclaredPrefix {
    keys: Vec<String>,
    kernel: crate::check::Kernel,
    resolved: Vec<Stmt>,
    prelude_names: Vec<Name>,
    kept: Vec<Stmt>,
    out: Vec<crate::check::FileEntry>,
}

thread_local! {
    static LAST_PREFIX: std::cell::RefCell<Option<DeclaredPrefix>> =
        const { std::cell::RefCell::new(None) };
}

fn executable_prefix_in(prefix: &[Stmt], standard: &HashSet<Name>) -> Result<Vec<Stmt>, Message> {
    // The files before keep their `T::` names until the
    // whole program is read; the kernel takes their functions by full name.
    let mut flat = crate::surface::modules::resolve_joined_files(
        prefix.to_vec(),
        &crate::surface::effect_sets::Sets::new(),
        crate::program::prelude_module_names(),
    )
    .0;
    // A later file asks again with the same files before it and a few more
    // statements: the kernel as the last answer left it is taken again, and
    // only the statements after those are declared to it. A statement is the
    // same one when its text without places is, and the references of what it
    // declares: those of another reading of the files are other declarations.
    let keys: Vec<String> = flat
        .iter()
        .map(|s| {
            let mut key = crate::check::fingerprint(s, false);
            for n in tauto_surface::bindings::declared_names(std::slice::from_ref(s)) {
                key.push_str(&format!("\n{n:?}"));
            }
            key
        })
        .collect();
    let earlier = LAST_PREFIX.with(|l| {
        let l = l.borrow();
        l.as_ref()
            .filter(|p| p.keys.len() <= keys.len() && p.keys[..] == keys[..p.keys.len()])
            .map(|p| {
                (
                    p.keys.len(),
                    p.kernel.clone(),
                    p.resolved.clone(),
                    p.prelude_names.clone(),
                    p.kept.clone(),
                    p.out.clone(),
                )
            })
    });
    let (start, mut kernel, mut resolved, prelude_names, mut kept, mut out) = match earlier {
        Some((start, mut kernel, mut resolved, prelude_names, kept, out)) => {
            let mut rest = flat.split_off(start);
            kernel.resolve_statements(&mut rest);
            resolved.append(&mut rest);
            (start, kernel, resolved, prelude_names, kept, out)
        }
        None => {
            let mut kernel = crate::check::Kernel::new();
            let prelude_names = crate::check::declare_prelude(&mut kernel)?;
            kernel.resolve_statements(&mut flat);
            kernel.record_ctor_sites();
            // A theorem's proof decides nothing a macro runs: it is erased when the
            // library is extracted, and it is checked where the theorem is, in the
            // check of its own file. Only its statement is checked here; checking
            // every proof of the files before each file that calls a macro checked
            // them again for every such file.
            kernel.set_statement_only(true);
            (0, kernel, flat, prelude_names, Vec::new(), Vec::new())
        }
    };
    let path = PathBuf::from("macro library");
    // A function sees every other one of its file, so a declaration is read before the first
    // one that uses it, wherever it is written.
    let order = tauto_kernel::check::dependency_positions(&resolved[start..]);
    for s in order.into_iter().map(|i| &resolved[start + i]) {
        // A struct or enum is declared to the kernel as the family it reads as, as the
        // files of a program are: stated as written, it declares nothing, and each function
        // that mentions it fails with the family's name.
        let as_written = matches!(s, Stmt::Struct(_) | Stmt::Enum(_));
        let s = &match s {
            Stmt::Struct(d) => Stmt::Inductive(tauto_kernel::check::program_family(d, true)),
            Stmt::Enum(d) => Stmt::Inductive(tauto_kernel::check::program_family(d, false)),
            s => s.clone(),
        };
        let entries = kernel.declare_program(&crate::surface::Program {
            stmts: vec![s.clone()],
            errors: Vec::new(),
        });
        let accepted = !entries.is_empty()
            && entries
                .iter()
                .all(|e| matches!(&e.verdict, Verdict::Checked { axioms } if axioms.is_empty()));
        let proof_language = matches!(
            s,
            Stmt::Inductive(_)
                | Stmt::Fn(_)
                | Stmt::Theorem(_)
                | Stmt::Def(_)
                | Stmt::Class(_)
                | Stmt::Instance(_)
                | Stmt::Mutual { .. }
        );
        // A function of `std/` that extraction maps onto Nib (`Bool.or` is
        // `||`), or that Nib's prelude has (`Nat.max`), is not written: the
        // name would be declared twice.
        let mapped = matches!(
            s,
            Stmt::Fn(f) if (mapped_fn(crate::surface::qualify::short(&f.name)).is_some() || nib_prelude_fn(crate::surface::qualify::short(&f.name)))
                && standard.contains(&f.name)
        );
        // The data a program declares runs as it is written (the family the kernel was given
        // is what it reads of it): extracted, its owning a slots type would make it a type
        // that a `var` may not hold.
        if accepted && proof_language && !mapped && !as_written {
            kept.push(s.clone());
        }
        out.extend(entries.into_iter().map(|entry| crate::check::FileEntry {
            file: path.clone(),
            entry,
        }));
    }
    LAST_PREFIX.with(|l| {
        *l.borrow_mut() = Some(DeclaredPrefix {
            keys,
            kernel: kernel.clone(),
            resolved: resolved.clone(),
            prelude_names: prelude_names.clone(),
            kept: kept.clone(),
            out: out.clone(),
        })
    });
    let prefix = resolved.as_slice();
    let checked = crate::check::checked_entries(kernel, vec![path.clone()], out, prelude_names);
    selected_references(&checked, &mut kept)?;
    let mut own = HashSet::new();
    let mut std = HashSet::new();
    for n in tauto_surface::bindings::declared_names(prefix) {
        if standard.contains(n) {
            std.insert(n.clone());
        } else {
            own.insert(n.clone());
        }
    }
    let mut std_names = StdNames::new(&[]);
    std_names.own = own;
    std_names.std = std;
    let mut ex = Extractor {
        dependent: None,
        app_id: None,
        lent_locals: std::cell::RefCell::new(HashSet::new()),
        checked: &checked,
        linear_data: linear_data(prefix),
        field_selections: None,
        generated: HashSet::new(),
        out: String::from(HELPERS),
        fresh: 0,
        mixed: false,
        needed: HashSet::new(),
        dependencies: HashSet::new(),
        runtime: Vec::new(),
        total: HashSet::new(),
        thunks: HashSet::new(),
        std: &std_names,
        written: HashSet::new(),
        pending: Vec::new(),
        unused: HashSet::new(),
        aliases: std::rc::Rc::new(type_aliases(&checked, &kept)),
        proof_takers: HashSet::new(),
        refined_takers: HashSet::new(),
        module_segments: module_segments(&checked, &[]),
        file_modules: std::rc::Rc::new(Vec::new()),
        module_locals: HashMap::new(),
        writers: HashSet::new(),
    };
    if checked
        .families
        .keys()
        .any(|n| std_names.of(n) == Some("Text"))
    {
        ex.out.push_str(TEXT_HELPERS);
    }
    if checked
        .families
        .keys()
        .any(|n| std_names.of(n) == Some("UInt"))
    {
        ex.out.push_str(&uint_helpers());
    }
    if checked
        .families
        .keys()
        .any(|n| std_names.of(n) == Some("SInt"))
    {
        ex.out.push_str(&sint_helpers());
    }
    runtime::prefix(&kept, prefix, &ex, &ex.out)
}

/// `text` with an `import std::prelude::<file>` for each non-core prelude file
/// that declares a name the program refers to (`Buf`, `Vec`, `Array`,
/// `Shared`, ...): the extracted program is one file, and sees only the core
/// prelude without them. The names are those of the parsed program (terms,
/// types, patterns, effect rows, bounds and `where` classes), looked up in
/// `hidden_prelude`; a name the program declares itself is its own. The
/// imports come first.
fn with_prelude_imports(text: &str, own: &HashSet<String>) -> String {
    let Ok(mut program) = tauto_parse::parse_program_unresolved_at(text, 0) else {
        return text.to_string();
    };
    let hidden = crate::surface::qualify::hidden_prelude();
    let mut files: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
    // A name `A::b::c`, then each prefix of it.
    let mut note = |path: &str| {
        let mut name = path;
        loop {
            if own.contains(name) {
                return;
            }
            if let Some(fs) = hidden.get(name) {
                files.extend(fs.iter().map(String::as_str));
                return;
            }
            match name.rfind("::") {
                Some(i) => name = &name[..i],
                None => return,
            }
        }
    };
    fn pattern(p: &Pattern, note: &mut dyn FnMut(&str)) {
        match p {
            Pattern::Ctor { name, args } => {
                note(name);
                args.iter().for_each(|a| pattern(a, note));
            }
            Pattern::Record { name, fields } => {
                note(name);
                fields.iter().for_each(|(_, a)| pattern(a, note));
            }
            _ => {}
        }
    }
    fn decl(d: &FnDecl, note: &mut dyn FnMut(&str)) {
        d.bounds.iter().flatten().for_each(|b| note(b));
        d.effects.iter().flatten().for_each(|e| note(e));
        d.where_.iter().for_each(|c| note(&c.class));
    }
    fn declarations(s: &Stmt, note: &mut dyn FnMut(&str)) {
        match s {
            Stmt::Fn(d) => decl(d, note),
            Stmt::Instance(i) => {
                note(&i.class);
                i.bounds.iter().flatten().for_each(|b| note(b));
                i.where_.iter().for_each(|c| note(&c.class));
                i.methods.iter().for_each(|d| decl(d, note));
            }
            Stmt::Class(c) => c.methods.iter().for_each(|d| decl(d, note)),
            Stmt::Extern { fns, .. } => fns.iter().for_each(|d| decl(d, note)),
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                items.iter().for_each(|i| declarations(i, note))
            }
            Stmt::Attributed { stmt, .. } => declarations(stmt, note),
            _ => {}
        }
    }
    for s in &mut program.stmts {
        declarations(s, &mut note);
        crate::surface::walk::stmt(s, &mut |t| match &*t.kind {
            TermKind::Var(n) => note(n),
            TermKind::Field { .. } => {
                if let Some(path) = dotted(t) {
                    note(&path);
                }
            }
            TermKind::Row(es) => es.iter().for_each(|e| note(e)),
            TermKind::Pi {
                effects: Some(es), ..
            } => es.iter().for_each(|e| note(e)),
            TermKind::Perform { effect, .. } => note(effect),
            TermKind::Record { name, .. } => note(name),
            TermKind::Match { arms, .. } => {
                arms.iter().for_each(|a| pattern(&a.pattern, &mut note))
            }
            TermKind::Block(stmts) => stmts.iter().for_each(|s| declarations(s, &mut note)),
            _ => {}
        });
    }
    let mut out = String::new();
    for f in files {
        let _ = writeln!(out, "import std::builtin::{f}");
    }
    out.push_str(text);
    out
}

/// The `struct`s and `enum`s that `stmts` declare `linear`.
pub(super) fn linear_data<'s>(stmts: impl IntoIterator<Item = &'s Stmt>) -> HashSet<Name> {
    fn go(s: &Stmt, out: &mut HashSet<Name>) {
        match s {
            Stmt::Struct(d) | Stmt::Enum(d)
                if tauto_surface::inductive_data::written_kind(d) == Some("linear") =>
            {
                out.insert(d.name.clone());
            }
            Stmt::Mutual { items, .. } => items.iter().for_each(|s| go(s, out)),
            Stmt::Attributed { stmt, .. } => go(stmt, out),
            _ => {}
        }
    }
    let mut out = HashSet::new();
    stmts.into_iter().for_each(|s| go(s, &mut out));
    out
}

fn extract_checked(
    input: &crate::read::ExtractionInput,
    mixed: bool,
    roots: &[PathBuf],
) -> Result<(String, Vec<(PathBuf, String)>, HashSet<Name>), Message> {
    let checked = &input.checked;
    let mut problems = Vec::new();
    let unproved = unproved_laws(&checked);
    let generated = generated_nib_names(input);
    let read_time = registered_functions(input, roots);
    crate::phases::mark("extract_prepare");
    let unused = unused_imported(input, roots, &read_time);
    crate::phases::mark("extract_unused");
    for e in &checked.entries {
        match &e.entry.verdict {
            // What `inductive_syntax!` makes for Nib (the tree `<syntax>.parse` reads, the reader and
            // `<syntax>.<Type>.to_i`) is written out as Nib, not extracted.
            Verdict::Skipped(_) if generated.contains(&e.entry.name) => {}
            // A function with effects the kernel does not read runs as written.
            // One the kernel read and rejected is an error like any other.
            Verdict::Skipped(_) if mixed && checked.runtime.contains(&e.entry.name) => {}
            // An imported function nothing extracted reaches, such as one a
            // macro runs while the program is read, is not written out.
            Verdict::Skipped(_) if unused.contains(&e.entry.name) => {}
            // A law an instance does not prove leaves its record of laws
            // incomplete, and the proofs that use it; they are erased, and
            // the program still runs.
            Verdict::Incomplete { .. } if !mixed && unproved.contains(&e.entry.name) => {}
            Verdict::Checked { axioms } if !axioms.iter().all(|a| mapped_axiom(a)) => problems
                .push(located(
                    crate::read::declaration_place(&input.loaded, &e.file, &e.entry.name)
                        .unwrap_or_else(|| e.file.display().to_string()),
                    msg!(
                        "tauto-extract-uses-axioms",
                        name = e.entry.name.to_string(),
                        axioms = axioms
                            .iter()
                            .map(Name::as_str)
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                )),
            // An imported theorem or def that extraction does not reach (proofs
            // are erased) may fail because it names a skipped executable; that
            // does not stop extracting the named program.
            Verdict::Failed(_) if unused.contains(&e.entry.name) => {}
            Verdict::Failed(d) => {
                // `file:line:col:`, as a type error from the run says where it is.
                let place = d
                    .span
                    .and_then(|sp| {
                        let text = std::fs::read_to_string(&e.file).ok()?;
                        let (l, c) = crate::report::line_col(&text, sp.start as usize);
                        Some(format!("{}:{l}:{c}", e.file.display()))
                    })
                    .unwrap_or_else(|| e.file.display().to_string());
                problems.push(located(
                    place,
                    msg!(
                        "tauto-extract-failed",
                        name = e.entry.name.to_string(),
                        why = d.message.clone()
                    ),
                ))
            }
            Verdict::Incomplete { .. } => problems.push(located(
                crate::read::declaration_place(&input.loaded, &e.file, &e.entry.name)
                    .unwrap_or_else(|| e.file.display().to_string()),
                msg!("tauto-extract-incomplete", name = e.entry.name.to_string()),
            )),
            Verdict::Skipped(why) => problems.push(located(
                crate::read::declaration_place(&input.loaded, &e.file, &e.entry.name)
                    .unwrap_or_else(|| e.file.display().to_string()),
                msg!(
                    "tauto-extract-skipped",
                    name = e.entry.name.to_string(),
                    why = why.clone()
                ),
            )),
            Verdict::Checked { .. } => {}
        }
    }
    if !problems.is_empty() {
        return Err(joined(problems));
    }
    crate::phases::mark("extract_verdicts");
    let std = StdNames::new(&input.sources);
    let lowered = dependent::lower(input, roots, &std)?;
    crate::phases::mark("extract_lower");
    let file_modules = file_modules_of(input);
    let mut ex = Extractor {
        dependent: None,
        app_id: None,
        lent_locals: std::cell::RefCell::new(HashSet::new()),
        checked: &checked,
        linear_data: linear_data(input.sources.iter().flat_map(|(_, s)| s)),
        field_selections: None,
        generated: generated.clone(),
        out: String::from(HELPERS),
        fresh: 0,
        mixed,
        needed: if mixed {
            reachable_once(input, roots, &read_time)?
        } else {
            HashSet::new()
        },
        dependencies: HashSet::new(),
        runtime: Vec::new(),
        total: HashSet::new(),
        thunks: HashSet::new(),
        std: &std,
        written: HashSet::new(),
        pending: Vec::new(),
        unused,
        aliases: std::rc::Rc::new(type_aliases(
            checked,
            input.sources.iter().flat_map(|(_, s)| s),
        )),
        proof_takers: HashSet::new(),
        refined_takers: HashSet::new(),
        module_segments: module_segments(&checked, &file_modules),
        file_modules: file_modules.clone(),
        module_locals: HashMap::new(),
        writers: HashSet::new(),
    };
    crate::phases::mark("extract_reachable");
    if checked.families.keys().any(|n| std.of(n) == Some("Text")) {
        ex.out.push_str(TEXT_HELPERS);
    }
    if checked.families.keys().any(|n| std.of(n) == Some("UInt")) {
        ex.out.push_str(&uint_helpers());
    }
    if checked.families.keys().any(|n| std.of(n) == Some("SInt")) {
        ex.out.push_str(&sint_helpers());
    }
    if let Some(lowered) = lowered {
        ex.out.push_str(&lowered.text);
        ex.total.extend(lowered.total.iter().cloned());
        ex.written.extend(lowered.exports.iter().cloned());
        ex.needed.extend(lowered.functions.iter().cloned());
        ex.refined_takers
            .extend(lowered.functions.difference(&lowered.exports).cloned());
        for name in &lowered.functions {
            if let Some(sig) = checked.signatures.get(name) {
                let arity = checked
                    .arities
                    .get(name)
                    .copied()
                    .unwrap_or(sig.params.len());
                if sig
                    .params
                    .get(sig.implicit..arity)
                    .is_some_and(|params| params.contains(&Role::Proof))
                {
                    ex.proof_takers.insert(name.clone());
                }
            }
        }
        for family in &lowered.families {
            if let Some(f) = checked.families.get(family) {
                ex.refined_takers.extend(f.ctors.iter().cloned());
                ex.refined_takers.insert(family.clone());
            }
        }
        ex.dependent = Some(lowered);
    }
    for (file, stmts) in &input.sources {
        ex.file(file, stmts)?;
    }
    if mixed {
        ex.kernel_functions()?;
        ex.runtime_files(&input.runtime_reasons)?;
    }
    let (out, _) = legal_names(&ex.out);
    let out = with_prelude_imports(&out, &ex.std.own.iter().map(ToString::to_string).collect());
    let total = ex.total;
    // Laid out as `tauto fmt` would, for whoever reads `tauto extract`.
    let text = crate::fmt::format(&out).unwrap_or(out);
    Ok((
        format!("{EXTRACTED_BEGIN}{text}\n{EXTRACTED_END}"),
        ex.runtime,
        total,
    ))
}

/// `text` with each name a macro expansion made hygienic (`x#3`, `x#r3`),
/// which no source can spell, written as a name that can be read back
/// (`x_3`, or another number when that is taken), and those renamings.
/// Each such name is unique, so a fresh name for each keeps what refers to what.
/// A local as an expression. A name spelled like a reserved word is written `r#name`. A name that
/// is a keyword only by what follows it (`if label {`) is written in parentheses, which the
/// keyword never is followed by.
fn local_name(n: &str) -> String {
    const CONTEXTUAL: &[&str] = &["as", "syntax"];
    if crate::surface::print::RESERVED.contains(&n) {
        raw(n)
    } else if CONTEXTUAL.contains(&n) {
        format!("({n})")
    } else {
        n.to_string()
    }
}

fn dotted(t: &crate::surface::SurfaceTerm) -> Option<String> {
    match &*t.kind {
        TermKind::Var(n) => Some(n.to_string()),
        TermKind::Field { base, name } => Some(format!("{}::{name}", dotted(base)?)),
        _ => None,
    }
}

fn legal_names(text: &str) -> (String, HashMap<String, String>) {
    let ident = tauto_parol::unicode::is_ident_continue;
    let mut words: Vec<(bool, &str)> = Vec::new();
    let mut rest = text;
    while let Some(c) = rest.chars().next() {
        let len = if c == '"' {
            let mut escaped = false;
            rest[1..]
                .char_indices()
                .find(|&(_, c)| {
                    let end = c == '"' && !escaped;
                    escaped = c == '\\' && !escaped;
                    end
                })
                .map_or(rest.len(), |(i, _)| i + 2)
        } else if rest.starts_with("//") {
            rest.find('\n').unwrap_or(rest.len())
        } else if ident(c) {
            let mut end = rest.find(|c| !ident(c)).unwrap_or(rest.len());
            // Dictionary and instance names (`inst@C`, `C::m@Head@instance21`)
            // use `@` as a mark; Nib's `@` starts a tag, so the whole spelling
            // is one hygienic name rewritten below.
            while let Some(after) = rest[end..].strip_prefix('@') {
                let mark = after.find(|c| !ident(c)).unwrap_or(after.len());
                if mark == 0 {
                    break;
                }
                end = rest.len() - after.len() + mark;
            }
            if let Some(after) = rest[end..].strip_prefix('#') {
                let digits = after.strip_prefix('r').unwrap_or(after);
                let n = digits
                    .find(|c: char| !c.is_ascii_digit())
                    .unwrap_or(digits.len());
                if n > 0 {
                    end = rest.len() - digits.len() + n;
                    words.push((true, &rest[..end]));
                    rest = &rest[end..];
                    continue;
                }
            }
            if rest[..end].contains('@') {
                words.push((true, &rest[..end]));
                rest = &rest[end..];
                continue;
            }
            end
        } else {
            c.len_utf8()
        };
        words.push((false, &rest[..len]));
        rest = &rest[len..];
    }
    let mut taken: HashSet<String> = words
        .iter()
        .filter(|(h, w)| !h && w.starts_with(ident))
        .map(|(_, w)| w.to_string())
        .collect();
    let mut renamed: HashMap<String, String> = HashMap::new();
    let mut out = String::with_capacity(text.len());
    for (hygienic, w) in words {
        if !hygienic {
            out.push_str(w);
            continue;
        }
        if !renamed.contains_key(w) {
            let plain = w
                .find('#')
                .map(|i| &w[..i])
                .unwrap_or(w)
                .replace('@', "_");
            let name = (1..)
                .map(|k| format!("{plain}_{k}"))
                .find(|n| !taken.contains(n))
                .unwrap_or_default();
            taken.insert(name.clone());
            renamed.insert(w.to_string(), name);
        }
        out.push_str(&renamed[w]);
    }
    (out, renamed)
}

/// The declarations that are incomplete only for laws that were not written:
/// those with such holes, and what uses only those.
fn unproved_laws(checked: &Checked) -> HashSet<Name> {
    let mut out: HashSet<Name> = HashSet::new();
    loop {
        let before = out.len();
        for e in &checked.entries {
            if let Verdict::Incomplete { holes, uses } = &e.entry.verdict
                && holes.iter().all(|h| h.name.starts_with("law:"))
                && uses.iter().all(|u| out.contains(u))
            {
                out.insert(e.entry.name.clone());
            }
        }
        if out.len() == before {
            return out;
        }
    }
}

/// A `def` as the function it is when executable code calls it: its
/// generics stay generics, its other parameters and its type become the
/// function's, and its body is checked as the function's would be. Its
/// signature in the kernel (`Checked::signatures`) covers the generics and
/// the parameters alike, as a function's does.
fn def_as_fn(t: &crate::surface::TheoremDecl) -> Option<FnDecl> {
    let body = t.body.clone()?;
    let (generics, params) = t.params.split_at(t.implicit.min(t.params.len()));
    Some(FnDecl {
        lends: None,
        budget: None,
        vis: Default::default(),
        name: t.name.clone(),
        generic_types: Vec::new(),
        generics: Vec::new(),
        rows: Vec::new(),
        bounds: Vec::new(),
        bound_spans: Vec::new(),
        params: generics
            .iter()
            .chain(params)
            .map(|(n, _)| n.clone())
            .collect(),
        borrows: vec![None; t.params.len()],
        param_types: t.params.iter().map(|(_, ty)| Some(ty.clone())).collect(),
        result: Some(t.ty.clone()),
        effects: None,
        written_effects: None,
        row_hole: None,
        where_: Vec::new(),
        span: t.span,
        opaque: false,
        ghost: false,
        decreasing_by: None,
        generates: None,
        body,
        unused: None,
        unused_generics: Vec::new(),
        unused_params: Vec::new(),
    })
}

fn executable(s: &Stmt, runtime: &HashSet<Name>) -> bool {
    match s {
        Stmt::Fn(f) => runtime.contains(&f.name),
        Stmt::Effect(e) => runtime.contains(&e.name),
        // An `inductive enum` the kernel reads is extracted with the
        // functions over it, which name its constructors.
        Stmt::Enum(d) => runtime.contains(&d.name),
        // A class whose methods have effects the proofs do not read runs as
        // written, with its instances.
        Stmt::Class(c) => runtime.contains(&c.name),
        Stmt::Instance(i) => runtime.contains(&i.class),
        Stmt::Inductive(_)
        | Stmt::Theorem(_)
        | Stmt::Def(_)
        | Stmt::Import { .. }
        | Stmt::Mutual { .. } => false,
        _ => true,
    }
}

/// What the executable code needs to know of the constructors of the
/// proofs: the struct a constructor builds, if it builds one, and whether a
/// name is a constructor.
struct Ctors<'a> {
    struct_of: &'a dyn Fn(&Name) -> Option<Name>,
    struct_fields: &'a dyn Fn(&Name) -> Option<(Name, Vec<Name>)>,
    is_ctor: &'a dyn Fn(&Name) -> bool,
    /// The path of a variant that kept its short name inside a type written
    /// out in modules ([`Extractor::qualified_ctor`]).
    qualified: &'a dyn Fn(&Name) -> Option<String>,
}

/// Where each argument of `parent` is written: its own span, or for an argument a macro made the
/// macro call that was written in its place. `None` when that cannot be told, and the call is
/// then not rewritten, since a span of an expansion is no place in the written text.
fn written_arguments(
    parent: tauto_parol::Span,
    arguments: &[SurfaceTerm],
    calls: &[tauto_parol::Span],
) -> Option<Vec<tauto_parol::Span>> {
    let made = |a: &SurfaceTerm| a.span.start >= crate::macros::EXPANSION_BASE;
    if !arguments.iter().any(made) {
        return Some(arguments.iter().map(|a| a.span).collect());
    }
    if parent.start >= crate::macros::EXPANSION_BASE {
        return None;
    }
    let own: Vec<tauto_parol::Span> = arguments
        .iter()
        .filter(|a| !made(a))
        .map(|a| a.span)
        .collect();
    let mut found = calls.iter().filter(|c| {
        parent.start <= c.start
            && c.end <= parent.end
            && !own.iter().any(|o| o.start <= c.start && c.end <= o.end)
    });
    let mut out = Vec::new();
    for a in arguments {
        out.push(if made(a) { *found.next()? } else { a.span });
    }
    found.next().is_none().then_some(out)
}

fn runtime_source(
    text: &str,
    base: u32,
    stmts: &[Stmt],
    runtime: &HashSet<Name>,
    std: &StdNames,
    written: &HashSet<Name>,
    called: &HashSet<String>,
    ctors: Ctors,
) -> String {
    let Ctors {
        struct_of,
        struct_fields,
        is_ctor,
        qualified,
    } = ctors;
    fn range(span: tauto_parol::Span, base: u32) -> std::ops::Range<usize> {
        span.start.saturating_sub(base) as usize..span.end.saturating_sub(base) as usize
    }
    /// `f` on each term of `s` that the source writes. A term the `for`
    /// expansion made borrows the span of the loop it replaced, so rewriting
    /// the text at that span would rewrite the loop's own text.
    fn walk_written(s: &mut Stmt, f: &mut dyn FnMut(&mut SurfaceTerm)) {
        crate::surface::walk::stmt(s, &mut |t| {
            if !t.is_lowered() {
                f(t)
            }
        });
    }
    fn blank(bytes: &mut [u8], span: tauto_parol::Span, base: u32) {
        let Some(bytes) = bytes.get_mut(range(span, base)) else {
            return;
        };
        for b in bytes {
            if *b != b'\n' && *b != b'\r' {
                *b = b' ';
            }
        }
    }
    fn erase(
        bytes: &mut [u8],
        original: &[u8],
        base: u32,
        stmts: &[Stmt],
        runtime: &HashSet<Name>,
        macro_fns: &HashSet<String>,
        swapped: &dyn Fn(&Stmt) -> bool,
    ) {
        for s in stmts {
            if executable(s, runtime) {
                // What the host's reference stands for is not written.
                if swapped(s) {
                    match s {
                        Stmt::Instance(i) => blank(bytes, i.span, base),
                        Stmt::Struct(d) => blank(bytes, d.span, base),
                        _ => {}
                    }
                }
                continue;
            }
            let span = match s {
                Stmt::Fn(f) if macro_fns.contains(f.name.as_str()) => continue,
                Stmt::Fn(f) => f.span,
                // An effect the proofs read is declared once, where it is
                // extracted, so that the code that runs handles that effect.
                Stmt::Effect(e) => e.span,
                Stmt::Theorem(t) | Stmt::Def(t) => t.span,
                Stmt::Inductive(i) => i.span,
                Stmt::Enum(d) => d.span,
                // An import is kept: what the file's names mean when it runs
                // is what its imports made them mean when it was checked.
                Stmt::Import { .. } => continue,
                Stmt::Class(c) => c.span,
                Stmt::Instance(i) => i.span,
                Stmt::Mutual { items, span } => {
                    blank(bytes, *span, base);
                    for item in items {
                        if let Stmt::Fn(f) = item
                            && runtime.contains(&f.name)
                        {
                            let r = range(f.span, base);
                            if let (Some(to), Some(from)) =
                                (bytes.get_mut(r.clone()), original.get(r))
                            {
                                to.copy_from_slice(from);
                            }
                        }
                    }
                    continue;
                }
                _ => continue,
            };
            blank(bytes, span, base);
        }
    }
    let mut bytes = text.as_bytes().to_vec();
    // An import is kept: the file is read again to run with the imports it
    // was checked with, so that its names mean what they meant then. A
    // macro call that makes statements is erased: what it made is in the
    // expanded statements, and calling it again would declare it twice.
    // The function of a `macro fn` whose macro an expression still calls is kept
    // as written: the program read again to run registers the macro from it and
    // expands those calls.
    let mut macro_fns: HashSet<String> = HashSet::new();
    let mut syntaxes = Vec::new();
    if let Ok(written) = tauto_parse::parse_program_unresolved_at(text, base) {
        for stmt in &written.stmts {
            match stmt {
                Stmt::Syntax {
                    inductive: false,
                    span,
                    ..
                } => syntaxes.push(*span),
                Stmt::Macro { name, function, .. } if called.contains(name) => {
                    macro_fns.insert(function.clone());
                }
                // A `macro fn` no expression calls is erased with its keyword:
                // erasing only the function would leave `macro` alone.
                Stmt::Macro { function, span, .. }
                    if !runtime.iter().any(|name| name.as_str() == function) =>
                {
                    blank(&mut bytes, *span, base)
                }
                Stmt::Called { span, .. } => blank(&mut bytes, *span, base),
                Stmt::Attributed { stmt, span, .. } => {
                    // The declaration an attribute is given stays as written
                    // when the macro kept it; the attribute is erased.
                    blank(&mut bytes, *span, base);
                    let mut stmt = &**stmt;
                    while let Stmt::Attributed { stmt: inner, .. } = stmt {
                        stmt = inner;
                    }
                    if let Some(d) = stmt_span(stmt) {
                        blank(
                            &mut bytes,
                            tauto_parol::Span::new(span.start, d.start),
                            base,
                        );
                        if !stmts.iter().any(|s| stmt_span(s) == Some(d)) {
                            blank(&mut bytes, d, base);
                        }
                    }
                }
                _ => {}
            }
        }
    }
    erase(
        &mut bytes,
        text.as_bytes(),
        base,
        stmts,
        runtime,
        &macro_fns,
        &|s| lend_of_mapped(s, std),
    );
    // A native syntax and its generated parser share a source span. Erasing
    // an unused parser must not erase the grammar that declares its input types.
    for span in syntaxes {
        let r = range(span, base);
        if let (Some(to), Some(from)) = (bytes.get_mut(r.clone()), text.as_bytes().get(r)) {
            to.copy_from_slice(from);
        }
    }
    // An `include_text!` (or `include_bytes!`) that is kept is written as the literal it was read
    // as: the source is read again without the file it was in. The literal
    // has no line break, so the lines after it stay where they were.
    // The macro calls written in this file, outermost first in text order: an
    // argument a macro made has no text of its own, and stands where the call
    // that made it was written.
    let calls: Vec<tauto_parol::Span> = {
        let mut all = Vec::new();
        if let Ok(written) = tauto_parse::parse_program_unresolved_at(text, base) {
            for mut s in written.stmts {
                crate::surface::walk::stmt(&mut s, &mut |t| {
                    if matches!(&*t.kind, TermKind::MacroCall { .. }) {
                        all.push(t.span);
                    }
                });
            }
        }
        all.sort_by_key(|g| (g.start, std::cmp::Reverse(g.end)));
        let mut outer: Vec<tauto_parol::Span> = Vec::new();
        for g in all {
            if outer.last().is_none_or(|o| g.start >= o.end) {
                outer.push(g);
            }
        }
        outer
    };
    let mut included: Vec<(tauto_parol::Span, String)> = Vec::new();
    let mut kept: Vec<Stmt> = Vec::new();
    for s in stmts {
        match s {
            Stmt::Mutual { items, .. } => kept.extend(
                items
                    .iter()
                    .filter(|i| matches!(i, Stmt::Fn(f) if runtime.contains(&f.name)))
                    .cloned(),
            ),
            s if executable(s, runtime) => kept.push(s.clone()),
            _ => {}
        }
    }
    // What a macro made has no text of its own here: it is printed after
    // the written source, so that the lines before it stay where they were.
    let (made, mut kept): (Vec<Stmt>, Vec<Stmt>) = kept.into_iter().partition(made_by_macro);
    for s in &mut kept {
        walk_written(s, &mut |t| {
            if let TermKind::Text(value) = &*t.kind
                && text
                    .get(range(t.span, base))
                    .is_some_and(|w| w.starts_with(crate::program::include::NAME))
            {
                included.push((t.span, crate::surface::print::quoted(value)));
            }
            // An `include_bytes!` is the `Bytes::of_list([…])` it was read as.
            if let TermKind::App { function, .. } = &*t.kind
                && matches!(&*function.kind, TermKind::Var(n) if crate::bindings::is_library(n, "Bytes::of_list"))
                && text
                    .get(range(t.span, base))
                    .is_some_and(|w| w.starts_with(crate::program::include::BYTES))
            {
                included.push((t.span, crate::surface::print::print_term(t)));
            }
        });
    }
    // The families and constructors of `std/` that extraction maps onto Nib
    // are written as Nib writes them in the executable code too (`Succ(n)`
    // as `(n + 1)`, `Nat` as `nat`), so that it can call what was extracted.
    for s in &mut kept {
        walk_written(s, &mut |t| match &*t.kind {
            TermKind::Var(n) if !runtime.contains(n) && std.of(n).is_some() => {
                let mapped = match std.of(n).unwrap_or(n) {
                    m @ ("Zero" | "true" | "false" | "Star") => mapped_ctor(m, &[]),
                    m @ ("Nat" | "Bool" | "Unit" | "Stack") => mapped_type(m).map(str::to_string),
                    _ => None,
                };
                if let Some(m) = mapped {
                    included.push((t.span, m));
                }
            }
            // A constructor without arguments is a value of Nib, not a
            // function: `hi()` as `hi`, as extraction writes it.
            TermKind::App {
                function,
                arguments,
            } if arguments.is_empty()
                && matches!(&*function.kind, TermKind::Var(n) if !runtime.contains(n) && std.of(n).is_none() && is_ctor(n) && struct_of(n).is_none()) =>
            {
                included.push((
                    tauto_parol::Span::new(function.span.end, t.span.end),
                    String::new(),
                ));
            }
            // A function of `std/` that is written out at each call
            // (`stack_len(&s)`) has no function to call: the call is written
            // as the proofs' calls are. Only the text around the arguments is
            // replaced, so that what is rewritten inside them stays apart.
            TermKind::App {
                function,
                arguments,
            } if matches!(&*function.kind, TermKind::Var(n) if !runtime.contains(n) && (std.of(n).is_some_and(inline_only) || std.written_by_mapping(n))) =>
            {
                let TermKind::Var(n) = &*function.kind else {
                    unreachable!()
                };
                if let Some(template) = std.of(n).and_then(mapped_fn) {
                    // The template between its holes, which come in order.
                    let mut pieces = Vec::new();
                    let mut rest = template;
                    for k in 0..arguments.len() {
                        let hole = format!("${k}");
                        let Some((before, after)) = rest.split_once(hole.as_str()) else {
                            return;
                        };
                        pieces.push(before);
                        rest = after;
                    }
                    let Some(at) = written_arguments(t.span, arguments, &calls) else {
                        return;
                    };
                    let mut start = t.span.start;
                    // Each argument is put in parentheses, as `fill` puts it.
                    for (k, (piece, a)) in pieces.iter().zip(&at).enumerate() {
                        let close = if k == 0 { "" } else { ")" };
                        included.push((
                            tauto_parol::Span::new(start, a.start),
                            format!("{close}{piece}("),
                        ));
                        start = a.end;
                    }
                    let close = if arguments.is_empty() { "" } else { ")" };
                    included.push((
                        tauto_parol::Span::new(start, t.span.end),
                        format!("{close}{rest}"),
                    ));
                }
            }
            TermKind::App {
                function,
                arguments,
            } if arguments.len() == 1
                && matches!(&*function.kind, TermKind::Var(n) if std.of(n) == Some("Succ") && !runtime.contains(n)) =>
            {
                let Some(at) = written_arguments(t.span, arguments, &calls) else {
                    return;
                };
                let x = at[0];
                included.push((tauto_parol::Span::new(t.span.start, x.start), "(".into()));
                included.push((tauto_parol::Span::new(x.end, t.span.end), " + 1)".into()));
            }
            _ => {}
        });
    }
    // The constructor of a family extracted as a struct is a function of a module
    // of Nib that executable code reaches by no path of its own; a call of it with
    // all its fields is the record that function builds, written as extraction
    // writes it: `Two::Mk(5, 6)` as `Two { left: 5, right: 6 }`.
    let mut records: Vec<tauto_parol::Span> = Vec::new();
    for s in &mut kept {
        walk_written(s, &mut |t| {
            let TermKind::App {
                function,
                arguments,
            } = &*t.kind
            else {
                return;
            };
            let TermKind::Var(n) = &*function.kind else {
                return;
            };
            if runtime.contains(n) {
                return;
            }
            let Some((family, names)) = struct_fields(n) else {
                return;
            };
            if names.len() != arguments.len() {
                return;
            }
            // The text replaced keeps its line breaks, so that the lines after it
            // stay where they were.
            let lines = |span: tauto_parol::Span| {
                let n = text
                    .get(range(span, base))
                    .map_or(0, |w| w.matches('\n').count());
                "\n".repeat(n)
            };
            let Some(at) = written_arguments(t.span, arguments, &calls) else {
                return;
            };
            let mut start = t.span.start;
            for (k, (name, a)) in names.iter().zip(&at).enumerate() {
                let open = if k == 0 {
                    format!("{family} {{ ")
                } else {
                    ", ".into()
                };
                let gap = tauto_parol::Span::new(start, a.start);
                included.push((gap, format!("{open}{}: {}", raw(name), lines(gap))));
                records.push(gap);
                start = a.end;
            }
            let gap = tauto_parol::Span::new(start, t.span.end);
            included.push((gap, format!(" }}{}", lines(gap))));
            records.push(gap);
        });
    }
    // A function of `std/` the proofs read is extracted by its full name
    // (`std::text::Text::len`), and the executable code is read again
    // without its imports. A call is written by the full name it was
    // resolved to, so that it means the function the proofs checked, not a
    // builtin of the prelude that has the same short name. So is a family or
    // a constructor the proofs declare: renamed to its full name because
    // another file has its name, it is extracted by that name, and read
    // again the short name would mean the other file's declaration.
    for s in &mut kept {
        walk_written(s, &mut |t| {
            if let TermKind::Var(n) = &*t.kind
                && n.contains(crate::surface::qualify::SEPARATOR)
                && written.contains(n)
                && !runtime.contains(n)
                && text
                    .get(range(t.span, base))
                    .is_some_and(|w| w != n.as_str())
            {
                included.push((t.span, n.to_string()));
            }
        });
    }
    // A variant that kept its short name is declared inside the modules of
    // its type when that type was renamed to its full name (a program's
    // `Pending` against the prelude's), and read again the short name finds
    // no variant: it is written by the path of its type.
    for s in &mut kept {
        walk_written(s, &mut |t| {
            if let TermKind::Var(n) = &*t.kind
                && !runtime.contains(n)
                && let Some(q) = qualified(n)
                && text
                    .get(range(t.span, base))
                    .is_some_and(|w| w == n.as_str())
            {
                included.push((t.span, q));
            }
        });
    }
    // The one constructor of a family extracted as a struct is matched as
    // Nib matches a struct by position: `usage(a, b)` as `Usage(a, b)`.
    for s in &mut kept {
        walk_written(s, &mut |t| {
            let TermKind::Match {
                scrutinee,
                result,
                arms,
                ..
            } = &*t.kind
            else {
                return;
            };
            // A match on `Nat` with a `Succ` pattern is written as the
            // chain of tests extraction writes for it, since a `nat` of Nib
            // has no constructors to match: the arms in order, the last one
            // taken when the others are not, as the kernel checked them to
            // cover every value.
            if let Some(chain) = nat_chain(arms, std, runtime, t.span.start) {
                let (first, rest) = chain.split_first().expect("a chain has an arm");
                // The line breaks of what is replaced stay, so that the lines
                // after it stay where they were.
                let lines = |span: tauto_parol::Span| {
                    let n = text
                        .get(range(span, base))
                        .map_or(0, |w| w.matches('\n').count());
                    "\n".repeat(n)
                };
                let mut push = |(span, s): (tauto_parol::Span, String)| {
                    let s = s + &lines(span);
                    included.push((span, s));
                };
                push((
                    tauto_parol::Span::new(t.span.start, scrutinee.span.start),
                    format!("{{ let {} := ", nat_subject(t.span.start)),
                ));
                push((
                    tauto_parol::Span::new(scrutinee.span.end, arms[0].body.span.start),
                    format!("; {first}"),
                ));
                for (k, open) in rest.iter().enumerate() {
                    push((
                        tauto_parol::Span::new(arms[k].body.span.end, arms[k + 1].body.span.start),
                        format!(" }} {open}"),
                    ));
                }
                let last = arms[arms.len() - 1].body.span.end;
                push((tauto_parol::Span::new(last, t.span.end), " } }".into()));
                return;
            }
            let mut start = scrutinee.span.end;
            if let Some(r) = result {
                start = start.max(r.span.end);
            }
            for arm in arms {
                let end = arm.body.span.start;
                let mut names = Vec::new();
                pattern_ctors(&arm.pattern, &mut names);
                // A constructor is written in the pattern by its short name,
                // and read again by the name it is extracted as: its family's
                // when matched as a struct, else its full name when it was
                // renamed to one.
                let mut renamed: Vec<(&str, String)> = names
                    .into_iter()
                    .filter_map(|n| {
                        let word = source_word(n);
                        match struct_of(n) {
                            Some(s) => Some((word, s.to_string())),
                            None if word != n.as_str()
                                && written.contains(n)
                                && !runtime.contains(n) =>
                            {
                                Some((word, n.to_string()))
                            }
                            None if !runtime.contains(n) => qualified(n).map(|q| (word, q)),
                            None => None,
                        }
                    })
                    .collect();
                // A nullary constructor that extraction maps onto a Nib
                // literal is matched as that literal: `Zero` as `0`, not
                // as a name that binds whatever the value is. One renamed to
                // its full name is matched by that name, as above.
                let mut binds = Vec::new();
                pattern_binds(&arm.pattern, &mut binds);
                renamed.extend(binds.into_iter().filter_map(|n| {
                    if runtime.contains(n) {
                        return None;
                    }
                    let word = crate::surface::qualify::short(n);
                    if word != n.as_str() && written.contains(n) {
                        return Some((word, n.to_string()));
                    }
                    if let Some(q) = qualified(n) {
                        return Some((word, q));
                    }
                    match std.of(n)? {
                        m @ ("Zero" | "true" | "false") => {
                            mapped_ctor(m, &[]).map(|l| (n.as_str(), l))
                        }
                        _ => None,
                    }
                }));
                if !renamed.is_empty() {
                    let skipped: Vec<tauto_parol::Span> =
                        arm.guard.iter().chain(&arm.goal).map(|g| g.span).collect();
                    for (at, word) in words(text, base, start, end) {
                        if skipped.iter().any(|g| g.start <= at && at < g.end) {
                            continue;
                        }
                        if let Some((_, s)) = renamed.iter().find(|(n, _)| *n == word) {
                            let span = tauto_parol::Span::new(at, at + word.len() as u32);
                            included.push((span, s.clone()));
                        }
                    }
                }
                start = arm.body.span.end;
            }
        });
    }
    // What the loops above wrote inside the text of a record (the name of the
    // constructor it replaces) is not written.
    included.retain(|(span, _)| {
        !records
            .iter()
            .any(|g| g != span && g.start <= span.start && span.end <= g.end)
    });
    // What a macro made in a written statement (a lambda written inside
    // `${…}` of a syntax literal, with its `Nat`) has no text of its own
    // here: the macro makes it again when the file is read again, so there
    // is nothing written to rewrite.
    included.retain(|(span, _)| span.start < crate::macros::EXPANSION_BASE);
    included.sort_by_key(|(span, _)| std::cmp::Reverse(span.start));
    for (span, literal) in included {
        bytes.splice(range(span, base), literal.into_bytes());
    }
    let mut out = String::from_utf8(bytes).expect("erasing source preserves UTF-8");
    if !made.is_empty() {
        out.push('\n');
        // A name a hygienic macro renamed (`x#1`) is written as Nib names one.
        out.push_str(&legal_names(&crate::surface::print::print_stmts(&made)).0);
    }
    out
}

/// Whether a macro made `s`: it was not written, so it has no place in the
/// written text.
fn made_by_macro(s: &Stmt) -> bool {
    let at = match s {
        Stmt::Expr(t) | Stmt::Return(Some(t)) => t.span,
        Stmt::Let { value, .. } | Stmt::Var { value, .. } | Stmt::Assign { value, .. } => {
            value.span
        }
        Stmt::While { condition, .. } => condition.span,
        Stmt::For { source, .. } => source.span,
        s => match stmt_span(s) {
            Some(span) => span,
            None => return false,
        },
    };
    at.start >= crate::macros::EXPANSION_BASE
}

fn stmt_span(s: &Stmt) -> Option<tauto_parol::Span> {
    Some(match s {
        Stmt::Fn(f) => f.span,
        Stmt::Effect(e) => e.span,
        Stmt::Theorem(t) | Stmt::Def(t) => t.span,
        Stmt::Inductive(i) => i.span,
        Stmt::Class(c) => c.span,
        Stmt::Instance(i) => i.span,
        Stmt::Struct(d) | Stmt::Enum(d) => d.span,
        Stmt::Mutual { span, .. }
        | Stmt::Module { span, .. }
        | Stmt::Extern { span, .. }
        | Stmt::Import { span, .. }
        | Stmt::Called { span, .. }
        | Stmt::Attributed { span, .. } => *span,
        _ => return None,
    })
}

/// The name the subject of a match on `Nat` is bound to, by where the
/// match starts.
fn nat_subject(at: u32) -> String {
    format!("extract_nat_{at}")
}

/// A match on `Nat` that names `Succ`, as what opens each arm of its chain
/// of tests (`if s >= 1 { let k = (s - 1); `, then `else if …`, and `else {`
/// for the last arm); `None` when no arm names `Succ` or an arm cannot be
/// written so (a guard, a goal, a pattern that is not on `Nat`).
fn nat_chain(
    arms: &[MatchArm],
    std: &StdNames,
    runtime: &HashSet<Name>,
    at: u32,
) -> Option<Vec<String>> {
    nat_chain_with(arms, std, runtime, at, &mut |name| raw(name))
}

fn nat_chain_with(
    arms: &[MatchArm],
    std: &StdNames,
    runtime: &HashSet<Name>,
    at: u32,
    binding: &mut dyn FnMut(&Name) -> String,
) -> Option<Vec<String>> {
    fn succ_in(p: &Pattern, std: &StdNames, runtime: &HashSet<Name>) -> bool {
        matches!(p, Pattern::Ctor { name, .. } if !runtime.contains(name) && std.of(name) == Some("Succ"))
    }
    fn test(
        p: &Pattern,
        at: &str,
        std: &StdNames,
        runtime: &HashSet<Name>,
        tests: &mut Vec<String>,
        binds: &mut Vec<String>,
        binding: &mut dyn FnMut(&Name) -> String,
    ) -> Option<()> {
        fn short<'n>(n: &'n Name, std: &StdNames, runtime: &HashSet<Name>) -> Option<&'n str> {
            if runtime.contains(n) { None } else { std.of(n) }
        }
        let mapped = |n| short(n, std, runtime);
        match p {
            Pattern::Wild => {}
            Pattern::Bind { name: n, .. } if mapped(n) == Some("Zero") => tests.push(format!("{at} == 0")),
            Pattern::Bind { name: n, .. } if mapped(n).is_none() => {
                binds.push(format!("let {} := {at};", binding(n)))
            }
            Pattern::Int(k) => tests.push(format!("{at} == {k}")),
            Pattern::Text(t) => tests.push(format!("{at} == {}", text_literal(t))),
            Pattern::Ctor { name, args } => match (mapped(name)?, args.as_slice()) {
                ("Zero", []) => tests.push(format!("{at} == 0")),
                ("Succ", [q]) => {
                    tests.push(format!("{at} >= 1"));
                    test(
                        q,
                        &format!("({at} - 1)"),
                        std,
                        runtime,
                        tests,
                        binds,
                        binding,
                    )?;
                }
                _ => return None,
            },
            _ => return None,
        }
        Some(())
    }
    if !arms.iter().any(|a| succ_in(&a.pattern, std, runtime)) {
        return None;
    }
    let subject = nat_subject(at);
    let n = arms.len();
    let mut out = Vec::new();
    for (k, arm) in arms.iter().enumerate() {
        // A goal on the arm is the type of its body, which the branches keep.
        if arm.guard.is_some() {
            return None;
        }
        let mut tests = Vec::new();
        let mut binds = Vec::new();
        test(
            &arm.pattern,
            &subject,
            std,
            runtime,
            &mut tests,
            &mut binds,
            binding,
        )?;
        let binds = binds.iter().map(|b| format!("{b} ")).collect::<String>();
        let open = if k + 1 == n {
            if k == 0 {
                "{ ".to_string()
            } else {
                "else { ".to_string()
            }
        } else {
            let test = if tests.is_empty() {
                "true".to_string()
            } else {
                tests.join(" && ")
            };
            if k == 0 {
                format!("if {test} {{ ")
            } else {
                format!("else if {test} {{ ")
            }
        };
        out.push(format!("{open}{binds}"));
    }
    Some(out)
}

/// The constructor as a pattern writes it: its own name. The short form of a
/// renamed constructor has its type before it (`Rect::Mk`), and the source
/// text has only `Mk` there.
fn source_word(n: &str) -> &str {
    let short = crate::surface::qualify::short(n);
    short.rsplit("::").next().unwrap_or(short)
}

/// The constructors a pattern names.
fn pattern_ctors<'p>(p: &'p Pattern, out: &mut Vec<&'p Name>) {
    match p {
        Pattern::Ctor { name, args } => {
            out.push(name);
            for a in args {
                pattern_ctors(a, out);
            }
        }
        Pattern::Record { fields, .. } => {
            for (_, f) in fields {
                pattern_ctors(f, out);
            }
        }
        _ => {}
    }
}

/// The names a pattern binds, a nullary constructor among them.
fn pattern_binds<'p>(p: &'p Pattern, out: &mut Vec<&'p Name>) {
    match p {
        Pattern::Bind { name: name, .. } => out.push(name),
        Pattern::Ctor { args, .. } => {
            for a in args {
                pattern_binds(a, out);
            }
        }
        Pattern::Record { fields, .. } => {
            for (_, f) in fields {
                pattern_binds(f, out);
            }
        }
        _ => {}
    }
}

/// The identifiers written between `start` and `end`, with where each
/// starts; a name after `.` or `::` is a field or a path, not a word.
fn words(text: &str, base: u32, start: u32, end: u32) -> Vec<(u32, &str)> {
    let from = start.saturating_sub(base) as usize;
    let to = (end.saturating_sub(base) as usize).min(text.len());
    let bytes = text.as_bytes();
    let word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut out = Vec::new();
    let mut i = from;
    while i < to {
        if word(bytes[i]) && (i == 0 || !word(bytes[i - 1])) {
            let mut j = i;
            while j < to && word(bytes[j]) {
                j += 1;
            }
            let after_path = i > 0 && matches!(bytes[i - 1], b'.' | b':');
            if !after_path && !bytes[i].is_ascii_digit() {
                out.push((i as u32 + base, &text[i..j]));
            }
            i = j;
        } else {
            i += 1;
        }
    }
    out
}

// The formatters and tokenizers the named files register remain executable
// editor entry points. One an imported file registers serves only the reading
// of that file, such as a grammar its proofs use; it is extracted when
// something reached uses it, like any imported function.
fn registered_functions(input: &crate::read::ExtractionInput, roots: &[PathBuf]) -> HashSet<Name> {
    let named: HashSet<_> = roots
        .iter()
        .map(|p| crate::program::canonicalize(p).unwrap_or_else(|_| p.clone()))
        .collect();
    fn names(stmts: &[Stmt], out: &mut HashSet<Name>) {
        for s in stmts {
            match s {
                Stmt::Fn(f) => {
                    out.insert(f.name.clone());
                }
                Stmt::Mutual { items, .. } => names(items, out),
                _ => {}
            }
        }
    }
    let mut imported = HashSet::new();
    for (file, stmts) in &input.sources {
        if !named.contains(&crate::program::canonical_path(&file.path)) {
            names(stmts, &mut imported);
        }
    }
    input
        .loaded
        .registrations
        .iter()
        .map(|r| r.function.clone())
        .filter(|f| !imported.contains(f))
        .collect()
}

/// [`reachable`], found once for the same input and roots: it extracts every function to see
/// which can be, so the extraction of a tote and its assembly would each pay for it.
pub(super) fn reachable_once(
    input: &crate::read::ExtractionInput,
    roots: &[PathBuf],
    read_time: &HashSet<Name>,
) -> Result<HashSet<Name>, Message> {
    if let Some((asked, found)) = &*input.reachable.borrow()
        && asked.as_slice() == roots
    {
        return Ok(found.clone());
    }
    let found = reachable(input, roots, read_time)?;
    *input.reachable.borrow_mut() = Some((roots.to_vec(), found.clone()));
    Ok(found)
}

// Proof-only helper functions are checked but need no executable representation.
fn reachable(
    input: &crate::read::ExtractionInput,
    roots: &[PathBuf],
    read_time: &HashSet<Name>,
) -> Result<HashSet<Name>, Message> {
    let checked = &input.checked;
    let exports: HashSet<_> = roots
        .iter()
        .map(|p| crate::program::canonicalize(p).unwrap_or_else(|_| p.clone()))
        .collect();
    let mut needed = read_time.clone();
    let mut candidates = HashSet::new();
    let mut unsupported = HashSet::new();
    let mut dependencies = std::collections::HashMap::<Name, HashSet<Name>>::new();
    let std_names = StdNames::new(&input.sources);
    let aliases = std::rc::Rc::new(type_aliases(
        checked,
        input.sources.iter().flat_map(|(_, s)| s),
    ));
    let file_modules = file_modules_of(input);
    let segments = module_segments(checked, &file_modules);
    fn references(s: &Stmt) -> HashSet<Name> {
        let mut refs = HashSet::new();
        let mut s = s.clone();
        crate::surface::walk::stmt(&mut s, &mut |t| match &*t.kind {
            TermKind::Var(n) => {
                refs.insert(n.clone());
            }
            TermKind::Field { .. } => {
                if let Some(n) = dotted(t) {
                    refs.insert(Name::from(n));
                }
            }
            _ => {}
        });
        refs
    }
    fn flatten(stmts: Vec<Stmt>, out: &mut Vec<Stmt>) {
        for s in stmts {
            if let Stmt::Mutual { items, .. } = s {
                flatten(items, out);
            } else {
                out.push(s);
            }
        }
    }
    for (file, source_stmts) in &input.sources {
        let path = &file.path;
        let mut stmts = Vec::new();
        flatten(source_stmts.clone(), &mut stmts);
        let mut normalized = Vec::new();
        for s in stmts {
            if executable(&s, &checked.runtime) {
                normalized.push(s);
            } else {
                flatten(vec![record_sugar(&checked.records, &s)], &mut normalized);
            }
        }
        for s in normalized {
            if let Stmt::Fn(f) = &s
                && executable(&s, &checked.runtime)
                && !exports.contains(&crate::program::canonical_path(path))
            {
                // A function an imported file runs as written is extracted
                // when something reached uses it, as `unused_imported` reads
                // it; its uses make what it uses needed then, not before.
                dependencies
                    .entry(f.name.clone())
                    .or_default()
                    .extend(references(&s));
            } else if executable(&s, &checked.runtime) || matches!(s, Stmt::Instance(_)) {
                needed.extend(references(&s));
            } else if let Some((f, def)) = match s {
                Stmt::Fn(f) => Some((f, false)),
                Stmt::Def(t) => def_as_fn(&t).map(|f| (f, true)),
                _ => None,
            } {
                let mut probe = Extractor {
                    dependent: None,
                    app_id: None,
                    lent_locals: std::cell::RefCell::new(HashSet::new()),
                    checked,
                    linear_data: HashSet::new(),
                    field_selections: None,
                    generated: HashSet::new(),
                    out: String::new(),
                    fresh: 0,
                    mixed: false,
                    needed: HashSet::new(),
                    dependencies: HashSet::new(),
                    runtime: Vec::new(),
                    total: HashSet::new(),
                    thunks: HashSet::new(),
                    std: &std_names,
                    written: HashSet::new(),
                    pending: Vec::new(),
                    unused: HashSet::new(),
                    aliases: aliases.clone(),
                    proof_takers: HashSet::new(),
                    refined_takers: HashSet::new(),
                    module_segments: segments.clone(),
                    file_modules: file_modules.clone(),
                    module_locals: HashMap::new(),
                    writers: HashSet::new(),
                };
                if probe.function(path, &f).is_err() {
                    unsupported.insert(f.name.clone());
                    continue;
                }
                // Follow the erased executable body, not its proof arguments or
                // termination certificates. Mapped primitives have no dependencies.
                let refs = probe.dependencies.clone();
                // A `def` is written out only when executable code reaches it.
                if !def
                    && exports.contains(&crate::program::canonical_path(path))
                    && !probe.out.is_empty()
                {
                    candidates.insert(f.name.clone());
                }
                dependencies.insert(f.name, refs);
            }
        }
    }
    // A function that uses an unsupported one is unsupported: followed from
    // each unsupported name to its users, each name once.
    let mut users = std::collections::HashMap::<&Name, Vec<&Name>>::new();
    for (name, refs) in &dependencies {
        for r in refs {
            users.entry(r).or_default().push(name);
        }
    }
    let mut queue: Vec<Name> = unsupported.iter().cloned().collect();
    while let Some(name) = queue.pop() {
        for user in users.get(&name).into_iter().flatten() {
            if unsupported.insert((*user).clone()) {
                queue.push((*user).clone());
            }
        }
    }
    // Export the tote's functions that have an executable representation. A
    // proof model without one is kept only if runtime code explicitly uses it;
    // normal extraction then reports the error instead of silently dropping it.
    needed.extend(candidates.difference(&unsupported).cloned());
    // The helpers of `std/sint.taut` call its range checks.
    if checked
        .families
        .keys()
        .any(|name| std_names.of(name) == Some("SInt"))
    {
        needed.extend(
            std_names
                .std
                .iter()
                .filter(|name| matches!(std_names.of(name), Some("SInt::fits8" | "SInt::fits16" | "SInt::fits32" | "SInt::fits64")))
                .cloned(),
        );
    }
    // What a needed function uses is needed: followed from each needed name,
    // each name once.
    let mut queue: Vec<Name> = needed.iter().cloned().collect();
    while let Some(name) = queue.pop() {
        for r in dependencies.get(&name).into_iter().flatten() {
            if needed.insert(r.clone()) {
                queue.push(r.clone());
            }
        }
    }
    Ok(needed)
}

/// The functions declared in imported files that are not reached from the
/// files named on the command line. Everything in the named files is
/// extracted, and an error there is still reported.
fn unused_imported(
    input: &crate::read::ExtractionInput,
    roots: &[PathBuf],
    read_time: &HashSet<Name>,
) -> HashSet<Name> {
    let named: HashSet<_> = roots
        .iter()
        .map(|p| crate::program::canonicalize(p).unwrap_or_else(|_| p.clone()))
        .collect();
    fn flatten(stmts: &[Stmt], out: &mut Vec<Stmt>) {
        for s in stmts {
            if let Stmt::Mutual { items, .. } = s {
                flatten(items, out);
            } else {
                out.push(s.clone());
            }
        }
    }
    fn references(s: &Stmt, refs: &mut HashSet<Name>) {
        let mut s = s.clone();
        crate::surface::walk::stmt(&mut s, &mut |t| match &*t.kind {
            TermKind::Var(n) => {
                refs.insert(n.clone());
            }
            TermKind::Field { .. } => {
                if let Some(n) = dotted(t) {
                    refs.insert(Name::from(n));
                }
            }
            _ => {}
        });
    }
    let mut imported = std::collections::HashMap::<Name, Stmt>::new();
    let mut needed = read_time.clone();
    // What `inductive_syntax!` makes for Nib is written out whether or not
    // something reaches it, so what it calls (`SynTree::expr` for an embedded
    // expression) is kept with it.
    needed.extend(input.loaded.generated_executable.iter().cloned());
    for (file, stmts) in &input.sources {
        let mut flat = Vec::new();
        flatten(stmts, &mut flat);
        let is_named = named.contains(&crate::program::canonical_path(&file.path));
        for s in flat {
            match &s {
                Stmt::Fn(f) if !is_named => {
                    imported.insert(f.name.clone(), s.clone());
                }
                // Proofs are erased from the extracted program; an imported
                // theorem or def nothing in the named files reaches is unused
                // (including one that fails because it names a skipped body).
                Stmt::Theorem(t) if !is_named => {
                    imported.insert(t.name.clone(), s.clone());
                }
                Stmt::Def(t) if !is_named => {
                    imported.insert(t.name.clone(), s.clone());
                }
                Stmt::Theorem(_) | Stmt::Def(_) | Stmt::Import { .. } => {}
                // An instance is reached through its class, not by name.
                _ => references(&s, &mut needed),
            }
        }
    }
    let mut queue: Vec<Name> = needed.iter().cloned().collect();
    while let Some(name) = queue.pop() {
        if let Some(s) = imported.get(&name) {
            let mut refs = HashSet::new();
            references(s, &mut refs);
            for r in refs {
                if needed.insert(r.clone()) {
                    queue.push(r);
                }
            }
        }
    }
    imported
        .into_keys()
        .filter(|n| !needed.contains(n))
        .collect()
}

struct Extractor<'a> {
    dependent: Option<dependent::Lowered>,
    checked: &'a Checked,
    /// The `struct`s and `enum`s the source declares `linear` (`struct(linear)
    /// Token {}`): a family the proofs read that holds one is linear in Nib
    /// too, as Nib requires it to say.
    linear_data: HashSet<Name>,
    field_selections: Option<HashMap<crate::surface::TermId, HashSet<Name>>>,
    /// The names `inductive_syntax!` declarations make for Nib.
    generated: HashSet<Name>,
    out: String,
    fresh: usize,
    mixed: bool,
    needed: HashSet<Name>,
    dependencies: HashSet<Name>,
    runtime: Vec<(PathBuf, String)>,
    total: HashSet<Name>,
    /// The functions written with effects and no parameters: such a name
    /// without `()` is the function, passed as a value.
    thunks: HashSet<Name>,
    /// The application being written: the checker's record of the implicit
    /// arguments it fixed there is found by it.
    app_id: Option<crate::surface::TermId>,
    /// Shared-borrow parameters of lambdas whose bodies are being written:
    /// passing one on lends nothing again.
    lent_locals: std::cell::RefCell<HashSet<Name>>,
    std: &'a StdNames,
    /// The functions written out, by the names they are written with.
    written: HashSet<Name>,
    /// The files whose executable source is still to be written.
    pending: Vec<(crate::program::SourceFile, Vec<Stmt>)>,
    /// Functions of imported files that nothing in the named files uses;
    /// they are not extracted, so that an import does not make the
    /// extraction depend on what it does not use.
    unused: HashSet<Name>,
    /// The functions that return a type, by name: a type naming one is
    /// read as its body, as the checker reads it, since Nib has no aliases.
    aliases: std::rc::Rc<HashMap<Name, FnDecl>>,
    /// The functions written out that take a proof among the parameters a
    /// call writes (not the laws a `where` adds).
    proof_takers: HashSet<Name>,
    /// The functions and constructors written out that take a refined
    /// value ([`Extractor::refined`]) among the parameters a call writes.
    refined_takers: HashSet<Name>,
    /// Each segment of a module path a declaration is written in, shared by
    /// every extractor of one program.
    module_segments: std::rc::Rc<HashSet<String>>,
    /// The module of each file of the program (`app::src::help`), longest
    /// first: a function `T::f` that a file declares has the module of the
    /// file in its full name, and is written without it ([`written_path`]).
    file_modules: std::rc::Rc<Vec<String>>,
    /// The fresh name a local named as such a segment is written with, once
    /// one is.
    module_locals: HashMap<String, String>,
    /// The functions that put texts before their last parameter
    /// ([`text_writers`]), by name: the program extraction also writes each
    /// as `f__w`, which pushes the same texts onto a buffer, and writes
    /// `Text::concat_all(f(…, Nil))` with it (`runtime/proof.rs`).
    writers: HashSet<Name>,
}

/// The functions among `stmts` that return a type and take only types,
/// which a type written for Nib unfolds.
fn type_aliases<'s>(
    checked: &Checked,
    stmts: impl IntoIterator<Item = &'s Stmt>,
) -> HashMap<Name, FnDecl> {
    fn walk(checked: &Checked, s: &Stmt, out: &mut HashMap<Name, FnDecl>) {
        match s {
            Stmt::Mutual { items, .. } => items.iter().for_each(|s| walk(checked, s, out)),
            Stmt::Fn(f) if f.generics.is_empty() => {
                if checked.signatures.get(&f.name).is_some_and(|sig| {
                    sig.result == Role::Type && sig.params.iter().all(|r| *r == Role::Type)
                }) {
                    out.insert(f.name.clone(), f.clone());
                }
            }
            _ => {}
        }
    }
    let mut out = HashMap::new();
    for s in stmts {
        walk(checked, s, &mut out);
    }
    out
}

type Locals = HashSet<Name>;

/// Each segment of the module path of a name `checked` declares
/// (`m::src::left` of `m::src::left::emit`), the modules the program is
/// written in, none with a fresh name yet ([`Extractor::local`]).
fn module_segments(checked: &Checked, file_modules: &[String]) -> std::rc::Rc<HashSet<String>> {
    let segments = checked
        .signatures
        .keys()
        .chain(checked.families.keys())
        .filter_map(|n| written_path(n, file_modules).rsplit_once("::").map(|(m, _)| m))
        .flat_map(|m| m.split("::"))
        .map(str::to_string)
        .collect();
    std::rc::Rc::new(segments)
}

/// The module of each file of the program, longest first.
fn file_modules_of(input: &crate::read::ExtractionInput) -> std::rc::Rc<Vec<String>> {
    let files: Vec<crate::program::SourceFile> =
        input.sources.iter().map(|(f, _)| f.clone()).collect();
    let mut modules = crate::program::module_names(&files);
    modules.sort_by_key(|m| std::cmp::Reverse(m.len()));
    modules.dedup();
    std::rc::Rc::new(modules)
}

/// A name as it is written out: `M::T::f` of a declaration `T::f` in the file
/// whose module is `M` is `T::f`, which is declared in `module T`. A name that
/// is only `M::f` stays whole: written bare it would meet another file's.
fn written_path<'a>(name: &'a str, file_modules: &[String]) -> &'a str {
    for m in file_modules {
        if let Some(rest) = name
            .strip_prefix(m.as_str())
            .and_then(|r| r.strip_prefix("::"))
            && rest.contains("::")
        {
            return rest;
        }
    }
    name
}

fn fail<X>(file: &Path, what: Message) -> Result<X, Message> {
    Err(located(file.display().to_string(), what))
}

/// `what`, said only of `f`'s file, placed at `f` and said of `f`: a problem
/// found in a function's body otherwise names its file and no line.
fn in_function(file: &crate::program::SourceFile, f: &FnDecl, what: Message) -> Message {
    let place = file.path.display().to_string();
    let bare =
        what.id == "tauto-extract-located" && what.get("place") == Some(&place.as_str().into());
    let Some(tauto_message::Value::Message(inner)) = what.get("what").filter(|_| bare) else {
        return what;
    };
    let at = f.span.start.saturating_sub(file.base) as usize;
    let (line, column) = crate::report::line_col(&file.text, at);
    located(
        format!("{place}:{line}:{column}"),
        msg!(
            "tauto-extract-in-function",
            name = crate::surface::qualify::short(&f.name).to_string(),
            what = (**inner).clone()
        ),
    )
}

/// What is wrong, and where: `place: what`.
fn located(place: String, what: Message) -> Message {
    msg!("tauto-extract-located", place = place, what = what)
}

/// Several problems as one message, in order.
fn joined(problems: Vec<Message>) -> Message {
    let mut rest = problems.into_iter().rev();
    let last = rest
        .next()
        .unwrap_or_else(|| msg!("tauto-extract-no-problems"));
    rest.fold(last, |rest, first| {
        msg!("tauto-extract-problems", first = first, rest = rest)
    })
}

impl Extractor<'_> {
    fn file(
        &mut self,
        file: &crate::program::SourceFile,
        source_stmts: &[Stmt],
    ) -> Result<(), Message> {
        let path = &file.path;
        let mut stmts = Vec::new();
        let mut runtime = Vec::new();
        let mut flattened = Vec::new();
        fn flatten(stmts: &[Stmt], out: &mut Vec<Stmt>) {
            for s in stmts {
                if let Stmt::Mutual { items, .. } = s {
                    flatten(items, out);
                } else {
                    out.push(s.clone());
                }
            }
        }
        flatten(source_stmts, &mut flattened);
        for s in &flattened {
            let made = match s {
                Stmt::Fn(f) => Some(&f.name),
                Stmt::Struct(d) | Stmt::Enum(d) => Some(&d.name),
                _ => None,
            };
            if made.is_some_and(|n| self.generated.contains(n)) {
                self.out
                    .push_str(&crate::surface::print::print_stmts(std::slice::from_ref(s)));
                continue;
            }
            if self.mixed && executable(s, &self.checked.runtime) {
                runtime.push(s.clone());
                continue;
            }
            match record_sugar(&self.checked.records, s) {
                Stmt::Mutual { items, .. } => stmts.extend(items),
                s => stmts.push(s),
            }
        }
        for s in &stmts {
            match s {
                Stmt::Inductive(i) => self.inductive(path, i)?,
                Stmt::Struct(d) => {
                    self.inductive(path, &tauto_kernel::check::program_family(d, true))?
                }
                Stmt::Enum(d) => {
                    self.inductive(path, &tauto_kernel::check::program_family(d, false))?
                }
                Stmt::Fn(f) => self
                    .function(path, f)
                    .map_err(|e| in_function(file, f, e))?,
                Stmt::Effect(e) => self.effect(path, e)?,
                Stmt::Class(c) if self.std.of(&c.name).is_some_and(mapped_class) => {}
                Stmt::Instance(i)
                    if self.std.of(&i.class).is_some_and(marker_class)
                        && self.checked.classes.contains(&i.class) =>
                {
                    self.instance(path, i)?;
                    self.marker_instance(path, i)?
                }
                Stmt::Class(c) if self.checked.classes.contains(&c.name) => self.class(path, c)?,
                Stmt::Instance(i)
                    if self.std.of(&i.class).is_some_and(mapped_class)
                        && head_name(&i.head)
                            .and_then(|name| self.std.of(name))
                            .is_some_and(std_instance_head) => {}
                Stmt::Instance(i) if self.checked.classes.contains(&i.class) => {
                    self.instance(path, i)?
                }
                // A def that runs as written has nothing the kernel checked
                // to extract: it is kept as the type function it reads as.
                Stmt::Def(t)
                    if self.mixed
                        && self.needed.contains(&t.name)
                        && !self.checked.runtime.contains(&t.name) =>
                {
                    if let Some(f) = def_as_fn(t) {
                        self.function(path, &f)?;
                    }
                }
                Stmt::Theorem(_) | Stmt::Def(_) | Stmt::Import { .. } => {}
                Stmt::Let { name, .. } => {
                    return fail(
                        path,
                        msg!(
                            "tauto-extract-a-constant-is-not-extracted",
                            name = name.to_string()
                        ),
                    );
                }
                _ => {
                    return fail(path, msg!("tauto-extract-only-declarations-of-the-proof"));
                }
            }
        }
        if !runtime.is_empty() {
            // Written once every file is extracted, when what each name is
            // extracted as is known.
            self.pending.push((file.clone(), source_stmts.to_vec()));
        }
        Ok(())
    }

    /// The executable source of each file that has some, kept verbatim,
    /// including its original positions and kinds: reprinting it would lose
    /// source locations and can change native syntax.
    fn runtime_files(
        &mut self,
        reasons: &HashMap<Name, tauto_message::Message>,
    ) -> Result<(), Message> {
        let mut problems = Vec::new();
        for (file, stmts) in &self.pending {
            self.proofs_given(file, stmts, reasons, &mut problems);
        }
        if !problems.is_empty() {
            return Err(joined(problems));
        }
        // An imported function nothing in the named files reaches (a macro's, which
        // runs while the program is read) is left out of what runs.
        let kept: HashSet<Name> = self
            .checked
            .runtime
            .iter()
            .filter(|n| !self.unused.contains(*n))
            .cloned()
            .collect();
        // The macros the files read again still call in an expression: their
        // calls are expanded again there, so their `macro fn`s stay.
        let mut called: HashSet<String> = HashSet::new();
        for (file, _) in &self.pending {
            if let Ok(written) = tauto_parse::parse_program_unresolved_at(&file.text, file.base) {
                for mut s in written.stmts {
                    crate::surface::walk::stmt(&mut s, &mut |t| {
                        if let TermKind::MacroCall { name, .. } = &*t.kind {
                            called.insert(name.clone());
                        }
                    });
                }
            }
        }
        for (file, stmts) in std::mem::take(&mut self.pending) {
            let source = runtime_source(
                &file.text,
                file.base,
                &stmts,
                &kept,
                &self.std,
                &self.written,
                &called,
                Ctors {
                    struct_of: &|c| self.struct_fields(c).map(|(family, _)| family),
                    struct_fields: &|c| self.struct_fields(c),
                    is_ctor: &|c| self.is_ctor(c),
                    qualified: &|c| self.qualified_ctor(c),
                },
            );
            self.runtime.push((file.path, source));
        }
        Ok(())
    }

    /// Executable code that the kernel does not check cannot give a proof:
    /// extraction erases the proof arguments of the functions it calls and
    /// the proof fields of the values it builds. So it may not call a
    /// declaration that takes a proof, a constructor with a proof field
    /// among them, nor write such a constructor's record. A value built by
    /// a function the kernel checked, and so with its proof, may be passed
    /// on and read.
    fn proofs_given(
        &self,
        file: &crate::program::SourceFile,
        stmts: &[Stmt],
        reasons: &HashMap<Name, tauto_message::Message>,
        problems: &mut Vec<Message>,
    ) {
        if let Some(d) = &self.dependent {
            for statement in stmts {
                if !executable(statement, &self.checked.runtime) {
                    continue;
                }
                let mut statement = statement.clone();
                crate::surface::walk::stmt(&mut statement, &mut |t| {
                    if let TermKind::Match { arms, .. } = &*t.kind {
                        fn forbidden_pattern(
                            p: &Pattern,
                            checked: &Checked,
                            families: &HashSet<Name>,
                        ) -> bool {
                            let (name, children): (Option<&Name>, Vec<&Pattern>) = match p {
                                Pattern::Ctor { .. } if let Some(ps) = p.product_members() => {
                                    (None, ps)
                                }
                                Pattern::Bind { name: n, .. } => (Some(n), Vec::new()),
                                Pattern::Ctor { name, args } => (Some(name), args.iter().collect()),
                                Pattern::Record { name, fields } => {
                                    (Some(name), fields.iter().map(|(_, p)| p).collect())
                                }
                                _ => (None, Vec::new()),
                            };
                            families.iter().any(|f| {
                                name.is_some_and(|name| {
                                    f == name
                                        || checked.families.get(f).is_some_and(|family| {
                                            family.ctors.iter().any(|c| c == name)
                                        })
                                })
                            }) || children
                                .into_iter()
                                .any(|p| forbidden_pattern(p, checked, families))
                        }
                        if arms
                            .iter()
                            .any(|a| forbidden_pattern(&a.pattern, self.checked, &d.families))
                        {
                            problems.push(located(
                                file.path.display().to_string(),
                                msg!("tauto-extract-opaque-dependent-pattern"),
                            ));
                        }
                    }
                });
            }
        }
        let runtime = &self.checked.runtime;
        let refined_takers = &self.refined_takers;
        // A function by the parameters a call writes; a constructor by its
        // fields, after the family's parameters.
        let takes_proof = |n: &Name| {
            !runtime.contains(n)
                && (self.proof_takers.contains(n)
                    // A family mapped onto a type of Nib (`U64` onto `u64`)
                    // is not built by its constructor there; its name is
                    // Nib's own type.
                    || self.checked.family_of_ctor(n).is_some_and(|(name, fam)| {
                        self.mapped_type(name).is_none()
                            && self.checked.signatures.get(n).is_some_and(|sig| {
                                sig.params
                                    .get(fam.params..)
                                    .is_some_and(|fields| fields.contains(&Role::Proof))
                            })
                    }))
        };
        let mut kept: Vec<Stmt> = Vec::new();
        for s in stmts {
            match s {
                Stmt::Mutual { items, .. } => kept.extend(
                    items
                        .iter()
                        .filter(|i| matches!(i, Stmt::Fn(f) if runtime.contains(&f.name)))
                        .cloned(),
                ),
                s if executable(s, runtime) => kept.push(s.clone()),
                _ => {}
            }
        }
        for s in &mut kept {
            let before = problems.len();
            crate::surface::walk::stmt(s, &mut |t| {
                let (name, what) = match &*t.kind {
                    TermKind::Var(n) if takes_proof(n) => {
                        (n.clone(), "tauto-extract-unchecked-takes-proof")
                    }
                    TermKind::Var(n) if !runtime.contains(n) && refined_takers.contains(n) => {
                        (n.clone(), "tauto-extract-unchecked-takes-refined")
                    }
                    TermKind::Record { name, .. }
                        if !runtime.contains(name)
                            && self
                                .checked
                                .records
                                .get(name)
                                .is_some_and(|(ctor, _)| takes_proof(ctor)) =>
                    {
                        (name.clone(), "tauto-extract-unchecked-proof-field")
                    }
                    TermKind::Record { name, .. }
                        if !runtime.contains(name) && refined_takers.contains(name) =>
                    {
                        (name.clone(), "tauto-extract-unchecked-refined-field")
                    }
                    _ => return,
                };
                let at = (t.span.start.saturating_sub(file.base)) as usize;
                let (l, c) = crate::report::line_col(&file.text, at);
                let short = crate::surface::qualify::short(&name);
                problems.push(located(
                    format!("{}:{l}:{c}", file.path.display()),
                    msg!(what, name = short.to_string()),
                ));
            });
            if problems.len() > before
                && let Stmt::Fn(f) = s
                && let Some(reason) = reasons.get(&f.name)
            {
                let at = f.span.start.saturating_sub(file.base) as usize;
                let (line, column) = crate::report::line_col(&file.text, at);
                problems.insert(
                    before,
                    located(
                        format!("{}:{line}:{column}", file.path.display()),
                        msg!(
                            "tauto-extract-unchecked-function",
                            name = crate::surface::qualify::short(&f.name).to_string(),
                            reason = reason.clone()
                        ),
                    ),
                );
            }
        }
    }

    /// The functions of the kernel's prelude that executable code calls
    /// (`nat_lt`, `nat_sub`, …). No file declares them, so no file writes
    /// them out; each is written as the proofs' calls to it are, by its
    /// mapping, and only when the program has no declaration of its own.
    fn kernel_functions(&mut self) -> Result<(), Message> {
        let prelude = bound_kernel_prelude()?;
        let path = Path::new("prelude");
        for s in &prelude.stmts {
            if let Stmt::Fn(f) = s
                && self.needed.contains(&f.name)
                && !self.std.of(&f.name).is_some_and(nib_prelude_fn)
                && self.std.of(&f.name).is_some_and(|n| mapped_fn(n).is_some())
            {
                self.function(path, f)?;
            }
        }
        Ok(())
    }

    fn inductive(&mut self, path: &Path, i: &InductiveDecl) -> Result<(), Message> {
        if self
            .dependent
            .as_ref()
            .is_some_and(|d| d.families.contains(&i.name))
        {
            return Ok(());
        }
        // A family over universe levels (`inductive UBox(u: Level, A: Type(u))`) is a
        // template the kernel checks once and makes an instance of at each level it
        // is used at: no family of its own name is there, and it has no runtime form.
        if over_levels(i) {
            return Ok(());
        }
        let Some(fam) = self.checked.families.get(&i.name) else {
            return fail(
                path,
                msg!("tauto-extract-did-not-check", name = i.name.to_string()),
            );
        };
        if fam.prop || fam.predicate || self.mapped_type(&i.name).is_some() {
            return Ok(());
        }
        if fam.indices > 0 {
            return fail(
                path,
                msg!(
                    "tauto-extract-has-indices-a-family-of",
                    name = i.name.to_string()
                ),
            );
        }
        // Executable code names the family and its constructors by what
        // they are extracted as, as it names the functions.
        self.written.insert(i.name.clone());
        // A constructor's full name is what it is written as only when its
        // family is written in its modules (`in_modules_text`); a family
        // written under its short name is not reached by that path.
        self.written.extend(
            i.constructors
                .iter()
                .filter(|c| i.name.contains("::") || !c.name.contains("::"))
                .map(|c| c.name.clone()),
        );
        let kept = self.kept_params(&i.name);
        let generics: Vec<&str> = i
            .params
            .iter()
            .zip(&kept)
            .filter(|(_, k)| **k)
            .map(|((n, _), _)| n.as_str())
            .collect();
        let mut locals: Locals = i
            .params
            .iter()
            .zip(&kept)
            .filter(|(_, keep)| **keep)
            .map(|((name, _), _)| name.clone())
            .collect();
        if let [c] = i.constructors.as_slice()
            && let Some((_, names)) = self.struct_fields(&c.name)
        {
            // One constructor with fields: a struct, so that Nib reads
            // `x.f` and writes `T { f: e }` as the proofs do.
            let sig = &self.checked.signatures[&c.name];
            let mut fields = Vec::new();
            let mut types = Vec::new();
            let mut linear = false;
            for (k, (n, t)) in c.params.iter().enumerate() {
                if sig.params[fam.params + k] == Role::Value {
                    linear |= self.owns_slots(t);
                    if self.refined(t) {
                        self.refined_takers.insert(c.name.clone());
                        self.refined_takers.insert(i.name.clone());
                    }
                    let ty = self.ty(path, t, &locals)?;
                    fields.push(format!("{}: {ty}", raw(n)));
                    types.push(ty);
                }
                locals.insert(n.clone());
            }
            debug_assert_eq!(fields.len(), names.len());
            let decl = format!(
                "struct({}) {}{} {{ {} }}",
                if linear { "linear" } else { "shared" },
                raw(&i.name),
                type_params(&generics),
                fields.join(", ")
            );
            let _ = writeln!(self.out, "\n{}", in_modules_text(&i.name, &decl));
            // Programs call the constructor by the name the proofs give it.
            // A struct is built only by its fields, so the name becomes a
            // function that builds them.
            if c.name != i.name {
                // The parameters have names of their own: a field's name can
                // be the name of a module the function is written in.
                let args: Vec<String> = names
                    .iter()
                    .map(|_| self.fresh("field").to_string())
                    .collect();
                let values: Vec<String> = names
                    .iter()
                    .zip(&args)
                    .map(|(n, a)| format!("{}: {a}", raw(n)))
                    .collect();
                let params: Vec<String> = args
                    .iter()
                    .zip(&types)
                    .map(|(a, t)| format!("{a}: {t}"))
                    .collect();
                let result = if generics.is_empty() {
                    i.name.to_string()
                } else {
                    format!("{}({})", i.name, generics.join(", "))
                };
                let target = extracted_ctor(self.checked, &c.name)
                    .ok_or_else(|| format!("constructor {} has no checked owner", c.name))?;
                let ctor = raw(&target);
                // A record expression names its struct without a path, which
                // the modules around it find.
                let decl = format!(
                    "fn {ctor}{}({}): {result} {{\n  {} {{ {} }}\n}}",
                    angle(&generics),
                    params.join(", "),
                    i.name,
                    values.join(", ")
                );
                let _ = writeln!(self.out, "\n{}", in_modules_text(&target, &decl));
            }
            return Ok(());
        }
        let linear = i.constructors.iter().any(|c| {
            let sig = &self.checked.signatures[&c.name];
            c.params
                .iter()
                .enumerate()
                .any(|(k, (_, t))| sig.params[fam.params + k] == Role::Value && self.owns_slots(t))
        });
        let mut decl = format!(
            "enum({}) {}{} {{\n",
            if linear { "linear" } else { "shared" },
            raw(&i.name),
            type_params(&generics)
        );
        for c in &i.constructors {
            let sig = &self.checked.signatures[&c.name];
            let mut fields = Vec::new();
            for (k, (n, t)) in c.params.iter().enumerate() {
                let role = sig.params[fam.params + k];
                if role == Role::Value {
                    if self.refined(t) {
                        self.refined_takers.insert(c.name.clone());
                    }
                    fields.push(self.ty(path, t, &locals)?);
                }
                locals.insert(n.clone());
            }
            // A variant is declared by its own name: one another type's
            // variant shares has its full name (`m::Bytecode::CBranch`), which
            // names this one.
            let name = &c.name;
            if fields.is_empty() {
                let _ = writeln!(decl, "  {name}");
            } else {
                let _ = writeln!(decl, "  {name}({})", fields.join(", "));
            }
        }
        decl.push('}');
        let _ = writeln!(self.out, "\n{}", in_modules_text(&i.name, &decl));
        Ok(())
    }

    /// Which parameters of the family `n` its extracted type keeps: the
    /// types. A parameter that is a predicate (`P: (A) -> Prop`) or a value
    /// (`p: (A) -> Bool`) is used only by the proofs in the fields, since a
    /// family of data has no indices and its value fields' types are data,
    /// so the extracted family does not take it.
    fn kept_params(&self, n: &Name) -> Vec<bool> {
        let Some(fam) = self.checked.families.get(n) else {
            return Vec::new();
        };
        match fam
            .ctors
            .first()
            .and_then(|c| self.checked.signatures.get(c))
        {
            Some(sig) => sig.params[..fam.params]
                .iter()
                .map(|r| *r == Role::Type)
                .collect(),
            None => vec![true; fam.params],
        }
    }

    /// Whether the type `t` mentions what a program holds linearly (the
    /// mapped slots type, or a `struct` or `enum` declared `linear`): a
    /// family with such a field is linear itself.
    fn owns_slots(&self, t: &SurfaceTerm) -> bool {
        let mut found = false;
        let mut t = t.clone();
        crate::surface::walk::term(&mut t, &mut |u| {
            if let TermKind::Var(n) = &*u.kind
                && (self.mapped_type(n) == Some("Slots") || self.linear_data.contains(n))
            {
                found = true;
            }
        });
        found
    }

    /// Whether the type `t` names a family whose extracted type leaves out a
    /// parameter (`Refined(Nat, Pos)`, `List(Refined(Nat, Pos))`): Nib reads
    /// `Refined(Nat, Pos)` and `Refined(Nat, Even)` as the same type.
    fn refined(&self, t: &SurfaceTerm) -> bool {
        let mut found = false;
        let mut t = t.clone();
        crate::surface::walk::term(&mut t, &mut |u| {
            if let TermKind::Var(n) = &*u.kind
                && self.mapped_type(n).is_none()
                && self
                    .checked
                    .families
                    .get(n)
                    .is_some_and(|f| !f.prop && !f.predicate)
                && self.kept_params(n).contains(&false)
            {
                found = true;
            }
        });
        found
    }

    /// For the one constructor of a family of data with fields: the family
    /// and the names of its value fields (it is extracted as a struct).
    fn struct_fields(&self, ctor: &Name) -> Option<(Name, Vec<Name>)> {
        let (family, (_, names)) = self.checked.record_of_ctor(ctor)?;
        let fam = self.checked.families.get(family)?;
        if fam.prop || fam.indices > 0 || self.mapped_type(family).is_some() {
            return None;
        }
        let sig = self.checked.signatures.get(ctor)?;
        let values: Vec<Name> = names
            .iter()
            .zip(sig.params.get(fam.params..)?)
            .filter(|(_, r)| **r == Role::Value)
            .map(|(n, _)| n.clone())
            .collect();
        (!values.is_empty()).then(|| (family.clone(), values))
    }

    /// Type binders used by the executable declaration. Full checked calls
    /// erase their type/proof arguments; a binder occurring only in those
    /// slots is not a native generic (and cannot be inferred by Rust).
    /// Unknown and partial calls are kept conservatively.
    fn native_generic_uses(&self, f: &FnDecl) -> HashSet<Name> {
        let mut uses = HashSet::new();
        let mut statement = Stmt::Fn(f.clone());
        // Binder declarations themselves are not uses. Their domains, value
        // annotations, constraints and bodies still are.
        let Stmt::Fn(function) = &mut statement else {
            unreachable!()
        };
        function.generics.clear();
        function.generic_types.clear();
        let mut body = function.body.clone();
        crate::surface::walk::term(&mut body, &mut |term| {
            if let TermKind::App {
                function,
                arguments,
            } = &*term.kind
                && let TermKind::Var(name) = &*function.kind
                && let Some(signature) = self.checked.source_call_signature(name)
                && arguments.len()
                    == self
                        .checked
                        .arities
                        .get(name)
                        .copied()
                        .map(|arity| {
                            arity
                                - self
                                    .checked
                                    .row_parameter_slots
                                    .get(name)
                                    .map_or(0, |slots| slots.len())
                        })
                        .unwrap_or(signature.params.len())
            {
                let arguments = arguments
                    .iter()
                    .zip(&signature.params)
                    .filter(|(_, role)| **role == Role::Value)
                    .map(|(argument, _)| argument.clone())
                    .collect();
                *term = term.with_kind(
                    TermKind::App {
                        function: function.clone(),
                        arguments,
                    },
                    term.span,
                );
            }
        });
        function.body = body;
        let source_roles = self
            .checked
            .signatures
            .get(&f.name)
            .map(|s| s.source_generic_roles(f))
            .unwrap_or_default();
        for (index, (_, ty)) in f.generic_parameters().into_iter().enumerate() {
            if source_roles.get(index) == Some(&Role::Value) {
                function.generic_types.push(ty);
            }
        }
        crate::surface::walk::stmt(&mut statement, &mut |term| {
            if let TermKind::Var(name) = &*term.kind {
                uses.insert(name.clone());
            }
        });
        for constraint in &f.where_ {
            let mut arguments = vec![constraint.ty.clone()];
            arguments.extend(constraint.arguments.iter().cloned());
            for mut argument in arguments {
                crate::surface::walk::term(&mut argument, &mut |term| {
                    if let TermKind::Var(name) = &*term.kind {
                        uses.insert(name.clone());
                    }
                });
            }
        }
        uses
    }

    fn function(&mut self, path: &Path, f: &FnDecl) -> Result<(), Message> {
        if self
            .dependent
            .as_ref()
            .is_some_and(|d| d.functions.contains(&f.name))
        {
            return Ok(());
        }
        if if self.mixed {
            !self.needed.contains(&f.name)
        } else {
            self.unused.contains(&f.name)
        } {
            return Ok(());
        }
        let mut stripped = f.clone();
        crate::surface::walk::strip_recursion_proofs(&mut stripped);
        let f = &stripped;
        let Some(sig) = self.checked.signatures.get(&f.name).cloned() else {
            return fail(
                path,
                msg!("tauto-extract-did-not-check", name = f.name.to_string()),
            );
        };
        let std = self.std.of(&f.name);
        if sig.result != Role::Value
            || std.is_some_and(builtin_name)
            || std.is_some_and(inline_only)
        {
            return Ok(());
        }
        let generic_uses = self.native_generic_uses(f);
        let source_generic_roles = sig.source_generic_roles(f);
        let mut generics: Vec<Name> = Vec::new();
        let mut params = Vec::new();
        let mut locals: Locals = Locals::new();
        for (index, (name, ty)) in f.generic_parameters().into_iter().enumerate() {
            if f.rows.get(index) == Some(&true) {
                generics.push(name.clone());
            } else {
                match source_generic_roles[index] {
                    Role::Type => {
                        if generic_uses.contains(&name) {
                            generics.push(name.clone());
                        }
                    }
                    Role::Proof => {
                        self.proof_takers.insert(f.name.clone());
                    }
                    Role::Value => {
                        if self.refined(&ty) {
                            self.refined_takers.insert(f.name.clone());
                        }
                        let ty = self.ty(path, &ty, &locals)?;
                        params.push(format!("{}: {ty}", self.local(&name)));
                    }
                }
            }
            locals.insert(name);
        }
        // The records of a `where` come after the generics in the kernel's
        // signature; the extracted function has the `where` itself.
        // A row variable is read as two parameters (`check/effects.rs`), in
        // place of its generic.
        let records = self.records_of(&f.where_);
        let row_var = f
            .effects
            .iter()
            .flatten()
            .any(|e| e.row_variable().is_some_and(|v| f.generics.contains(&v)));
        let n_generics = f.generics.len() + records + usize::from(row_var);
        for (k, (n, t)) in f.params.iter().zip(&f.param_types).enumerate() {
            let Some(t) = t else {
                return fail(
                    path,
                    msg!(
                        "tauto-extract-parameter-has-no-type",
                        name = f.name.to_string(),
                        n = n.to_string()
                    ),
                );
            };
            let lent = match f.borrows.get(k) {
                Some(Some(true)) => "&mut ",
                Some(Some(false)) => "&",
                _ => "",
            };
            match sig.params[n_generics + k] {
                Role::Type => generics.push(n.clone()),
                Role::Proof => {
                    self.proof_takers.insert(f.name.clone());
                }
                Role::Value => {
                    if self.refined(t) {
                        self.refined_takers.insert(f.name.clone());
                    }
                    let ty = self.ty(path, t, &locals)?;
                    params.push(format!("{}: {}", self.local(n), borrowed_ty(lent, &ty)))
                }
            }
            locals.insert(n.clone());
        }
        let Some(result) = &f.result else {
            return fail(
                path,
                msg!(
                    "tauto-extract-has-no-result-type",
                    name = f.name.to_string()
                ),
            );
        };
        let result = self.ty(path, result, &locals)?;
        let body = match std.and_then(mapped_fn) {
            Some(template) => {
                self.template_dependencies(template)?;
                let names: Vec<Name> = f
                    .params
                    .iter()
                    .enumerate()
                    .filter(|(k, _)| sig.params[n_generics + k] == Role::Value)
                    .map(|(_, n)| n.clone())
                    .collect();
                fill(
                    template,
                    &names.iter().map(ToString::to_string).collect::<Vec<_>>(),
                )
            }
            None => self.expr(path, &f.body, &locals, 1)?,
        };
        // A row variable is written `!e` again, as the source declares it,
        // and is not a type with a bound. A generic keeps the bound the
        // source writes (`<A: Shared>`), and without one is affine, as in any
        // function: a body that copies `x: A` is rejected where it is written.
        let generics: Vec<String> = generics
            .into_iter()
            .map(|g| {
                match f.generics.iter().position(|name| name == &g) {
                    Some(index) if f.rows.get(index) == Some(&true) => format!("!{g}"),
                    Some(index) => with_bound(&g, f.bounds.get(index).cloned().flatten()),
                    // A type written as a parameter, `A: Type`, may be carried
                    // by a value of the proof language: it stays shared.
                    None => format!("{g}: Shared"),
                }
            })
            .collect();
        let generics: Vec<&str> = generics.iter().map(String::as_str).collect();
        let wheres = self.where_clause(path, &f.where_, &locals)?;
        let row = match f.effects.as_deref() {
            Some(row) if !row.is_empty() => format!(" ! {}", row_text(row)),
            _ => String::new(),
        };
        // `borrows(…)` after the result: keep it so a live item still freezes
        // the named source under ordinary Nib ownership.
        let lends = match &f.lends {
            Some(paths) if !paths.is_empty() => {
                let shown: Vec<String> = paths
                    .iter()
                    .map(|path| {
                        let mut parts = path.split('.');
                        let root = parts.next().unwrap_or(path.as_str());
                        let root = raw(&self.local(&Name::from(root)));
                        let fields: Vec<&str> = parts.collect();
                        if fields.is_empty() {
                            root
                        } else {
                            format!("{root}.{}", fields.join("."))
                        }
                    })
                    .collect();
                format!(" borrows({})", shown.join(", "))
            }
            _ => String::new(),
        };
        // `M::f` is written with its prefix: `fn M::f`.
        let full = written_path(f.name.as_str(), &self.file_modules);
        let decl = format!(
            "fn {}{}({}): {result}{lends}{row}{wheres} {{\n  {body}\n}}",
            raw(&full),
            angle(&generics),
            params.join(", ")
        );
        let _ = writeln!(self.out, "\n{decl}");
        self.written.insert(f.name.clone());
        // The kernel has checked termination, including for computations
        // with effects, and extraction guards the arithmetic it introduces.
        // The row checker still follows the declared operations.
        self.total.insert(f.name.clone());
        if !row.is_empty() && params.is_empty() {
            self.thunks.insert(f.name.clone());
        }
        Ok(())
    }

    /// `effect e(P, …): R`, its types mapped as the functions' are.
    fn effect(&mut self, path: &Path, e: &crate::surface::EffectDecl) -> Result<(), Message> {
        if self
            .dependent
            .as_ref()
            .is_some_and(|d| d.effects.contains(&e.name))
        {
            return Ok(());
        }
        let locals = Locals::new();
        let mut params = Vec::new();
        for (i, p) in e.params.iter().enumerate() {
            let Some(p) = p else {
                return fail(
                    path,
                    msg!(
                        "tauto-extract-a-parameter-has-no-type",
                        name = e.name.to_string()
                    ),
                );
            };
            // Nib reads a parameter only with its name, so the written one
            // is kept and one is made up where none was written.
            let name = match e.param_names.get(i) {
                Some(n) if !n.is_empty() => n.to_string(),
                _ => format!("p{i}"),
            };
            params.push(format!("{}: {}", raw(&name), self.ty(path, p, &locals)?));
        }
        let result = match &e.result {
            Some(r) => self.ty(path, r, &locals)?,
            None => "Unit".into(),
        };
        let resume = e
            .resume
            .as_ref()
            .map(|r| match r.as_str() {
                "direct" => " direct".to_string(),
                r => format!(" resume {r}"),
            })
            .unwrap_or_default();
        let _ = writeln!(
            self.out,
            "\neffect {}({}): {result}{resume}",
            raw(&e.name),
            params.join(", ")
        );
        Ok(())
    }

    /// How many constraints of a `where` are records of the proof language.
    fn records_of(&self, wheres: &[crate::surface::Constraint]) -> usize {
        if wheres
            .iter()
            .all(|c| self.checked.classes.contains(&c.class))
        {
            wheres.len()
        } else {
            0
        }
    }

    fn where_clause(
        &self,
        path: &Path,
        wheres: &[crate::surface::Constraint],
        locals: &Locals,
    ) -> Result<String, Message> {
        if wheres.is_empty() {
            return Ok(String::new());
        }
        let mut parts = Vec::new();
        for c in wheres {
            parts.push(format!("{}({})", c.class, self.ty(path, &c.ty, locals)?));
        }
        Ok(format!(" where {}", parts.join(", ")))
    }

    fn class(&mut self, path: &Path, c: &crate::surface::ClassDecl) -> Result<(), Message> {
        let bound = if self.std.native_key_class(&c.name) {
            "linear"
        } else {
            c.bound.as_deref().unwrap_or("Type")
        };
        let mut text = format!("\nclass {}({}: {bound}) {{\n", c.name, c.param);
        for m in &c.methods {
            let locals: Locals = std::iter::once(c.param.clone())
                .chain(m.generics.iter().cloned())
                .collect();
            let generics: Vec<_> = m.generics.iter().map(Name::as_str).collect();
            let mut params = Vec::new();
            for (k, (n, t)) in m.params.iter().zip(&m.param_types).enumerate() {
                let Some(t) = t else {
                    return fail(
                        path,
                        msg!(
                            "tauto-extract-member-parameter-has-no-type",
                            class = c.name.to_string(),
                            member = m.name.to_string(),
                            n = n.to_string()
                        ),
                    );
                };
                let lent = match m.borrows.get(k) {
                    Some(Some(true)) => "&mut ",
                    Some(Some(false)) => "&",
                    _ => "",
                };
                params.push(format!(
                    "{}: {}",
                    raw(n),
                    borrowed_ty(lent, &self.ty(path, t, &locals)?)
                ));
            }
            let result = match &m.result {
                Some(r) => self.ty(path, r, &locals)?,
                None => "Unit".into(),
            };
            let _ = writeln!(
                text,
                "  fn {}{}({}): {result}",
                raw(&m.name),
                angle(&generics),
                params.join(", ")
            );
        }
        text.push_str("}\n");
        self.out.push_str(&text);
        Ok(())
    }

    /// `instance<G> C(H) where … { fn m(…): R { … } }`: the methods, with
    /// the types and the proofs erased like a function's.
    /// The prelude's instance for an instance of a [`marker_class`]: its head,
    /// and no methods.
    fn marker_instance(
        &mut self,
        path: &Path,
        i: &crate::surface::InstanceDecl,
    ) -> Result<(), Message> {
        // A program that also runs as written gets it from its statements
        // (`runtime::proof`).
        if self.mixed {
            return Ok(());
        }
        let locals: Locals = i.generics.iter().cloned().collect();
        let head = self.ty(path, &i.head, &locals)?;
        let wheres = self.where_clause(path, &i.where_, &locals)?;
        let generics: Vec<String> = i
            .generics
            .iter()
            .enumerate()
            .map(|(index, g)| with_bound(g, i.bounds.get(index).cloned().flatten()))
            .collect();
        let generics: Vec<&str> = generics.iter().map(String::as_str).collect();
        let text = format!(
            "\ninstance{} {MARKER_PRELUDE_CLASS}({head}){wheres} {{}}\n",
            angle(&generics)
        );
        self.out.push_str(&text);
        Ok(())
    }

    fn instance(&mut self, path: &Path, i: &crate::surface::InstanceDecl) -> Result<(), Message> {
        let records = self.records_of(&i.where_);
        let n_generics = i.generics.len() + records;
        let locals: Locals = i.generics.iter().cloned().collect();
        let head = self.ty(path, &i.head, &locals)?;
        let wheres = self.where_clause(path, &i.where_, &locals)?;
        let generics: Vec<String> = i
            .generics
            .iter()
            .enumerate()
            .map(|(index, g)| with_bound(g, i.bounds.get(index).cloned().flatten()))
            .collect();
        let generics: Vec<&str> = generics.iter().map(String::as_str).collect();
        let mut text = format!(
            "\ninstance{} {}({head}){wheres} {{\n",
            angle(&generics),
            i.class
        );
        // A product `A × B` is the instance for the prelude's `Pair` it is read as.
        let pair = crate::bindings::library_name("Pair");
        let numeral = tauto_kernel::check::numeral_head(&i.head);
        let head_ref = match &*i.head.kind {
            _ if i.head.as_pair_type().is_some() => Some(&pair),
            _ if numeral.is_some() => numeral.as_ref(),
            _ => head_name(&i.head),
        };
        for m in &i.methods {
            let target = head_ref.and_then(|head| {
                self.checked.instance_methods.get(&(
                    i.class.clone(),
                    head.clone(),
                    m.name.to_string(),
                ))
            });
            let Some(sig) = target.and_then(|n| self.checked.signatures.get(n)).cloned() else {
                return fail(
                    path,
                    msg!("tauto-extract-did-not-check", name = m.name.to_string()),
                );
            };
            let mut params = Vec::new();
            let mut inner = locals.clone();
            inner.extend(m.generics.iter().cloned());
            let method_generics: Vec<_> = m.generics.iter().map(Name::as_str).collect();
            for (k, (n, t)) in m.params.iter().zip(&m.param_types).enumerate() {
                let Some(t) = t else {
                    return fail(
                        path,
                        msg!(
                            "tauto-extract-member-parameter-has-no-type",
                            class = i.class.to_string(),
                            member = m.name.to_string(),
                            n = n.to_string()
                        ),
                    );
                };
                let lent = match m.borrows.get(k) {
                    Some(Some(true)) => "&mut ",
                    Some(Some(false)) => "&",
                    _ if self.std.of(&i.class).is_some_and(mapped_class) => "&",
                    _ => "",
                };
                if sig.params[n_generics + m.generics.len() + k] == Role::Value {
                    let ty = self.ty(path, t, &inner)?;
                    params.push(format!("{}: {}", self.local(n), borrowed_ty(lent, &ty)));
                }
                inner.insert(n.clone());
            }
            let Some(result) = &m.result else {
                return fail(
                    path,
                    msg!(
                        "tauto-extract-member-has-no-result-type",
                        class = i.class.to_string(),
                        member = m.name.to_string()
                    ),
                );
            };
            let result = self.ty(path, result, &inner)?;
            let body = self.expr(path, &m.body, &inner, 2)?;
            let _ = writeln!(
                text,
                "  fn {}{}({}): {result} {{\n    {body}\n  }}",
                raw(&m.name),
                angle(&method_generics),
                params.join(", ")
            );
        }
        text.push_str("}\n");
        self.out.push_str(&text);
        Ok(())
    }

    fn ty(&self, path: &Path, t: &SurfaceTerm, locals: &Locals) -> Result<String, Message> {
        self.ty_in(path, t, locals, &HashMap::new())
    }

    /// `t` as a Nib type, with the parameters of the aliases being unfolded
    /// (`env`) read as the types they were given.
    fn ty_in(
        &self,
        path: &Path,
        t: &SurfaceTerm,
        locals: &Locals,
        env: &HashMap<Name, String>,
    ) -> Result<String, Message> {
        if is_unit(t) {
            return Ok("Unit".into());
        }
        match &*t.kind {
            // `A × B`: Nib's own product, its members in the order written (`A × Unit` is not `A`: `Unit` is a member like any other).
            TermKind::App { .. } if let Some(items) = t.product_type_members() => {
                let members = items
                    .iter()
                    .map(|m| self.ty_in(path, m, locals, env).map(|m| format!("({m})")))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(match members.len() {
                    0 => "Unit".into(),
                    _ => members.join(" × "),
                })
            }
            TermKind::Var(n) if env.contains_key(n) => Ok(env[n].clone()),
            TermKind::Var(n) if locals.contains(n) => Ok(n.to_string()),
            TermKind::Var(n) if self.aliases.contains_key(n) => self.unfold(path, n, Vec::new()),
            TermKind::Var(n) => self.type_name(path, n).map(|s| s.to_string()),
            TermKind::App {
                function,
                arguments,
            } => {
                let TermKind::Var(n) = &*function.kind else {
                    return fail(
                        path,
                        msg!("tauto-extract-a-type-is-not-extracted", ty = show(t)),
                    );
                };
                // A quotient is its representation: a program reads a value
                // of it only through `Quot_lift`, which respects the relation.
                if self.std.of(n) == Some("Quot")
                    && let [a, _] = &arguments[..]
                {
                    return self.ty_in(path, a, locals, env);
                }
                if !env.contains_key(n) && !locals.contains(n) && self.aliases.contains_key(n) {
                    let args = arguments
                        .iter()
                        .map(|a| self.ty_in(path, a, locals, env))
                        .collect::<Result<Vec<_>, _>>()?;
                    return self.unfold(path, n, args);
                }
                // `Pair(A, B)`: the elaborated form of a product, Nib's `A × B`.
                if self.std.of(n) == Some("Pair") && arguments.len() == 2 {
                    let members = arguments
                        .iter()
                        .map(|a| self.ty_in(path, a, locals, env).map(|m| format!("({m})")))
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(members.join(" × "));
                }
                if let Some(m) = self.mapped_type(n)
                    && is_width_family(m)
                {
                    return match mapped_width(m, explicit_args(arguments)) {
                        Some(native) => Ok(native.to_string()),
                        None => fail(
                            path,
                            msg!("tauto-extract-is-not-a-type-of", n = n.to_string()),
                        ),
                    };
                }
                let head = self.type_name(path, n)?;
                let kept = if let Some(m) = self.mapped_type(n) {
                    mapped_kept(m)
                } else {
                    self.kept_params(n)
                };
                let args = arguments
                    .iter()
                    .enumerate()
                    .filter(|(k, _)| kept.get(*k).copied().unwrap_or(true))
                    .map(|(_, a)| self.ty_in(path, a, locals, env))
                    .collect::<Result<Vec<_>, _>>()?;
                // The `struct &T` of a mapped type is the host's reference to it.
                let head = if self.std.of(n).is_some_and(|m| m.starts_with('&')) && self.mapped_type(n).is_some() {
                    format!("&{head}")
                } else {
                    head.to_string()
                };
                if args.is_empty() {
                    return Ok(head);
                }
                Ok(format!("{head}({})", args.join(", ")))
            }
            TermKind::Pi {
                params,
                result,
                effects,
                ..
            } => {
                let mut inner = locals.clone();
                let mut env = env.clone();
                let mut doms = Vec::new();
                for (n, d) in params {
                    doms.push(self.ty_in(path, d, &inner, &env)?);
                    if let Some(n) = n {
                        env.remove(n);
                        inner.insert(n.clone());
                    }
                }
                let row = match effects.as_deref() {
                    Some(row) if !row.is_empty() => format!(" ! {}", row_text(row)),
                    _ => String::new(),
                };
                Ok(format!(
                    "({}) -> {}{row}",
                    doms.join(", "),
                    self.ty_in(path, result, &inner, &env)?
                ))
            }
            // `affine (…) -> R`: Nib writes a function's kind the same way.
            TermKind::FnKind { kind, ty } => {
                Ok(format!("{kind} {}", self.ty_in(path, ty, locals, env)?))
            }
            // A borrowed parameter's type, as a class method's is (`&K`).
            TermKind::Borrow { mutable, term, .. } => Ok(format!(
                "{}{}",
                if *mutable { "&mut " } else { "&" },
                self.ty_in(path, term, locals, env)?
            )),
            // `@a T`: Nib's own label, a mark of the type.
            TermKind::Tagged { tag, term } => Ok(format!(
                "@{} {}",
                raw(tag),
                self.ty_in(path, term, locals, env)?
            )),
            _ => fail(
                path,
                msg!("tauto-extract-a-type-is-not-extracted", ty = show(t)),
            ),
        }
    }

    /// The alias `n` given `args`, as the type its body names.
    fn unfold(&self, path: &Path, n: &Name, args: Vec<String>) -> Result<String, Message> {
        let f = &self.aliases[n];
        if f.params.len() != args.len() {
            return fail(
                path,
                msg!(
                    "tauto-extract-is-given-types-for-parameters",
                    n = n.to_string(),
                    count = args.len(),
                    params = f.params.len()
                ),
            );
        }
        let mut body = &f.body;
        while let TermKind::Block(stmts) = &*body.kind {
            match stmts.as_slice() {
                [Stmt::Expr(e)] => body = e,
                _ => {
                    return fail(
                        path,
                        msg!("tauto-extract-a-type-alias-s-body", n = n.to_string()),
                    );
                }
            }
        }
        let env = f.params.iter().cloned().zip(args).collect();
        self.ty_in(path, body, &Locals::new(), &env)
    }

    /// The builtin of Nib a family of the standard library is mapped onto.
    fn mapped_type(&self, n: &Name) -> Option<&'static str> {
        self.std.of(n).and_then(mapped_type)
    }

    fn type_name<'s>(&self, path: &Path, n: &'s Name) -> Result<&'s str, Message> {
        if let Some(m) = self.mapped_type(n) {
            return Ok(m);
        }
        // A field of an `inductive enum` names Nib's
        // own type (`u64`), which the kernel reads as its family (`U64`).
        let bare = crate::surface::qualify::short(n);
        if tauto_surface::inductive_data::proof_type(bare).is_some()
            && (crate::bindings::is_library(n, bare) || self.std.of(n).is_some())
        {
            return Ok(bare);
        }
        match self.checked.families.get(n) {
            Some(f) if !f.prop && !f.predicate => Ok(n),
            _ => fail(
                path,
                msg!("tauto-extract-is-not-a-type-of", n = n.to_string()),
            ),
        }
    }

    /// The name a local `n` is written with where it is bound. A local may
    /// not have the name of a module visible where it is, and the program is
    /// written in modules named by the paths of its declarations
    /// (`module m { module src { … } }`), so a local named as a segment of
    /// such a path is written with a fresh name, the same at its binders and
    /// its uses.
    fn local(&mut self, n: &str) -> String {
        if let Some(m) = self.module_locals.get(n) {
            return m.clone();
        }
        if !self.module_segments.contains(n) {
            return raw(n);
        }
        let m = self.fresh(n).to_string();
        self.module_locals.insert(n.to_string(), m.clone());
        m
    }

    /// A local `n` as an expression ([`local_name`]), under the name
    /// [`Extractor::local`] binds it with.
    fn local_use(&mut self, n: &str) -> String {
        if self.module_segments.contains(n) {
            self.local(n)
        } else {
            local_name(n)
        }
    }

    fn fresh(&mut self, base: &str) -> Name {
        self.fresh += 1;
        Name::from(tauto_surface::identity::LocalRef::fresh(format!(
            "{base}_x{}",
            self.fresh
        )))
    }

    /// `t` as the subject of a `match`: in parentheses unless it is a name,
    /// so that a record it builds (`Item { value: 42 }`) is not read as the
    /// arms of the `match`.
    fn subject(
        &mut self,
        path: &Path,
        t: &SurfaceTerm,
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        let s = self.expr(path, t, locals, depth)?;
        Ok(match &*t.kind {
            TermKind::Var(_) => s,
            _ => format!("({s})"),
        })
    }

    /// `t` as a Nib expression, `depth` levels of indentation in.
    fn expr(
        &mut self,
        path: &Path,
        t: &SurfaceTerm,
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        if is_unit(t) {
            return Ok("#()".into());
        }
        match &*t.kind {
            // `A × B` where a type is passed as a value.
            TermKind::App { .. } if let Some(_) = t.product_type_members() => {
                self.ty(path, t, locals)
            }
            // `#(a, b)`: Nib's own product, its members in the order written.
            TermKind::App { .. } if let Some(items) = t.product_value_members() => {
                let items = items
                    .iter()
                    .map(|a| self.expr(path, a, locals, depth))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("#({})", items.join(", ")))
            }
            TermKind::Nat(n) => Ok(n.clone()),
            TermKind::Bool(b) => Ok(b.to_string()),
            TermKind::Float(x) => Ok(x.clone()),
            TermKind::Text(s) => Ok(text_literal(s)),
            // A place lent to a call: `&mut x`, `&mut x.f`.
            TermKind::Borrow { mutable, term, .. } => {
                let place = match &*term.kind {
                    TermKind::Var(x) => self.local(x),
                    TermKind::Field { base, name } => match &*base.kind {
                        TermKind::Var(x) => format!("{}.{}", self.local(x), raw(name)),
                        _ => {
                            return fail(
                                path,
                                msg!("tauto-extract-is-not-extracted", ty = show(t)),
                            );
                        }
                    },
                    _ => self.expr(path, term, locals, depth)?,
                };
                Ok(format!("{}{place}", if *mutable { "&mut " } else { "&" }))
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                let c = self.expr(path, condition, locals, depth)?;
                let a = self.expr(path, then, locals, depth + 1)?;
                let mut out = format!("if {c} {}", braces(&[a], depth));
                if let Some(b) = otherwise {
                    let b = self.expr(path, b, locals, depth + 1)?;
                    out.push_str(&format!(" else {}", braces(&[b], depth)));
                }
                Ok(out)
            }
            TermKind::Var(n) if locals.contains(n) => Ok(self.local_use(n)),
            TermKind::Var(n) if self.thunks.contains(n) => Ok(local_name(n)),
            TermKind::Var(n) => self.global(path, n, &[], Some(t.id()), locals, depth),
            TermKind::App {
                function,
                arguments,
            } => match &*function.kind {
                // `Cons(a, Cons(b, Nil))` is written back as `[a, b]`, which
                // the parser reads as the same terms: a long list nested as
                // calls would be deeper than any source is allowed to be.
                TermKind::Var(n)
                    if crate::bindings::is_library(&n, "Cons") && !locals.contains(n) =>
                {
                    match list_items(t, locals) {
                        Some(items) => {
                            let items = items
                                .into_iter()
                                .map(|a| self.expr(path, a, locals, depth))
                                .collect::<Result<Vec<_>, _>>()?;
                            Ok(format!("[{}]", items.join(", ")))
                        }
                        None => self.global(path, n, arguments, Some(t.id()), locals, depth),
                    }
                }
                TermKind::Var(n) if !locals.contains(n) => {
                    self.app_id = Some(t.id());
                    self.global(path, n, arguments, Some(t.id()), locals, depth)
                }
                // `C::m(…)`: a method of a class.
                TermKind::Field { base, name } if matches!(&*base.kind, TermKind::Var(c) if !locals.contains(c) && self.checked.classes.contains(c)) =>
                {
                    let TermKind::Var(c) = &*base.kind else {
                        unreachable!()
                    };
                    // A mapped class's methods borrow their arguments; one
                    // written already lent (`Ord::compare(&a, &b)`) is lent once.
                    let args = arguments
                        .iter()
                        .map(|a| {
                            let lent = self.std.of(c).is_some_and(mapped_class)
                                && !matches!(&*a.kind, TermKind::Borrow { .. });
                            self.expr(path, a, locals, depth)
                                .map(|a| if lent { format!("&{a}") } else { a })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(format!("{c}::{}({})", raw(name), args.join(", ")))
                }
                // `match x: (P, …) -> R { … }(h, …)`: the parameters of the
                // result that are propositions are erased in the arms and in
                // the arguments alike, as the checker typed them.
                TermKind::Match {
                    scrutinee,
                    result: Some(motive),
                    arms,
                    ..
                } if matches!(&*motive.kind, TermKind::Pi { params, .. }
                    if params.iter().any(|(_, t)| self.is_prop(t))) =>
                {
                    let TermKind::Pi { params, .. } = &*motive.kind else {
                        unreachable!()
                    };
                    let erased: Vec<bool> = params.iter().map(|(_, t)| self.is_prop(t)).collect();
                    if arguments.len() != erased.len() {
                        return fail(path, msg!("tauto-extract-a-match-whose-result-takes"));
                    }
                    let mut stripped = Vec::new();
                    for arm in arms {
                        let TermKind::Lam {
                            params: names,
                            body,
                            types,
                            ..
                        } = &*arm.body.kind
                        else {
                            return fail(path, msg!("tauto-extract-arm-is-lambda"));
                        };
                        if names.len() != erased.len() {
                            return fail(path, msg!("tauto-extract-arm-binds-parameters"));
                        }
                        let keep = |k: &usize| !erased[*k];
                        let mut arm = arm.clone();
                        arm.body = if erased.iter().all(|e| *e) {
                            (**body).clone()
                        } else {
                            arm.body.with_kind(
                                TermKind::Lam {
                                    params: (0..names.len())
                                        .filter(keep)
                                        .map(|k| names[k].clone())
                                        .collect(),
                                    unused_params: Vec::new(),
                                    body: body.clone(),
                                    types: if types.is_empty() {
                                        Vec::new()
                                    } else {
                                        (0..types.len())
                                            .filter(keep)
                                            .map(|k| types[k].clone())
                                            .collect()
                                    },
                                },
                                arm.body.span,
                            )
                        };
                        stripped.push(arm);
                    }
                    let f = self.matching(path, scrutinee, &stripped, locals, depth)?;
                    let args = arguments
                        .iter()
                        .zip(&erased)
                        .filter(|(_, e)| !**e)
                        .map(|(a, _)| self.expr(path, a, locals, depth))
                        .collect::<Result<Vec<_>, _>>()?;
                    if args.is_empty() {
                        Ok(f)
                    } else {
                        Ok(format!("({f})({})", args.join(", ")))
                    }
                }
                _ => {
                    let f = self.expr(path, function, locals, depth)?;
                    let args = arguments
                        .iter()
                        .map(|a| self.expr(path, a, locals, depth))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(format!("({f})({})", args.join(", ")))
                }
            },
            TermKind::BorrowLam { borrows, lam } => match &*lam.kind {
                TermKind::Lam {
                    params,
                    body,
                    types,
                    ..
                } => self.lambda(path, params, types, borrows, body, locals, depth),
                _ => fail(path, msg!("tauto-extract-is-not-extracted", ty = show(t))),
            },
            TermKind::Lam {
                params,
                body,
                types,
                ..
            } => self.lambda(path, params, types, &[], body, locals, depth),
            TermKind::Match {
                scrutinee, arms, ..
            } => self.matching(path, scrutinee, arms, locals, depth),
            TermKind::Block(stmts) => self.block(path, stmts, locals, depth),
            TermKind::Field { base, name } => self.field(path, t.id(), base, name, locals, depth),
            TermKind::Perform { effect, args } => {
                let args = args
                    .iter()
                    .map(|a| self.expr(path, a, locals, depth))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("perform {}({})", raw(effect), args.join(", ")))
            }
            TermKind::Handle { body, handlers } => self.handle(path, body, handlers, locals, depth),
            // `@a e`: Nib's own label, which leaves the value as it is.
            TermKind::Tagged { tag, term } => Ok(format!(
                "@{} ({})",
                raw(tag),
                self.expr(path, term, locals, depth)?
            )),
            // `(e: T)`: Nib takes the members `T` names out of a product, as the proof does.
            TermKind::Ascribe { term, ty } => Ok(format!(
                "({}: {})",
                self.expr(path, term, locals, depth)?,
                self.ty(path, ty, locals)?
            )),
            _ => fail(path, msg!("tauto-extract-is-not-extracted", ty = show(t))),
        }
    }

    /// `handle { body } with { … }`: arms whose patterns are names.
    fn handle(
        &mut self,
        path: &Path,
        body: &SurfaceTerm,
        handlers: &[crate::surface::Handler],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        use crate::surface::Handler;
        fn name(path: &Path, p: &Pattern) -> Result<Name, Message> {
            match p {
                Pattern::Bind { name: n, .. } => Ok(n.clone()),
                Pattern::Wild => Ok("_".into()),
                _ => fail(path, msg!("tauto-extract-a-handler-arm-s-pattern")),
            }
        }
        let b = self.expr(path, body, locals, depth + 1)?;
        let pad = "  ".repeat(depth + 1);
        let mut arms = Vec::new();
        for h in handlers {
            let mut inner = locals.clone();
            match h {
                Handler::Return { pattern, body } => {
                    let x = name(path, pattern)?;
                    inner.insert(x.clone());
                    let e = self.expr(path, body, &inner, depth + 1)?;
                    let x = self.local(&x);
                    arms.push(format!("{pad}return {x} => {e}"));
                }
                Handler::Operation {
                    effect,
                    patterns,
                    cont,
                    guard,
                    body,
                    ..
                } => {
                    if guard.is_some() {
                        return fail(path, msg!("tauto-extract-a-guard-on-a-handler"));
                    }
                    let xs = patterns
                        .iter()
                        .map(|p| name(path, p))
                        .collect::<Result<Vec<_>, _>>()?;
                    inner.extend(xs.iter().cloned());
                    let k = cont.clone().unwrap_or_else(|| "_".into());
                    inner.insert(k.clone());
                    let e = self.expr(path, body, &inner, depth + 1)?;
                    let xs: Vec<String> = xs.iter().map(|x| self.local(x)).collect();
                    let k = self.local(&k);
                    arms.push(format!(
                        "{pad}{}({}), {k} => {e}",
                        raw(effect),
                        xs.join(", ")
                    ));
                }
            }
        }
        let end = "  ".repeat(depth);
        Ok(format!(
            "handle {} with {{\n{}\n{end}}}",
            braces(&[b], depth),
            arms.join("\n")
        ))
    }

    /// `x.f`: Nib's own field for a mapped record (`Pair`), else a match on
    /// the one constructor of the family that has the field.
    fn field(
        &mut self,
        path: &Path,
        occurrence: crate::surface::TermId,
        base: &SurfaceTerm,
        name: &str,
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        let selections = self.field_selections.get_or_insert_with(|| {
            let mut selections: HashMap<_, HashSet<_>> = HashMap::new();
            for site in &self.checked.field_sites {
                selections
                    .entry(site.occurrence)
                    .or_default()
                    .insert(site.family.clone());
            }
            selections
        });
        let selected = selections.get(&occurrence);
        let owners: Vec<(Name, (Name, Vec<Name>))> = self
            .checked
            .records
            .iter()
            .filter(|(family, (_, fs))| {
                !self.checked.props.contains(*family)
                    && selected.is_none_or(|selected| selected.contains(*family))
                    && fs.iter().any(|f| f.as_str() == name)
            })
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        // A struct's field Nib reads itself, by the type it infers, so
        // records that share a field name are told apart there.
        if !owners.is_empty()
            && owners.iter().all(|(family, (ctor, _))| {
                self.mapped_type(family).is_some() || self.struct_fields(ctor).is_some()
            })
        {
            let b = self.expr(path, base, locals, depth)?;
            return Ok(format!("({b}).{}", raw(name)));
        }
        let [(_, (ctor, fields))] = owners.as_slice() else {
            return fail(path, msg!("tauto-extract-is-a-field-of-no", name = name));
        };
        let var = Name::from(tauto_surface::identity::LocalRef::fresh(format!(
            "extract_{name}"
        )));
        let arm = MatchArm {
            goal: None,
            pattern: Pattern::Ctor {
                name: ctor.clone(),
                args: fields
                    .iter()
                    .map(|f| match f.as_str() == name {
                        true => Pattern::Bind { name: var.clone(), unused: None },
                        false => Pattern::Wild,
                    })
                    .collect(),
            },
            guard: None,
            body: SurfaceTerm::new(TermKind::Var(var), base.span),
        };
        self.matching(path, base, &[arm], locals, depth)
    }

    fn block(
        &mut self,
        path: &Path,
        stmts: &[Stmt],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        // A block that ends with a statement is `()`.
        let (last, lets) = match stmts.split_last() {
            Some((Stmt::Expr(last), lets)) => (Some(last), lets),
            _ => (None, stmts),
        };
        let mut inner = locals.clone();
        let mut lines = Vec::new();
        for s in lets {
            match s {
                Stmt::Let {
                    name, ty, value, ..
                } => {
                    if !ty.as_ref().is_some_and(|ty| self.is_prop(ty)) {
                        let v = self.expr(path, value, &inner, depth + 1)?;
                        // The type written can be what fixes a generic of
                        // the value (`let x: Box(Nat) = empty()`).
                        let ty = ty.as_ref().map(|ty| self.ty(path, ty, &inner));
                        let x = self.local(name);
                        match ty {
                            Some(Ok(ty)) => lines.push(format!("let {x}: {ty} := {v}")),
                            _ => lines.push(format!("let {x} := {v}")),
                        }
                    }
                    inner.insert(name.clone());
                }
                Stmt::Var {
                    stack: _,
                    name,
                    ty,
                    value,
                    borrow: false,
                    unused: None,
                } => {
                    let v = self.expr(path, value, &inner, depth + 1)?;
                    let x = self.local(name);
                    match ty {
                        Some(ty) => {
                            let ty = self.ty(path, ty, &inner)?;
                            lines.push(format!("var {x}: {ty} := {v}"))
                        }
                        None => lines.push(format!("var {x} := {v}")),
                    }
                    inner.insert(name.clone());
                }
                Stmt::Assign {
                    name,
                    place,
                    value,
                    deref,
                } => {
                    let v = self.expr(path, value, &inner, depth + 1)?;
                    let target = match place {
                        Some(p) => self.expr(path, p, &inner, depth + 1)?,
                        None => self.local(name),
                    };
                    let star = if deref.is_some() { "*" } else { "" };
                    lines.push(format!("{star}{target} := {v}"));
                }
                Stmt::Expr(e) => lines.push(self.expr(path, e, &inner, depth + 1)?),
                _ => {
                    return fail(path, msg!("tauto-extract-a-block-holds-only-let"));
                }
            }
        }
        if let Some(last) = last {
            lines.push(self.expr(path, last, &inner, depth + 1)?);
        }
        Ok(braces(&lines, depth))
    }

    /// Whether `ty` is a proposition: its head (under `∀`) makes one.
    fn is_prop(&self, ty: &SurfaceTerm) -> bool {
        match &*ty.kind {
            TermKind::Pi { result, .. } => self.is_prop(result),
            TermKind::Var(n) => {
                self.checked.props.contains(n)
                    || n.sort_symbol() == Some(crate::identity::SortSymbol::Proposition)
                    || crate::bindings::is_library(n, "=")
            }
            TermKind::App { function, .. } => self.is_prop(function),
            _ => false,
        }
    }

    fn global(
        &mut self,
        path: &Path,
        n: &Name,
        args: &[SurfaceTerm],
        occurrence: Option<crate::surface::TermId>,
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        if crate::bindings::is_library(n, n.as_str())
            && matches!(
                n.as_str(),
                "+" | "*" | "<" | "<=" | ">" | ">=" | "&&" | "||" | "==" | "!="
            )
        {
            let [a, b] = args else {
                return fail(
                    path,
                    msg!("tauto-extract-takes-two-arguments", n = n.to_string()),
                );
            };
            let a = self.expr(path, a, locals, depth)?;
            let b = self.expr(path, b, locals, depth)?;
            return Ok(format!("({a} {n} {b})"));
        }
        // An operator the kernel read at a fixed width (`a - b` at `UInt(64)`
        // is `UInt::sub_or_overflow64(a, b)`, `check/machine.rs` in the
        // kernel crate) is that function, which is Nib's own operator.
        if (crate::bindings::is_library(n, "-")
            || crate::bindings::is_library_selected(n, "div")
            || crate::bindings::is_library_selected(n, "mod"))
            && let Some(id) = occurrence
            && let Some(callee) = self
                .checked
                .sites_at(id)
                .map(|site| site.callee.clone())
                .find(|callee| callee != n && self.std.of(callee).is_some_and(width_function))
        {
            // `-1` at a width is that width's literal, which Nib reads as one.
            if let [a] = args
                && let TermKind::Nat(v) = &*a.kind
                && width_literal(self.std.of(&callee))
            {
                return Ok(format!("(-{v})"));
            }
            return self.global(path, &callee, args, None, locals, depth);
        }
        if crate::bindings::is_library(n, "-") {
            // `-a`: the negative of an integer (`-2147483648`). The program
            // language reads `-5` as an `i64`, so it is `Int::neg` of the
            // literal, which is the integer the proofs mean.
            if let [a] = args {
                let a = self.int_operand(path, a, locals, depth)?;
                let negate = self
                    .std
                    .std
                    .iter()
                    .find(|name| self.std.of(name) == Some("Int::neg"))
                    .ok_or("integer negation has no checked declaration")?;
                self.dependencies.insert(negate.clone());
                return Ok(format!("Int::neg({a})"));
            }
            let [a, b] = args else {
                return fail(path, msg!("tauto-extract-minus-takes-two-arguments"));
            };
            let a = self.expr(path, a, locals, depth)?;
            let b = self.expr(path, b, locals, depth)?;
            return Ok(format!("extract_nat_sub({a}, {b})"));
        }
        if crate::bindings::is_library(&n, "the") {
            let Some(last) = args.last() else {
                return fail(path, msg!("tauto-extract-the-takes-a-type-and"));
            };
            return self.expr(path, last, locals, depth);
        }
        let Some(mut sig) = self.checked.source_call_signature(n) else {
            return fail(
                path,
                msg!("tauto-extract-is-not-a-declaration-that", n = n.to_string()),
            );
        };
        // `f(<x: v>, a)`: the implicit arguments written by name, put in the
        // order of the telescope when each one is written.
        let ordered = positional_args(args, sig.names.get(..sig.implicit).unwrap_or_default());
        let args = &ordered[..];
        // The policy of a `SlotsModel` operation is implicit: the checker
        // recorded the values it fixed at this call.
        let app_id = self.app_id.take();
        let policy_handled = self.std.of(n).is_some_and(|m| m.starts_with("SlotsModel::"))
            && self.std.of(n).and_then(mapped_fn).is_some();
        let policy = if policy_handled {
            let written = args.len();
            let site = app_id
                .and_then(|id| {
                    self.checked
                        .sites_at(id)
                        .find(|s| s.written == written && &s.callee == n)
                })
                .ok_or_else(|| {
                    Message::from(format!(
                        "extract: no application site for the SlotsModel call `{n}`"
                    ))
                })?;
            let mut values = Vec::new();
            for (a, r) in site.arguments.iter().zip(&sig.params[..sig.implicit]) {
                if *r == Role::Value {
                    values.push(self.expr(path, a, locals, depth)?);
                }
            }
            values
        } else {
            Vec::new()
        };
        // A constructor is built from its fields: the family's parameters,
        // values among them, are not passed.
        if let Some((_, fam)) = self.checked.family_of_ctor(n) {
            for r in &mut sig.params[..fam.params] {
                if *r == Role::Value {
                    *r = Role::Proof;
                }
            }
        }
        if sig.result != Role::Value {
            return fail(
                path,
                msg!("tauto-extract-is-used-as-a-value", n = n.to_string()),
            );
        }
        // The arguments as the kernel has them: the implicit ones left out
        // are the leading ones. When an implicit prefix still carries Value
        // slots (class dictionaries), recover them from the checked
        // application site so exclusive method calls keep their instance.
        let inserted = occurrence.and_then(|id| {
            let mut choices = self
                .checked
                .sites_at(id)
                .filter(|site| site.written == args.len() && site.callee == *n)
                .map(|site| &site.arguments);
            let first = choices.next()?;
            if choices.any(|args| {
                args.len() != first.len()
                    || args
                        .iter()
                        .zip(first.iter())
                        .any(|(a, b)| !tauto_kernel::check::same_up_to_binders(a, b))
            }) {
                return None;
            }
            Some(first.as_slice())
        });
        let (prefix, roles): (Vec<&SurfaceTerm>, &[Role]) = if args.len() == sig.params.len() {
            (Vec::new(), &sig.params)
        } else if args.len() + sig.implicit == sig.params.len() {
            let implicit = &sig.params[..sig.implicit];
            // The policy of a `SlotsModel` operation is already emitted above.
            if !policy_handled && implicit.iter().any(|r| *r == Role::Value) {
                let Some(prefix) = inserted else {
                    return fail(
                        path,
                        msg!(
                            "tauto-extract-is-applied-to-arguments-write",
                            n = n.to_string(),
                            count = args.len()
                        ),
                    );
                };
                (
                    prefix.iter().collect(),
                    &sig.params[..],
                )
            } else {
                (Vec::new(), &sig.params[sig.implicit..])
            }
        } else if args.is_empty() {
            (Vec::new(), &[])
        } else {
            return fail(
                path,
                msg!(
                    "tauto-extract-is-applied-to-arguments-write",
                    n = n.to_string(),
                    count = args.len()
                ),
            );
        };
        let supplied: Vec<&SurfaceTerm> = prefix.into_iter().chain(args.iter()).collect();
        // The standard library's `Int::` functions take integers, and a
        // literal among their arguments is a natural number the program
        // language does not read as an `Int`.
        let int_fn = !self.is_ctor(n) && self.std.of(n).is_some_and(|m| m.starts_with("Int::"));
        // `C::m(…)` of a mapped class: its methods borrow their arguments,
        // and one written already lent (`Ord::compare(&a, &b)`) is lent once.
        let lends = self
            .checked
            .class_members
            .get(n)
            .is_some_and(|c| self.std.of(c).is_some_and(mapped_class));
        let mut values = Vec::new();
        let first = sig.params.len() - roles.len();
        for (i, (a, r)) in supplied.iter().zip(roles).enumerate() {
            if *r == Role::Value {
                let lent = self.std.lends_argument(
                    n,
                    first + i,
                    sig.params.len(),
                    a,
                    &self.lent_locals.borrow(),
                );
                let v = if int_fn {
                    self.int_operand(path, a, locals, depth)?
                } else {
                    self.expr(path, a, locals, depth)?
                };
                values.push(if (lends || lent) && !matches!(&*a.kind, TermKind::Borrow { .. }) {
                    format!("&{v}")
                } else {
                    v
                });
            }
        }
        let values: Vec<String> = policy.into_iter().chain(values).collect();
        let wanted = sig.params.iter().filter(|r| **r == Role::Value).count();
        if args.is_empty() && wanted > 0 {
            if self
                .checked
                .class_members
                .get(n)
                .is_some_and(|class| self.std.native_key_class(class))
            {
                return Ok(raw(n));
            }
            // Used as a function value.
            let xs: Vec<String> = (0..wanted).map(|_| self.fresh("a").to_string()).collect();
            let call = self.call(path, n, &xs)?;
            return Ok(format!("({}) => {call}", xs.join(", ")));
        }
        self.call(path, n, &values)
    }

    /// `t` as an `Int`: a numeral is `IntOfNat` of it.
    fn int_operand(
        &mut self,
        path: &Path,
        t: &SurfaceTerm,
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        match &*t.kind {
            TermKind::Nat(n) => Ok(format!("IntOfNat({n})")),
            _ => self.expr(path, t, locals, depth),
        }
    }

    /// `n` applied to the value arguments `values`.
    fn call(&mut self, path: &Path, n: &Name, values: &[String]) -> Result<String, Message> {
        if let Some(c) = self.std.of(n).and_then(|m| mapped_ctor(m, values)) {
            return Ok(c);
        }
        // The standard library's constructor of `Text`, by its full name.
        if let [bytes] = values
            && self
                .checked
                .family_of_ctor(n)
                .is_some_and(|(family, _)| self.std.of(family) == Some("Text"))
        {
            return Ok(format!("extract_text_of_bytes({bytes})"));
        }

        if self.checked.family_of_ctor(n).is_some_and(|(name, _)| {
            matches!(
                self.std.of(name).unwrap_or(""),
                "Text"
                    | "Array"
                    | "Bytes"
                    | "Stack"
                    | "UInt"
                    | "UHost"
                    | "SInt"
                    | "Float"
                    | "Float32"
            )
        }) {
            return fail(
                path,
                msg!(
                    "tauto-extract-has-no-executable-constructor-representation",
                    n = n.to_string()
                ),
            );
        }
        if let Some((family, names)) = self.struct_fields(n) {
            let fields: Vec<String> = names
                .iter()
                .zip(values)
                .map(|(f, v)| format!("{}: {v}", raw(f)))
                .collect();
            return Ok(format!("{family} {{ {} }}", fields.join(", ")));
        }
        if let Some(m) = self.std.of(n)
            && let Some(folded) = literal_shift(m, values)
        {
            return Ok(folded);
        }
        if let Some(template) = self.std.of(n).and_then(mapped_fn) {
            self.template_dependencies(template)?;
            return Ok(format!("({})", fill(template, values)));
        }
        if is_eliminator(n) {
            return fail(
                path,
                msg!("tauto-extract-is-an-eliminator-write-a", n = n.to_string()),
            );
        }
        if self.checked.ghosts.contains(n) {
            return fail(
                path,
                msg!("tauto-extract-ghost-fn-is-not-run", n = n.to_string()),
            );
        }
        self.dependencies.insert(n.clone());
        let is_ctor = self.checked.is_ctor(n);
        if is_ctor && values.is_empty() {
            return Ok(self.ctor_ref(n));
        }
        if is_ctor {
            return Ok(format!("{}({})", self.ctor_ref(n), values.join(", ")));
        }
        let written = written_path(n.as_str(), &self.file_modules);
        Ok(format!("{}({})", raw(written), values.join(", ")))
    }

    /// Compiler templates contribute their checked standard declarations to
    /// reachability, even when the source function's body is replaced.
    fn template_dependencies(&mut self, template: &str) -> Result<(), Message> {
        let slots = template
            .split('$')
            .skip(1)
            .filter_map(|tail| {
                tail.split(|c: char| !c.is_ascii_digit())
                    .next()?
                    .parse::<usize>()
                    .ok()
            })
            .max()
            .map_or(0, |index| index + 1);
        let source = fill(template, &vec!["0".into(); slots]);
        let mut program = tauto_parse::parse_program_unresolved_at(&source, 0)?;
        if let Some((error, _)) = program.errors.first() {
            return Err(error.clone());
        }
        for statement in &mut program.stmts {
            crate::surface::walk::stmt(statement, &mut |term| {
                let TermKind::Var(reference) = &*term.kind else {
                    return;
                };
                for declaration in &self.std.std {
                    if self.std.of(declaration) == Some(reference.as_str()) {
                        self.dependencies.insert(declaration.clone());
                    }
                }
            });
        }
        Ok(())
    }

    /// The path of a variant that kept its short name inside a type written
    /// out in modules: when the type was renamed to its full name (a
    /// program's `Pending` against the prelude's) it is declared inside the
    /// modules of that name, which the bare variant does not find.
    fn qualified_ctor(&self, n: &Name) -> Option<String> {
        if n.contains(['.', ':']) || !self.written.contains(n) {
            return None;
        }
        let (family, _) = self
            .checked
            .families
            .iter()
            .find(|(_, f)| f.ctors.iter().any(|c| c == n))?;
        // The family is declared inside the modules of its name
        // (`in_modules_text`), the file's module included: that name is the
        // path.
        family
            .contains("::")
            .then(|| format!("{family}::{}", raw(n)))
    }

    /// The constructor is referenced through the family that owns it in
    /// the executable declaration table.
    fn ctor_ref(&self, n: &Name) -> String {
        extracted_ctor(self.checked, n)
            .map(|n| n.to_string())
            .unwrap_or_else(|| raw(n))
    }

    /// `(x: A, y: &B) => body`: a written parameter type is kept, as Nib
    /// reads a lambda's parameters before the arguments that would tell them,
    /// and a borrowed parameter keeps its `&` or `&mut`.
    #[allow(clippy::too_many_arguments)]
    fn lambda(
        &mut self,
        path: &Path,
        params: &[Name],
        types: &[Option<SurfaceTerm>],
        borrows: &[Option<bool>],
        body: &SurfaceTerm,
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        let mut shown = Vec::new();
        let mut added = Vec::new();
        for (k, p) in params.iter().enumerate() {
            let mark = match borrows.get(k).copied().flatten() {
                Some(true) => "&mut ",
                Some(false) => {
                    if self.lent_locals.borrow_mut().insert(p.clone()) {
                        added.push(p.clone());
                    }
                    "&"
                }
                None => "",
            };
            match types.get(k).and_then(|t| t.as_ref()) {
                Some(t) => match self.ty_in(path, t, locals, &HashMap::new()) {
                    Ok(t) => shown.push(format!("{}: {}", self.local(p), borrowed_ty(mark, &t))),
                    // The borrow comes from the type the closure is expected to have.
                    Err(_) => shown.push(self.local(p).to_string()),
                },
                None => shown.push(self.local(p).to_string()),
            }
        }
        let mut inner = locals.clone();
        inner.extend(params.iter().cloned());
        let body = self.expr(path, body, &inner, depth)?;
        let mut lent = self.lent_locals.borrow_mut();
        for p in added {
            lent.remove(&p);
        }
        Ok(format!("({}) => {body}", shown.join(", ")))
    }

    fn matching(
        &mut self,
        path: &Path,
        scrutinee: &SurfaceTerm,
        arms: &[MatchArm],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        // A constructor written by its short name is the one the kernel read it as
        // (`Checked::ctor_sites`), not the first declaration with that spelling.
        let named: Vec<MatchArm>;
        let arms = if self.checked.ctor_sites.is_empty() {
            arms
        } else {
            named = arms
                .iter()
                .map(|a| {
                    let notes: Vec<&CtorSite> = self
                        .checked
                        .ctor_sites
                        .iter()
                        .filter(|s| !s.expression && s.occurrence == a.body.id())
                        .collect();
                    MatchArm {
                        pattern: self.kernel_named(&a.pattern, &notes, &mut 0),
                        ..a.clone()
                    }
                })
                .collect();
            &named[..]
        };
        // `@a p`: the labels come off the value's type in Nib as in the kernel. The
        // value is bound under them once (`match s { @a v => … }`) and the patterns
        // under them are matched against `v`, at the type the kernel gave `p`.
        if let Some(head) = arms.iter().find(|a| a.pattern.label().is_some()) {
            let mut tags = Vec::new();
            let mut p = &head.pattern;
            while let Some((tag, inner)) = p.label() {
                tags.push(format!("@{} ", raw(tag)));
                p = inner;
            }
            let unlabelled: Vec<MatchArm> = arms
                .iter()
                .map(|a| MatchArm {
                    pattern: unlabel(&a.pattern),
                    ..a.clone()
                })
                .collect();
            let s = self.subject(path, scrutinee, locals, depth + 1)?;
            let v = self.fresh("unlabelled");
            let mut inner = locals.clone();
            inner.insert(v.clone());
            let under = SurfaceTerm::var(&v, scrutinee.span);
            let body = self.matching(path, &under, &unlabelled, &inner, depth + 1)?;
            let pad = "  ".repeat(depth + 1);
            let end = "  ".repeat(depth);
            return Ok(format!(
                "match {s} {{\n{pad}{}{} => {body}\n{end}}}",
                tags.concat(),
                raw(&v)
            ));
        }
        // Guards are the `match`es on `Bool` the kernel read them as.
        if arms.iter().any(|a| a.guard.is_some()) {
            let chain = crate::check::guard_chain(scrutinee, None, None, arms, scrutinee.span);
            return self.expr(path, &chain, locals, depth);
        }
        // `false` and `true` are the constructors of `Bool`, as the kernel
        // reads them.
        let read: Vec<MatchArm>;
        let arms = if arms.iter().any(|a| has_bool(&a.pattern)) {
            read = arms
                .iter()
                .map(|a| MatchArm {
                    pattern: bool_constructors(&a.pattern),
                    ..a.clone()
                })
                .collect();
            &read[..]
        } else {
            arms
        };
        let family = arms
            .iter()
            .find_map(|a| self.pattern_family(&a.pattern))
            .unwrap_or_default();
        if self.checked.families.get(&family).is_some_and(|f| f.prop) || arms.is_empty() {
            // A proof is matched only to fix types: its one arm is the value.
            return match arms {
                [] => Ok("extract_unreachable()".into()),
                [arm] => {
                    let mut inner = locals.clone();
                    pattern_names(&arm.pattern, &mut inner);
                    self.expr(path, &arm.body, &inner, depth)
                }
                _ => fail(path, msg!("tauto-extract-a-match-on-a-proof")),
            };
        }
        // `Text::Mk(bs)` binds the bytes of the text.
        if crate::bindings::is_library(&family, "Text")
            && let [arm] = arms
            && arm.guard.is_none()
            && let Pattern::Ctor { args, .. } = &arm.pattern
            && let [inner_pat] = args.as_slice()
        {
            let s = self.subject(path, scrutinee, locals, depth + 1)?;
            let mut inner = locals.clone();
            let bytes = match inner_pat {
                Pattern::Bind { name: n, .. } if !self.is_ctor(n) => n.clone(),
                Pattern::Wild => self.fresh("bytes"),
                _ => return fail(path, msg!("tauto-extract-a-match-on-text-binds")),
            };
            inner.insert(bytes.clone());
            let body = self.expr(path, &arm.body, &inner, depth + 1)?;
            return Ok(braces(
                &[
                    format!("let {} := extract_text_bytes({s})", self.local(&bytes)),
                    body,
                ],
                depth,
            ));
        }
        if self.std.of(&family) == Some("Secret") {
            return fail(path, msg!("tauto-extract-match-on-secret"));
        }
        if matches!(
            self.std.of(&family).unwrap_or(""),
            "Text"
                | "Array"
                | "Bytes"
                | "Stack"
                | "UInt"
                | "UHost"
                | "SInt"
                | "Float"
                | "Float32"
        ) {
            return fail(
                path,
                msg!(
                    "tauto-extract-a-match-on-has-no",
                    family = family.to_string()
                ),
            );
        }
        let s = self.subject(path, scrutinee, locals, depth + 1)?;
        if matches!(self.std.of(&family), Some("Nat" | "Bool")) {
            return self.chain(path, &s, arms, locals, depth);
        }
        if let Some(out) = self.shaped(path, &s, arms, locals, depth)? {
            return Ok(out);
        }
        let mut lines = Vec::new();
        for arm in arms {
            if arm.guard.is_some() {
                return fail(path, msg!("tauto-extract-a-guard-is-not-extracted"));
            }
            let mut inner = locals.clone();
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            let pat = self.nib_pattern(path, &arm.pattern, &mut inner, &mut tests, &mut binds)?;
            let body = self.expr(path, &arm.body, &inner, depth + 2)?;
            let guard = if tests.is_empty() {
                String::new()
            } else {
                format!(" if {}", tests.join(" && "))
            };
            let body = if binds.is_empty() {
                body
            } else {
                binds.push(body);
                braces(&binds, depth + 1)
            };
            lines.push(format!("{pat}{guard} => {body}"));
        }
        let pad = "  ".repeat(depth + 1);
        let end = "  ".repeat(depth);
        Ok(format!(
            "match {s} {{\n{}\n{end}}}",
            lines
                .iter()
                .map(|l| format!("{pad}{l}"))
                .collect::<Vec<_>>()
                .join("\n")
        ))
    }

    /// `p`, an arm's pattern (the arm's body at `at`), with each constructor named as
    /// the kernel read it.
    ///
    /// The kernel notes the constructors of an arm's pattern in the order it meets
    /// them, a nested pattern's after the one around it, which is the order of
    /// this walk. A constructor is taken from the next note when the note was made
    /// for that spelling; otherwise the pattern is left as written.
    fn kernel_named(&self, p: &Pattern, notes: &[&CtorSite], next: &mut usize) -> Pattern {
        let mut read = |name: &Name| match notes.get(*next) {
            Some(site)
                if site.written == *name
                    || matches!(name, Name::Selection(selection)
                    if site.written.as_global().is_some_and(|reference|
                        selection.candidates().contains(reference))) =>
            {
                *next += 1;
                site.resolved.clone()
            }
            _ => name.clone(),
        };
        match p {
            Pattern::Bind { name: n, .. } => Pattern::Bind { name: read(n), unused: None },
            Pattern::Ctor { name, args } => {
                let name = read(name);
                Pattern::Ctor {
                    name,
                    args: args
                        .iter()
                        .map(|q| self.kernel_named(q, notes, next))
                        .collect(),
                }
            }
            other => other.clone(),
        }
    }

    fn pattern_family(&self, p: &Pattern) -> Option<Name> {
        let name = match p {
            Pattern::Ctor { name, .. } => name,
            Pattern::Bind { name: name, .. } => name,
            _ => return None,
        };
        self.checked
            .families
            .iter()
            .find(|(_, f)| f.ctors.iter().any(|c| c == name))
            .map(|(n, _)| n.clone())
    }

    fn is_ctor(&self, name: &Name) -> bool {
        self.checked.is_ctor(name)
    }

    /// A match on `Nat` or `Bool`: each arm's pattern as a test and bindings
    /// on `s`, tried in order.
    fn chain(
        &mut self,
        path: &Path,
        s: &str,
        arms: &[MatchArm],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        let (subject, bind) = if is_name(s) {
            (s.to_string(), None)
        } else {
            let v = self.fresh("m");
            (v.to_string(), Some(format!("let {v} := {s}")))
        };
        let rows: Vec<(Vec<Pattern>, &SurfaceTerm)> = arms
            .iter()
            .map(|a| (vec![a.pattern.clone()], &a.body))
            .collect();
        let out = self.chain_rows(path, &[subject], &rows, locals, depth)?;
        Ok(match bind {
            Some(b) => braces(&[b, out], depth),
            None => out,
        })
    }

    /// Rows of patterns, one per name of `subjects`, as a chain of tests
    /// tried in order. The last row is not tested: the kernel has checked
    /// that the rows take every value that reaches them.
    fn chain_rows(
        &mut self,
        path: &Path,
        subjects: &[String],
        rows: &[(Vec<Pattern>, &SurfaceTerm)],
        locals: &Locals,
        depth: usize,
    ) -> Result<String, Message> {
        let mut out = String::new();
        let n = rows.len();
        for (k, (pats, body)) in rows.iter().enumerate() {
            let mut inner = locals.clone();
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            for (p, at) in pats.iter().zip(subjects) {
                self.test(path, p, at, &mut inner, &mut tests, &mut binds)?;
            }
            binds.push(self.expr(path, body, &inner, depth + 2)?);
            let body = braces(&binds, depth + 1);
            if k + 1 == n {
                if k == 0 {
                    out.push_str(&body);
                } else {
                    let _ = write!(out, " else {body}");
                }
            } else {
                let test = if tests.is_empty() {
                    "true".to_string()
                } else {
                    tests.join(" && ")
                };
                if k == 0 {
                    let _ = write!(out, "if {test} {body}");
                } else {
                    let _ = write!(out, " else if {test} {body}");
                }
            }
        }
        Ok(out)
    }

    /// A match whose patterns have a part on `Nat` or `Bool` under a
    /// constructor (`#(b, Succ(k))`), as the case tree the kernel read it as:
    /// the arms of one shape (the pattern with each such part, each name and
    /// each `_` taken out) are one Nib arm, which binds every part taken out
    /// and tests the parts on `Nat` and `Bool` in its body, by `chain_rows`.
    /// Nib then sees no guard, and checks that the shapes cover every value.
    /// `None` when no arm has such a part.
    fn shaped(
        &mut self,
        path: &Path,
        s: &str,
        arms: &[MatchArm],
        locals: &Locals,
        depth: usize,
    ) -> Result<Option<String>, Message> {
        let mut shapes = Vec::new();
        for arm in arms {
            let mut holes = Vec::new();
            let shape = self.shape(&arm.pattern, &mut holes);
            shapes.push((shape, holes));
        }
        let tested = |p: &Pattern| {
            !matches!(p, Pattern::Wild | Pattern::Bind { .. })
                || matches!(p, Pattern::Bind { name: n, .. } if self.is_ctor(n))
        };
        if !shapes.iter().any(|(_, holes)| holes.iter().any(tested)) {
            return Ok(None);
        }
        // The default arm (`_ =>`, or a name) is last, and takes what the
        // arms of each shape leave.
        let default = arms.last().filter(|a| {
            matches!(&a.pattern, Pattern::Wild)
                || matches!(&a.pattern, Pattern::Bind { name: n, .. } if !self.is_ctor(n))
        });
        let written = arms.len() - usize::from(default.is_some());
        let mut groups: Vec<(Pattern, Vec<usize>)> = Vec::new();
        for (i, (shape, _)) in shapes[..written].iter().enumerate() {
            match groups.iter_mut().find(|(g, _)| g == shape) {
                Some((_, members)) => members.push(i),
                None => groups.push((shape.clone(), vec![i])),
            }
        }
        // Two shapes that some value has would order their arms, which the
        // kernel's case tree does not: each arm's tests would then have to
        // fall through to another Nib arm.
        for (a, (x, _)) in groups.iter().enumerate() {
            if groups[a + 1..].iter().any(|(y, _)| overlap(x, y)) {
                return fail(path, msg!("tauto-extract-nested-arms-overlap"));
            }
        }
        let (subject, bind) = if is_name(s) || default.is_none() {
            (s.to_string(), None)
        } else {
            let v = self.fresh("m");
            (v.to_string(), Some(format!("let {v} := {s}")))
        };
        let mut lines = Vec::new();
        for (shape, members) in &groups {
            let count = shapes[members[0]].1.len();
            let names: Vec<Name> = (0..count).map(|_| self.fresh("p")).collect();
            let mut next = names.iter();
            let filled = fill_holes(shape, &mut next);
            let mut inner = locals.clone();
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            let pat = self.nib_pattern(path, &filled, &mut inner, &mut tests, &mut binds)?;
            let mut rows: Vec<(Vec<Pattern>, &SurfaceTerm)> = members
                .iter()
                .map(|&i| (shapes[i].1.clone(), &arms[i].body))
                .collect();
            if let Some(d) = default {
                let mut row = vec![Pattern::Wild; count];
                let mut pats = vec![d.pattern.clone()];
                pats.append(&mut row);
                rows.push((pats, &d.body));
            }
            let subjects: Vec<String> = if default.is_some() {
                std::iter::once(subject.clone())
                    .chain(names.iter().map(ToString::to_string))
                    .collect()
            } else {
                names.iter().map(ToString::to_string).collect()
            };
            let rows: Vec<(Vec<Pattern>, &SurfaceTerm)> = if default.is_some() {
                rows.into_iter()
                    .enumerate()
                    .map(|(k, (pats, body))| {
                        if k < members.len() {
                            (std::iter::once(Pattern::Wild).chain(pats).collect(), body)
                        } else {
                            (pats, body)
                        }
                    })
                    .collect()
            } else {
                rows
            };
            let body = self.chain_rows(path, &subjects, &rows, &inner, depth + 2)?;
            lines.push(format!("{pat} => {body}"));
        }
        if let Some(d) = default {
            // A name, not `_`: the shapes may already take every value, and
            // an arm no value reaches is left out when the program is lowered.
            let rest = self.fresh("rest");
            let mut inner = locals.clone();
            let mut binds = Vec::new();
            self.test(
                path,
                &d.pattern,
                &subject,
                &mut inner,
                &mut Vec::new(),
                &mut binds,
            )?;
            binds.push(self.expr(path, &d.body, &inner, depth + 2)?);
            lines.push(format!("{rest} => {}", braces(&binds, depth + 1)));
        }
        let pad = "  ".repeat(depth + 1);
        let end = "  ".repeat(depth);
        let out = format!(
            "match {subject} {{\n{}\n{end}}}",
            lines
                .iter()
                .map(|l| format!("{pad}{l}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        Ok(Some(match bind {
            Some(b) => braces(&[b, out], depth),
            None => out,
        }))
    }

    /// `p` with each part that `shaped` takes out (a part on `Nat` or
    /// `Bool`, a name, `_`) put in `holes` and written as [`HOLE`].
    fn shape(&self, p: &Pattern, holes: &mut Vec<Pattern>) -> Pattern {
        let p = unlabel(p);
        let hole = |holes: &mut Vec<Pattern>| {
            holes.push(p.clone());
            Pattern::Bind {
                name: HOLE.into(),
                unused: None,
            }
        };
        match &p {
            Pattern::Ctor { .. } if let Some(items) = p.product_members() => {
                Pattern::product(items.iter().map(|q| self.shape(q, holes)).collect())
            }
            Pattern::Wild | Pattern::Int(_) | Pattern::Text(_) => hole(holes),
            Pattern::Bind { name: n, .. } if !self.is_ctor(n) => hole(holes),
            Pattern::Bind { .. } | Pattern::Ctor { .. }
                if matches!(
                    self.std.of(&self.pattern_family(&p).unwrap_or_default()),
                    Some("Nat" | "Bool")
                ) =>
            {
                hole(holes)
            }
            Pattern::Bind { name: n, .. } => Pattern::Ctor {
                name: n.clone(),
                args: vec![],
            },
            Pattern::Ctor { name, args } => Pattern::Ctor {
                name: name.clone(),
                args: args.iter().map(|q| self.shape(q, holes)).collect(),
            },
            other => other.clone(),
        }
    }

    fn test(
        &mut self,
        path: &Path,
        p: &Pattern,
        at: &str,
        locals: &mut Locals,
        tests: &mut Vec<String>,
        binds: &mut Vec<String>,
    ) -> Result<(), Message> {
        match p {
            Pattern::Wild => Ok(()),
            Pattern::Bind { name: n, .. } if !self.is_ctor(n) => {
                binds.push(format!("let {} := {at}", self.local(n)));
                locals.insert(n.clone());
                Ok(())
            }
            Pattern::Bind { name: n, .. } => self.test(
                path,
                &Pattern::Ctor {
                    name: n.clone(),
                    args: vec![],
                },
                at,
                locals,
                tests,
                binds,
            ),
            Pattern::Ctor { name, args } => {
                match (self.std.of(name).unwrap_or(""), args.as_slice()) {
                    ("Zero", []) => {
                        tests.push(format!("{at} == 0"));
                        Ok(())
                    }
                    ("Succ", [q]) => {
                        tests.push(format!("{at} >= 1"));
                        let inner = format!("({at} - 1)");
                        self.test(path, q, &inner, locals, tests, binds)
                    }
                    ("true", []) => {
                        tests.push(at.to_string());
                        Ok(())
                    }
                    ("false", []) => {
                        tests.push(format!("not({at})"));
                        Ok(())
                    }
                    _ => fail(
                        path,
                        msg!("tauto-extract-in-a-match-on-at", name = name.to_string()),
                    ),
                }
            }
            Pattern::Int(k) => {
                tests.push(format!("{at} == {k}"));
                Ok(())
            }
            Pattern::Text(t) => {
                tests.push(format!("{at} == {}", text_literal(t)));
                Ok(())
            }
            _ => fail(path, msg!("tauto-extract-a-pattern-that-is-not")),
        }
    }

    /// `p` as a Nib pattern; a part on `Nat` or `Bool` becomes a fresh name
    /// with tests in the guard and bindings in the body.
    fn nib_pattern(
        &mut self,
        path: &Path,
        p: &Pattern,
        locals: &mut Locals,
        tests: &mut Vec<String>,
        binds: &mut Vec<String>,
    ) -> Result<String, Message> {
        match p {
            // `#(p, q)`: Nib's own product.
            Pattern::Ctor { .. } if let Some(items) = p.product_members() => {
                let mut parts = Vec::new();
                for q in items {
                    parts.push(self.nib_pattern(path, q, locals, tests, binds)?);
                }
                Ok(format!("#({})", parts.join(", ")))
            }
            Pattern::Wild => Ok("_".into()),
            Pattern::Bind { name: n, .. } if !self.is_ctor(n) => {
                locals.insert(n.clone());
                Ok(self.local(n))
            }
            Pattern::Bind { name: n, .. } => self.nib_pattern(
                path,
                &Pattern::Ctor {
                    name: n.clone(),
                    args: vec![],
                },
                locals,
                tests,
                binds,
            ),
            // `@a p`: kept, so Nib takes the label off the value's type as the kernel
            // did; `p` alone would bind the member at `@a T`, and `cur + n` on it
            // would no longer be the sum of two `Nat`s.
            Pattern::Ctor { .. } if let Some((tag, inner)) = p.label() => {
                let inner = self.nib_pattern(path, inner, locals, tests, binds)?;
                Ok(format!("@{} {inner}", raw(tag)))
            }
            Pattern::Ctor { name, args } => {
                let fam = self.pattern_family(p).unwrap_or_default();
                if matches!(self.std.of(&fam), Some("Nat" | "Bool")) {
                    let v = self.fresh("p");
                    locals.insert(v.clone());
                    let mut inner_binds = Vec::new();
                    self.test(path, p, &v, locals, tests, &mut inner_binds)?;
                    binds.extend(inner_binds);
                    return Ok(v.to_string());
                }
                let sig = self.checked.signatures.get(name).cloned().ok_or_else(|| {
                    format!(
                        "{}: pattern constructor {name:?} has no checked declaration",
                        path.display()
                    )
                })?;
                let fields: &[Role] = if args.len() + sig.implicit == sig.params.len() {
                    &sig.params[sig.implicit..]
                } else {
                    let fam_params = self.checked.families[&fam].params;
                    &sig.params[fam_params..]
                };
                if fields.len() != args.len() {
                    return fail(
                        path,
                        msg!(
                            "tauto-extract-in-a-pattern-has-the",
                            name = name.to_string()
                        ),
                    );
                }
                let mut parts = Vec::new();
                for (q, r) in args.iter().zip(fields) {
                    let part = self.nib_pattern(path, q, locals, tests, binds)?;
                    if *r == Role::Value {
                        parts.push(part);
                    }
                }
                Ok(match (self.std.of(name).unwrap_or(""), parts.as_slice()) {
                    ("Pair::Mk", [a, b]) => format!("#({a}, {b})"),
                    ("Star", []) => "#()".into(),
                    _ if self.struct_fields(name).is_some() => {
                        let (family, names) = self.struct_fields(name).unwrap();
                        let fields: Vec<String> = names
                            .iter()
                            .zip(&parts)
                            .map(|(f, p)| format!("{}: {p}", raw(f)))
                            .collect();
                        format!("{family} {{ {} }}", fields.join(", "))
                    }
                    (_, []) => self.ctor_ref(name),
                    _ => format!("{}({})", self.ctor_ref(name), parts.join(", ")),
                })
            }
            Pattern::Int(_) | Pattern::Text(_) => {
                let v = self.fresh("p");
                locals.insert(v.clone());
                self.test(path, p, &v, locals, tests, binds)?;
                Ok(v.to_string())
            }
            _ => fail(path, msg!("tauto-extract-a-pattern-that-is-not")),
        }
    }
}

/// `()`, which the parser reads as the empty tuple.
/// The items of `Cons(a, Cons(b, Nil))`, the terms `[a, b]` reads as; none
/// when the chain ends in anything but `Nil`.
/// The functions among `stmts` that only put texts before their last
/// parameter: `f(…, r: List(Text)): List(Text)` whose every tail is `r`,
/// `Cons(h, e)` or `g(…, e)` for another such `g`, with `r` nowhere else. Then
/// `Text::concat_all(f(…, r))` is the texts `f` puts, then those of `r`.
fn text_writers(stmts: &[Stmt], std: &StdNames) -> HashSet<Name> {
    use crate::direct::mentions;
    fn list_of_text(t: &Option<SurfaceTerm>, std: &StdNames) -> bool {
        let Some(t) = t else { return false };
        let TermKind::App {
            function,
            arguments,
        } = &*t.kind
        else {
            return false;
        };
        matches!(&*function.kind, TermKind::Var(l) if std.of(l) == Some("List"))
            && matches!(arguments.as_slice(), [a] if matches!(&*a.kind, TermKind::Var(x) if std.of(x) == Some("Text") || x.to_string() == "Text"))
    }
    fn tail(t: &SurfaceTerm, r: &Name, ok: &HashSet<Name>) -> bool {
        match &*t.kind {
            TermKind::Var(v) => v == r,
            TermKind::Ascribe { term, .. } => tail(term, r, ok),
            TermKind::Match {
                scrutinee, arms, ..
            } => {
                !mentions(scrutinee, r)
                    && !arms.is_empty()
                    && arms.iter().all(|a| {
                        a.guard.as_ref().is_none_or(|g| !mentions(g, r)) && tail(&a.body, r, ok)
                    })
            }
            TermKind::If {
                condition,
                then,
                otherwise,
            } => {
                !mentions(condition, r)
                    && tail(then, r, ok)
                    && otherwise.as_ref().is_some_and(|o| tail(o, r, ok))
            }
            TermKind::App {
                function,
                arguments,
            } => {
                let TermKind::Var(g) = &*function.kind else {
                    return false;
                };
                let Some((last, rest)) = arguments.split_last() else {
                    return false;
                };
                (crate::bindings::is_library(g, "Cons") && rest.len() == 1 || ok.contains(g))
                    && rest.iter().all(|a| !mentions(a, r))
                    && tail(last, r, ok)
            }
            _ => false,
        }
    }
    let candidates: Vec<&FnDecl> = stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Fn(f) => Some(f),
            _ => None,
        })
        .filter(|f| {
            f.effects.as_ref().is_none_or(|e| e.is_empty())
                && f.where_.is_empty()
                // Shared borrows are passed along as written; the list the
                // texts go before is taken by value.
                && f.borrows.iter().all(|b| *b != Some(true))
                && f.borrows.last().is_none_or(Option::is_none)
                && f.params.len() == f.param_types.len()
                && !f.params.is_empty()
                && list_of_text(&f.result, std)
                && list_of_text(f.param_types.last().unwrap(), std)
        })
        .collect();
    let mut ok: HashSet<Name> = candidates.iter().map(|f| f.name.clone()).collect();
    loop {
        let before = ok.len();
        let kept: HashSet<Name> = candidates
            .iter()
            .filter(|f| ok.contains(&f.name) && tail(&f.body, f.params.last().unwrap(), &ok))
            .map(|f| f.name.clone())
            .collect();
        ok = kept;
        if ok.len() == before {
            break;
        }
    }
    // Only the writers a `Text::concat_all(g(…, Nil))` reaches are written
    // twice.
    let mut used = HashSet::new();
    for s in stmts {
        // Any statement: a definition's closures (a codec's) reach writers too.
        let mut s = s.clone();
        crate::surface::walk::roots(&mut s, &mut |body| {
            crate::surface::walk::term(body, &mut |u| {
                if let TermKind::App {
                function,
                arguments,
            } = &*u.kind
                && let (TermKind::Var(c), [inner]) = (&*function.kind, arguments.as_slice())
                && std.of(c) == Some("Text::concat_all")
                && let TermKind::App {
                    function,
                    arguments,
                } = &*inner.kind
                && let TermKind::Var(g) = &*function.kind
                && ok.contains(g)
                && arguments.last().is_some_and(
                    |l| matches!(&*l.kind, TermKind::Var(n) if crate::bindings::is_library(n, "Nil")),
                )
            {
                used.insert(g.clone());
            }
            })
        });
    }
    let mut todo: Vec<Name> = used.iter().cloned().collect();
    while let Some(g) = todo.pop() {
        let Some(f) = candidates.iter().find(|f| f.name == g) else {
            continue;
        };
        for h in &ok {
            if !used.contains(h) && mentions(&f.body, h) {
                used.insert(h.clone());
                todo.push(h.clone());
            }
        }
    }
    used
}

fn list_items<'t>(mut t: &'t SurfaceTerm, locals: &Locals) -> Option<Vec<&'t SurfaceTerm>> {
    let mut items = Vec::new();
    loop {
        match &*t.kind {
            TermKind::Var(n) if crate::bindings::is_library(&n, "Nil") && !locals.contains(n) => {
                return Some(items);
            }
            TermKind::App {
                function,
                arguments,
            } if arguments.len() == 2
                && matches!(&*function.kind, TermKind::Var(n) if crate::bindings::is_library(&n, "Cons") && !locals.contains(n)) =>
            {
                items.push(&arguments[0]);
                t = &arguments[1];
            }
            _ => return None,
        }
    }
}

fn has_bool(p: &Pattern) -> bool {
    match p {
        Pattern::Bool(_) => true,
        Pattern::Ctor { args, .. } => args.iter().any(has_bool),
        Pattern::Record { fields, .. } => fields.iter().any(|(_, p)| has_bool(p)),
        _ => false,
    }
}

fn bool_constructors(p: &Pattern) -> Pattern {
    match p {
        Pattern::Bool(b) => Pattern::Ctor {
            name: crate::bindings::library_name(if *b { "true" } else { "false" }),
            args: Vec::new(),
        },
        Pattern::Ctor { name, args } => Pattern::Ctor {
            name: name.clone(),
            args: args.iter().map(bool_constructors).collect(),
        },
        Pattern::Record { name, fields } => Pattern::Record {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(f, p)| (f.clone(), bool_constructors(p)))
                .collect(),
        },
        other => other.clone(),
    }
}

fn is_unit(t: &SurfaceTerm) -> bool {
    t.is_unit()
}

fn mapped_ctor(n: &str, values: &[String]) -> Option<String> {
    Some(match (n, values) {
        // A bare numeral defaults to an integer where nothing else says what it is
        // (`Ord::compare(#(Zero, Zero), …)`); `Zero` is a `nat`.
        ("Zero", []) => "(0: nat)".into(),
        ("Succ", [x]) => format!("({x} + 1)"),
        ("true", []) => "true".into(),
        ("false", []) => "false".into(),
        ("Star", []) => "#()".into(),
        ("U8::Mk", [v]) => format!("U8::of_u64(U64::of_nat({v}))"),
        ("U32::Mk", [v]) => format!("U32::of_u64(U64::of_nat({v}))"),
        ("U64::Mk", [v]) => format!("U64::of_nat({v})"),
        ("UHost::Mk", [v]) => format!("UHost::of_u64_below(U64::of_nat({v}))"),
        ("Bytes::Mk", [l]) => format!("Bytes::of_list({l})"),
        ("Float::Mk", [b]) => format!("Float::of_bits({b})"),
        ("Float32::Mk", [b]) => format!("Float32::of_bits({b})"),
        ("Secret::Mk", [v]) => format!("secret({v})"),
        ("Pair::Mk", [a, b]) => format!("#({a}, {b})"),
        _ => return None,
    })
}

/// A function of a width of `std/uint.taut` or `std/sint.taut`
/// (`UInt::sub_or_overflow64`).
/// The function a numeral at a width is read as (`SInt::mk64`).
pub(crate) fn width_literal(n: Option<&str>) -> bool {
    n.is_some_and(|n| {
        width_function(n)
            && n.trim_end_matches(|c: char| c.is_ascii_digit())
                .ends_with("::mk")
    })
}

pub(crate) fn width_function(n: &str) -> bool {
    (n.starts_with("UInt::") || n.starts_with("SInt::")) && n.ends_with(|c: char| c.is_ascii_digit())
}

fn is_eliminator(n: &str) -> bool {
    ["::rec", "::ind", "::nc", "::noconf", "::nc_diag"]
        .iter()
        .any(|s| n.ends_with(s))
}

/// A shift or rotation of `U32` or `U64` by a literal amount: the amount
/// is reduced modulo the width here, once, instead of through `nat` at
/// every call (`u32_rotr(x, 7)` in hash rounds). The result is the one the
/// table's template computes.
fn literal_shift(name: &str, values: &[String]) -> Option<String> {
    let bits: u128 = match name {
        "UInt::shl32" | "UInt::shr32" | "UInt::rotl32" | "UInt::rotr32" => 32,
        "UInt::shl64" | "UInt::shr64" | "UInt::rotl64" | "UInt::rotr64" => 64,
        _ => return None,
    };
    let [a, s] = values else { return None };
    let s = s.trim();
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    // Only the low digits matter: 10^k is 0 modulo 32 and 64 for k >= 6.
    let low = &s[s.len().saturating_sub(6)..];
    let s = low.parse::<u128>().ok()? % bits;
    // Nib's own operation: `UInt::shl32` is `U32::shl`.
    let op = name.strip_prefix("UInt::")?.trim_end_matches(|c: char| c.is_ascii_digit());
    Some(format!("(U{bits}::{op}(({a}), {s}))"))
}

fn fill(template: &str, values: &[String]) -> String {
    let mut out = template.to_string();
    for (k, v) in values.iter().enumerate().rev() {
        out = out.replace(&format!("${k}"), &format!("({v})"));
    }
    out
}

/// `<A, B: Shared, !e>`: the generics of a function, which a call infers,
/// each written as [`with_bound`] gives it.
fn angle(generics: &[&str]) -> String {
    if generics.is_empty() {
        return String::new();
    }
    format!("<{}>", generics.join(", "))
}

/// A type generic with the bound the source writes; none is affine, the
/// default of every function (`docs/design/ownership.md`).
fn with_bound(g: &str, bound: Option<crate::surface::GenericBound>) -> String {
    match bound {
        Some(b) => format!("{g}: {b}"),
        None => g.to_string(),
    }
}

fn type_params(generics: &[&str]) -> String {
    if generics.is_empty() {
        return String::new();
    }
    let gs: Vec<String> = generics.iter().map(|g| format!("{g}: Type")).collect();
    format!("({})", gs.join(", "))
}

fn braces(lines: &[String], depth: usize) -> String {
    let pad = "  ".repeat(depth + 1);
    let end = "  ".repeat(depth);
    format!(
        "{{\n{}\n{end}}}",
        lines
            .iter()
            .map(|l| format!("{pad}{l}"))
            .collect::<Vec<_>>()
            .join("\n")
    )
}

fn is_name(s: &str) -> bool {
    !s.is_empty() && s.chars().all(tauto_parol::unicode::is_ident_continue)
}

fn pattern_names(p: &Pattern, out: &mut Locals) {
    match p {
        Pattern::Bind { name: n, .. } => {
            out.insert(n.clone());
        }
        Pattern::Ctor { args, .. } => args.iter().for_each(|a| pattern_names(a, out)),
        _ => {}
    }
}

fn text_literal(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{{{:x}}}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn show(t: &SurfaceTerm) -> String {
    crate::check::describe(t)
}

/// The statements an `inductive_syntax!` declaration makes: the types and `<syntax>.parse` of Nib,
/// Executable declarations retained from the syntax expansion boundary.
fn generated_nib_names(input: &crate::read::ExtractionInput) -> HashSet<Name> {
    input.loaded.generated_executable.clone()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The helpers are Tauto source written into every extracted program, so
    /// each one has to be read like a program written by hand. A static name
    /// is written with `::` (`.` takes a field only), and no helper takes a
    /// field of a value named with a capital, so `I64.of_u64` for
    /// `I64::of_u64` is caught here, not in the program of whoever extracts.
    #[test]
    fn every_helper_is_read_as_tauto() {
        for (name, text) in [
            ("HELPERS", HELPERS.to_string()),
            ("TEXT_HELPERS", TEXT_HELPERS.to_string()),
            ("sint_helpers", sint_helpers()),
            ("uint_helpers", uint_helpers()),
        ] {
            if let Err(e) = crate::read::parse_program(&text) {
                panic!("{name} is not read as Tauto: {e}");
            }
            let b = text.as_bytes();
            for (i, _) in text.match_indices('.') {
                let mut s = i;
                while s > 0 && (b[s - 1].is_ascii_alphanumeric() || b[s - 1] == b'_') {
                    s -= 1;
                }
                let after = b.get(i + 1).copied().unwrap_or(b' ');
                assert!(
                    !(s < i
                        && b[s].is_ascii_uppercase()
                        && (after.is_ascii_lowercase() || after == b'_')),
                    "{name} writes the static name `{}` with `.`, not `::`",
                    &text[s..text[i..]
                        .find(|c: char| c == '(' || c.is_whitespace())
                        .map_or(text.len(), |n| i + n)]
                );
            }
        }
    }

    #[test]
    fn helpers_import_the_prelude_files_they_name() {
        tauto_parse::install();
        let imports = |text: &str| -> Vec<String> {
            with_prelude_imports(text, &HashSet::new())
                .lines()
                .take_while(|l| l.starts_with("import "))
                .map(str::to_string)
                .collect()
        };
        // The helpers name only what the core prelude declares
        // (`std::prelude::Collections` among it), which every file sees
        // without an import.
        let helpers = imports(&format!("{HELPERS}{TEXT_HELPERS}"));
        assert!(helpers.is_empty(), "{helpers:?}");
        // A name only a `std::builtin` file declares brings its import.
        let (name, files) = crate::surface::qualify::hidden_prelude()
            .iter()
            .filter(|(n, _)| {
                n.starts_with(|c: char| c.is_ascii_alphabetic())
                    && n.chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == ':')
            })
            .min_by(|a, b| a.0.cmp(b.0))
            .unwrap();
        let named = imports(&format!("fn f(): Nat {{ {name} }}\n"));
        for f in files {
            let import = format!("import std::builtin::{f}");
            assert!(named.contains(&import), "{name}: {named:?}");
        }
    }

    #[test]
    fn hygienic_names_become_fresh_names_outside_text() {
        let (out, renamed) =
            legal_names("fn f(t_1: Nat) { let t#1 := \"t#1\" // t#2\n  g#r2(t#1, t_1) }");
        assert_eq!(
            out,
            "fn f(t_1: Nat) { let t_2 := \"t#1\" // t#2\n  g_1(t_2, t_1) }"
        );
        assert_eq!(renamed.len(), 2);
    }

    #[test]
    fn dictionary_marks_become_fresh_names_outside_text() {
        let (out, renamed) = legal_names(
            "fn C::next(inst@C: C(A), x: A) { C::inst@Head@instance1() }",
        );
        assert_eq!(
            out,
            "fn C::next(inst_C_1: C(A), x: A) { C::inst_Head_instance1_1() }"
        );
        assert_eq!(renamed.len(), 2);
    }

    #[test]
    fn extraction_uses_the_checked_source_and_include_snapshot() {
        tauto_parse::install();
        let root =
            std::env::temp_dir().join(format!("tauto-extraction-snapshot-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let source = root.join("source.tauto");
        let included = root.join("message.txt");
        let base = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../std/base.taut")
            .canonicalize()
            .unwrap();
        std::fs::write(&included, "checked text").unwrap();
        std::fs::write(
            &source,
            format!(
                "import \"{}\"\n{}",
                base.display(),
                r#"fn twice(n: Nat): Nat {
  ⊢ Nat from match n {
    Zero => Zero
    Succ(k) => Succ(Succ(twice(k)))
  }
}
fn message(): Text { include_text!("message.txt") }
show(&twice(2))
"#
            ),
        )
        .unwrap();
        let roots = vec![source.clone()];
        let input = crate::read::check_files_for_extraction(&roots, None, false, true).unwrap();
        std::fs::write(&source, r#"fn twice(n: Nat): Nat { twice(n) }"#).unwrap();
        std::fs::remove_file(&included).unwrap();
        let (text, runtime, total) = extract_checked(&input, true, &roots).unwrap();
        assert!(total.iter().any(|name| name.as_str() == "twice"));
        assert!(text.contains("+ 1"), "{text}");
        assert!(
            runtime
                .iter()
                .any(|(_, text)| text.contains("checked text"))
        );
        assert!(
            runtime
                .iter()
                .all(|(_, text)| !text.contains("include_text!"))
        );
        let (loaded, _) = runtime::assemble(&input, &text, &roots).unwrap();
        assert_eq!(
            loaded.files[..input.loaded.files.len()]
                .iter()
                .map(|f| &f.text)
                .collect::<Vec<_>>(),
            input
                .loaded
                .files
                .iter()
                .map(|f| &f.text)
                .collect::<Vec<_>>()
        );
        for i in 0..input.loaded.spans.len() {
            let at = crate::macros::EXPANSION_BASE + i as u32;
            assert_eq!(loaded.spans.origin(at), input.loaded.spans.origin(at));
        }
        assert!(loaded.program.stmts.iter().any(|s| {
            let mut found = false;
            crate::surface::walk::stmt(&mut s.clone(), &mut |t| {
                found |= matches!(&*t.kind, TermKind::Text(value) if value == "checked text");
            });
            found
        }));
        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn a_function_with_effects_the_kernel_rejects_does_not_run() {
        tauto_parse::install();
        let src = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/fixed-width/src");
        let roots = vec![src.join("counter.taut"), src.join("main.taut")];
        let mut input = crate::read::check_files_for_extraction(&roots, None, true, true).unwrap();
        let name = "UInt::add_or_overflow8";
        let entry = input
            .checked
            .entries
            .iter_mut()
            .find(|e| e.entry.name.as_str() == name)
            .unwrap();
        entry.entry.verdict =
            Verdict::Failed(tauto_surface::diagnostic::Diagnostic::new("rejected", None));
        input.checked.runtime.insert(name.into());
        let Err(e) = extract_checked(&input, true, &roots) else {
            panic!("a rejected function was extracted");
        };
        // The problems come as a chain of `tauto-extract-problems`; the rejected
        // function is one of them, said by its id and arguments.
        let mut problems = vec![&e];
        let mut rejected = false;
        while let Some(problem) = problems.pop() {
            if problem.id == "tauto-extract-problems" {
                for part in ["first", "rest"] {
                    if let Some(tauto_message::Value::Message(m)) = problem.get(part) {
                        problems.push(m);
                    }
                }
            } else if problem.id == "tauto-extract-located"
                && let Some(tauto_message::Value::Message(what)) = problem.get("what")
            {
                rejected |= what.id == "tauto-extract-failed"
                    && what.get("name") == Some(&name.into())
                    && what.get("why") == Some(&Message::text("rejected").into());
            }
        }
        assert!(rejected, "{e:?}");
    }
}

/// A row as written, a set expression: its effects `{A, B}`, then its variable united with them,
/// `{A, B} ∪ e`; a row of a variable alone is `e`.
fn row_text(row: &[Name]) -> String {
    let (vars, effects): (Vec<&Name>, Vec<&Name>) =
        row.iter().partition(|e| e.row_variable().is_some());
    let effects = effects
        .iter()
        .map(|e| e.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    match vars.first() {
        Some(v) if effects.is_empty() => v.row_variable().expect("a row variable").to_string(),
        Some(v) => format!(
            "{{{effects}}} ∪ {}",
            v.row_variable().expect("a row variable")
        ),
        None => format!("{{{effects}}}"),
    }
}

/// Whether the prelude every Nib program sees declares a function `name` (`not`): extraction calls
/// it and does not write it out.
fn nib_prelude_fn(name: &str) -> bool {
    static NAMES: std::sync::OnceLock<HashSet<String>> = std::sync::OnceLock::new();
    NAMES
        .get_or_init(|| {
            tauto_parse::parse_program_as_written(crate::nibstd::PRELUDE)
                .map(|p| {
                    p.stmts
                        .iter()
                        .filter_map(|s| match s {
                            Stmt::Fn(f) => Some(f.name.to_string()),
                            _ => None,
                        })
                        .collect()
                })
                .unwrap_or_default()
        })
        .contains(name)
}

/// Where `Extractor::shape` took a part out of a pattern; not a name a
/// program can write.
const HOLE: &str = "\u{0}hole";

/// `shape` with its holes, in order, as the names of `names`.
fn fill_holes<'n>(shape: &Pattern, names: &mut impl Iterator<Item = &'n Name>) -> Pattern {
    match shape {
        Pattern::Bind { name: n, .. } if n.spelling() == Some(HOLE) => {
            Pattern::Bind { name: names.next().cloned().unwrap_or_default(), unused: None }
        }
        Pattern::Ctor { name, args } => Pattern::Ctor {
            name: name.clone(),
            args: args.iter().map(|q| fill_holes(q, names)).collect(),
        },
        other => other.clone(),
    }
}

/// Whether some value has both shapes (a hole has every value). A pattern
/// `shape` does not take apart is taken to overlap.
fn overlap(a: &Pattern, b: &Pattern) -> bool {
    match (a, b) {
        (Pattern::Bind { name: n, .. }, _) | (_, Pattern::Bind { name: n, .. }) if n.spelling() == Some(HOLE) => true,
        (Pattern::Ctor { name: m, args: x }, Pattern::Ctor { name: n, args: y }) => {
            m == n && x.len() == y.len() && x.iter().zip(y).all(|(p, q)| overlap(p, q))
        }
        _ => true,
    }
}

/// `p` with the labels at its head taken off: `@a @b q` is `q`.
fn unlabel(p: &Pattern) -> Pattern {
    let mut p = p;
    while let Some((_, inner)) = p.label() {
        p = inner;
    }
    p.clone()
}

pub(crate) fn macro_made(s: &Stmt) -> bool {
    let span = match s {
        Stmt::Fn(f) => f.span,
        Stmt::Effect(e) => e.span,
        Stmt::Theorem(t) | Stmt::Def(t) => t.span,
        Stmt::Inductive(i) => i.span,
        Stmt::Class(c) => c.span,
        Stmt::Instance(i) => i.span,
        Stmt::Mutual { span, .. } => *span,
        _ => return false,
    };
    (crate::macros::EXPANSION_BASE..crate::surface::PRELUDE_BASE).contains(&span.start)
}

/// An extracted program written as `extract_files` writes its output: parsed
/// and written back, so a text that differs only in redundant parentheses or
/// layout is written the same.
pub fn rewrite_source(text: &str) -> Result<String, String> {
    tauto_parse::install();
    let program = tauto_parse::parse_program_unresolved_at(text, 0)?;
    if let Some((error, _)) = program.errors.first() {
        return Err(error.to_string());
    }
    let text = source::write_unchecked(&program.stmts).map_err(|e| e.to_string())?;
    Ok(format!("{EXTRACTED_BEGIN}{text}\n{EXTRACTED_END}"))
}

/// A borrowed parameter's type, `&T` or `&mut T`. A function type is put in
/// parentheses so that the `&` takes all of it.
fn borrowed_ty(mark: &str, ty: &str) -> String {
    // Class projections may carry both a `borrows` mark and a `Borrow` in the
    // parameter type; emit the place once.
    if mark.is_empty() || ty.starts_with('&') {
        ty.to_string()
    } else if ty.contains("->") {
        format!("{mark}({ty})")
    } else {
        format!("{mark}{ty}")
    }
}
