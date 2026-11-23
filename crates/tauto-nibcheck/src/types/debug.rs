//! The `Debug` instances the compiler writes (`docs/design/debug.md`): one for
//! each `struct` and `enum` whose program writes none, its `where` inferred
//! from the fields. They are added as written instances, so resolution and
//! expansion treat them as any other.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::surface::walk;
use crate::surface::{DataDecl, Name, Pattern, Program, Stmt, SurfaceTerm, TermKind, Vis};

/// Where the spans of the instances made here start: below the terms the
/// class expansion makes, and above any written program.
const BASE: u32 = 3 << 28;

/// Whether `span` is one of the instances made here, or the prelude's. The
/// spans of what a macro expands to (`GENERATED_BASE` up to the prelude's) are
/// the program's: a function a macro replaces is written by the program.
pub(super) fn is_made(span: tauto_parol::Span) -> bool {
    (BASE..crate::surface::GENERATED_BASE).contains(&span.start)
        || span.start >= crate::surface::PRELUDE_BASE
}

/// For a type head, which of its parameters must be `Debug` for it to be.
type Table = HashMap<String, Vec<bool>>;

/// The declarations the written instances are for, by `key`: a resolved
/// head spelled the same as one of them but declared apart (the builtin
/// `Bytes` and a `std::bytes::Bytes` of its own) is another type, which the
/// entry of `Table` under that key does not answer for.
type Ids = HashMap<String, HashSet<String>>;

fn written_ids(stmts: &[Stmt], out: &mut Ids) {
    for s in stmts {
        match s {
            Stmt::Instance(i) if is_debug(&i.class) => {
                let h = match &*i.head.kind {
                    TermKind::Var(h) => h,
                    TermKind::App { function, .. } => match &*function.kind {
                        TermKind::Var(h) => h,
                        _ => continue,
                    },
                    _ => continue,
                };
                if let Some(r) = h.as_global() {
                    out.entry(key(h)).or_default().insert(format!("{r:?}"));
                }
            }
            Stmt::Mutual { items, .. } => written_ids(items, out),
            _ => {}
        }
    }
}

/// Whether `n` is a type other than the one the written instance under its
/// key is for.
fn other(n: &Name, ids: &Ids) -> bool {
    match (n.as_global(), ids.get(&key(n))) {
        (Some(r), Some(set)) => !set.contains(&format!("{r:?}")),
        _ => false,
    }
}

/// How a head is looked up across the program and the prelude, which may
/// name it differently: a spelled name by its last segment, a resolved one by
/// its whole path, so that two modules' types spelled the same (an imported
/// `Node` and a file's own `Node`) stay two types.
fn key(n: &Name) -> String {
    if n.as_global().is_some() {
        n.as_str().to_string()
    } else {
        last(n)
    }
}

/// The last segment of a name, as it is shown.
fn last(n: &Name) -> String {
    let s = n.as_str();
    s.rsplit("::").next().unwrap_or(s).to_string()
}

fn is_debug(n: &Name) -> bool {
    last(n) == "Debug"
}

pub(super) fn is_debug_class(n: &Name) -> bool {
    is_debug(n)
}

fn datas(stmts: &[Stmt], out: &mut Vec<DataDecl>) {
    for s in stmts {
        match s {
            Stmt::Struct(d) | Stmt::Enum(d) => out.push(d.clone()),
            Stmt::Mutual { items, .. } => datas(items, out),
            _ => {}
        }
    }
}

/// The heads of the written `Debug` instances, with the parameters their
/// `where` asks `Debug` of.
/// The types the `Debug` instances of `stmts` are for.
fn heads(stmts: &[Stmt]) -> HashSet<Name> {
    let mut out = HashSet::new();
    for s in stmts {
        match s {
            Stmt::Instance(i) if is_debug(&i.class) => {
                let head = match &*i.head.kind {
                    TermKind::Var(h) => h,
                    TermKind::App { function, .. } => match &*function.kind {
                        TermKind::Var(h) => h,
                        _ => continue,
                    },
                    _ => continue,
                };
                out.insert(head.clone());
            }
            Stmt::Mutual { items, .. } => out.extend(heads(items)),
            _ => {}
        }
    }
    out
}

fn written(stmts: &[Stmt], out: &mut Table) {
    for s in stmts {
        match s {
            Stmt::Instance(i) if is_debug(&i.class) => {
                let (head, args) = match &*i.head.kind {
                    TermKind::Var(h) => (h, Vec::new()),
                    TermKind::App {
                        function,
                        arguments,
                    } => match &*function.kind {
                        TermKind::Var(h) => (h, arguments.clone()),
                        _ => continue,
                    },
                    _ => continue,
                };
                let need = args
                    .iter()
                    .map(|a| {
                        i.where_
                            .iter()
                            .any(|c| is_debug(&c.class) && same_var(&c.ty, a))
                    })
                    .collect();
                out.insert(key(head), need);
            }
            Stmt::Mutual { items, .. } => written(items, out),
            _ => {}
        }
    }
}

fn same_var(a: &SurfaceTerm, b: &SurfaceTerm) -> bool {
    matches!((&*a.kind, &*b.kind), (TermKind::Var(x), TermKind::Var(y)) if x.as_str() == y.as_str())
}

/// Adds to `need` the generics of `d` that the type `t` asks `Debug` of;
/// false when the obligation cannot be reduced to them.
fn reduce(t: &SurfaceTerm, generics: &[Name], table: &Table, ids: &Ids, need: &mut [bool]) -> bool {
    match &*t.kind {
        // A function shows as `fn { .. }`, asking nothing.
        TermKind::Pi { .. } | TermKind::FnKind { .. } => true,
        TermKind::Borrow { term, .. } => reduce(term, generics, table, ids, need),
        TermKind::Var(n) => {
            if let Some(i) = generics.iter().position(|g| g.as_str() == n.as_str()) {
                need[i] = true;
                true
            } else {
                !other(n, ids) && table.get(&key(n)).is_some_and(|p| p.is_empty())
            }
        }
        TermKind::App {
            function,
            arguments,
        } => {
            let TermKind::Var(h) = &*function.kind else {
                return false;
            };
            if generics.iter().any(|g| g.as_str() == h.as_str()) {
                return false;
            }
            let Some(p) = table.get(&key(h)) else {
                return false;
            };
            if other(h, ids) {
                return false;
            }
            if p.len() != arguments.len() {
                return false;
            }
            p.clone()
                .iter()
                .zip(arguments)
                // A function shows as `fn { .. }` only as a field itself: the
                // instance of a type applied to one has no instance to ask.
                .all(|(&asks, a)| !asks || (!is_fn(a) && reduce(a, generics, table, ids, need)))
        }
        _ => false,
    }
}

/// Whether the compiler shows the inside of `d`: every file that can name it
/// can see its inside.
fn shows_inside(d: &DataDecl) -> bool {
    !d.host && d.vis != Vis::Pub
}

/// The type names `t` mentions.
fn mentioned(t: &SurfaceTerm, out: &mut HashSet<String>) {
    let mut t = t.clone();
    walk::term(&mut t, &mut |t| {
        if let TermKind::Var(n) = &*t.kind {
            out.insert(key(n));
        }
    });
}

/// The recursive candidates (also through other types): their instance,
/// once passed on as a dictionary, is a function value the row check cannot
/// see stop, so it would perform `div`. The compiler writes none for them;
/// their file writes one with fuel (`docs/design/debug.md`).
fn nested(candidates: &[DataDecl]) -> HashSet<String> {
    components(candidates)
        .into_iter()
        .flatten()
        .map(|i| key(&candidates[i].name))
        .collect()
}

/// The groups of recursive candidates (by index): the types that each reach
/// the others, through their fields.
fn components(candidates: &[DataDecl]) -> Vec<Vec<usize>> {
    let names: HashSet<String> = candidates.iter().map(|d| key(&d.name)).collect();
    // The candidates each one's fields mention.
    let mut edges: HashMap<String, HashSet<String>> = HashMap::new();
    for d in candidates {
        let mut all = HashSet::new();
        for (_, t) in d.constructors.iter().flat_map(|c| &c.fields) {
            mentioned(t, &mut all);
        }
        all.retain(|n| names.contains(n));
        edges.insert(key(&d.name), all);
    }
    let reach = |from: &str| {
        let mut seen: HashSet<String> = HashSet::new();
        let mut todo = vec![from.to_string()];
        while let Some(n) = todo.pop() {
            for m in edges.get(&n).into_iter().flatten() {
                if seen.insert(m.clone()) {
                    todo.push(m.clone());
                }
            }
        }
        seen
    };
    let reaches: HashMap<String, HashSet<String>> =
        names.iter().map(|n| (n.clone(), reach(n))).collect();
    let mut done = vec![false; candidates.len()];
    let mut out = Vec::new();
    for (i, d) in candidates.iter().enumerate() {
        let k = key(&d.name);
        if done[i] || !reaches[&k].contains(&k) {
            continue;
        }
        let group: Vec<usize> = (0..candidates.len())
            .filter(|&j| {
                let e = key(&candidates[j].name);
                e == k || (reaches[&k].contains(&e) && reaches[&e].contains(&k))
            })
            .collect();
        for &j in &group {
            done[j] = true;
        }
        out.push(group);
    }
    out
}

/// Whether the types of `group` can be shown together, and with fuel (a
/// type recursive through itself alone) or without: each field
/// that mentions one of them is the type itself (applied to its own
/// generics, when it is alone), or, for types without generics, one of them
/// or a `List` or an `Option` of one.
fn fuelable(candidates: &[DataDecl], group: &[usize], nested: &HashSet<String>) -> Option<bool> {
    let decls: Vec<&DataDecl> = group.iter().map(|&i| &candidates[i]).collect();
    // The fields name a type by its spelling, which another candidate (a
    // syntax's `I` of each rule) may share.
    if decls.iter().any(|d| {
        candidates
            .iter()
            .filter(|e| key(&e.name) == key(&d.name))
            .count()
            != 1
    }) {
        return None;
    }
    if let [d] = decls.as_slice()
        && only_itself(d, nested)
    {
        return Some(true);
    }
    decls.iter().all(|d| d.generics.is_empty()).then_some(false)
}

/// Whether every field of `d` that mentions a recursive type is `d` itself,
/// with its own generics in order.
fn only_itself(d: &DataDecl, nested: &HashSet<String>) -> bool {
    let own = key(&d.name);
    d.constructors.iter().flat_map(|c| &c.fields).all(|(_, t)| {
        let mut all = HashSet::new();
        mentioned(t, &mut all);
        if !all.iter().any(|n| nested.contains(n)) {
            return true;
        }
        match &*t.kind {
            TermKind::Var(n) => key(n) == own && d.generics.is_empty(),
            TermKind::App {
                function,
                arguments,
            } => {
                matches!(&*function.kind, TermKind::Var(n) if key(n) == own)
                    && arguments.len() == d.generics.len()
                    && arguments.iter().zip(&d.generics).all(
                        |(a, g)| matches!(&*a.kind, TermKind::Var(n) if n.as_str() == g.as_str()),
                    )
            }
            _ => false,
        }
    })
}

/// The `where` of each instance the compiler writes for `candidates`, or none
/// for a type whose fields cannot be reduced. The instances are assumed for
/// their own fields, so recursion settles at the least set.
fn infer(
    candidates: &[DataDecl],
    mut table: Table,
    ids: &Ids,
    hidden: &dyn Fn(&DataDecl, &SurfaceTerm) -> bool,
) -> HashMap<String, Vec<bool>> {
    let mut ok: HashSet<String> = HashSet::new();
    for d in candidates {
        table.insert(key(&d.name), vec![false; d.generics.len()]);
        ok.insert(key(&d.name));
    }
    loop {
        let mut changed = false;
        for d in candidates {
            let k = key(&d.name);
            if !ok.contains(&k) || !shows_inside(d) || d.rows.iter().any(|r| *r) {
                if d.rows.iter().any(|r| *r) && ok.remove(&k) {
                    table.remove(&k);
                    changed = true;
                }
                continue;
            }
            let mut need = table[&k].clone();
            // Another declaration spelled the same may have put its own entry here.
            need.resize(d.generics.len(), false);
            let fits = d
                .constructors
                .iter()
                .flat_map(|c| &c.fields)
                .all(|(_, t)| hidden(d, t) || reduce(t, &d.generics, &table, ids, &mut need));
            if !fits {
                ok.remove(&k);
                table.remove(&k);
                changed = true;
            } else if need != table[&k] {
                table.insert(k, need);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    table.retain(|k, _| ok.contains(k));
    table
}

fn quote(s: &str) -> String {
    format!("{s:?}")
}

/// Nested `concat`s of the parts, as written text.
fn concat(parts: &[String]) -> String {
    match parts {
        [] => "\"\"".into(),
        [one] => one.clone(),
        [first, rest @ ..] => format!("concat({first}, {})", concat(rest)),
    }
}

fn is_fn(t: &SurfaceTerm) -> bool {
    match &*t.kind {
        TermKind::Pi { .. } | TermKind::FnKind { .. } => true,
        TermKind::Borrow { term, .. } => is_fn(term),
        _ => false,
    }
}

/// How a recursive group shows a field of type `t`, by the placeholders of
/// its functions: by a call of the function of a type of the group (with the
/// fuel left, when it has fuel), or a `List` or an `Option` of one.
enum Shown {
    /// A field the group cannot show through its own functions: `..`, as a
    /// function is.
    Hidden,
    Call(String, bool),
    List(String),
    Option(String),
}

type Go<'a> = &'a dyn Fn(&SurfaceTerm) -> Option<Shown>;

fn value(binder: &str, t: &SurfaceTerm, go: Option<Go>) -> String {
    if is_fn(t) {
        quote("..")
    } else if let Some(shown) = go.and_then(|go| go(t)) {
        match shown {
            Shown::Hidden => quote(".."),
            Shown::Call(f, true) => format!("{f}(&{binder}, {FUEL_LEFT})"),
            Shown::Call(f, false) => format!("{f}(&{binder})"),
            Shown::List(items) => {
                format!("concat(\"[\", concat({items}(&{binder}), \"]\"))")
            }
            Shown::Option(f) => format!(
                "match &{binder} {{\n None => \"None\"\n Some(debug__x) => concat(\"Some(\", concat({f}(&debug__x), \")\"))\n }}"
            ),
        }
    } else {
        format!("Debug::debug(&{binder})")
    }
}

/// The local function of a recursive type's instance, the fuel it is given,
/// and the fuel left for the fields of the type itself. Deeper than the fuel,
/// a value shows as `..`, so the instance stops without `div`.
const FUEL_LEFT: &str = "debug__left";
const FUEL: u32 = 64;

/// The placeholders of the names of the `tag`th type of a source: its own,
/// its constructors', and the function that shows it with fuel.
fn type_placeholder(tag: usize) -> String {
    format!("debug__Type{tag}")
}

fn ctor_placeholder(tag: usize, i: usize) -> String {
    format!("debug__Ctor{tag}_{i}")
}

fn fuel_placeholder(tag: usize) -> String {
    format!("debug__go{tag}")
}

/// The fields of a constructor as shown and as matched: `C(x, y)` or
/// `C { f: x }`, with the binders `b0`, `b1`, ….
fn shown_fields(
    name: &str,
    fields: &[(Option<String>, SurfaceTerm)],
    binder: &dyn Fn(usize) -> String,
    go: Option<Go>,
) -> Vec<String> {
    if fields.is_empty() {
        return vec![quote(name)];
    }
    let named = fields.iter().all(|(n, _)| n.is_some());
    let mut parts = vec![quote(&format!("{name}{}", if named { " { " } else { "(" }))];
    // A function field shows as `..`: a named one is left out, and the
    // braces end with `..` (`Secret { .. }` hides the same way).
    let mut first = true;
    let mut hidden = false;
    for (i, (n, t)) in fields.iter().enumerate() {
        if named && (is_fn(t) || matches!(go.and_then(|go| go(t)), Some(Shown::Hidden))) {
            hidden = true;
            continue;
        }
        let sep = if first { "" } else { ", " };
        first = false;
        match n {
            Some(n) if named => {
                parts.push(quote(&format!("{sep}{}: ", n.trim_start_matches("r#"))))
            }
            _ if !sep.is_empty() => parts.push(quote(sep)),
            _ => {}
        }
        parts.push(value(&binder(i), t, go));
    }
    if hidden {
        parts.push(quote(if first { ".." } else { ", .." }));
    }
    parts.push(quote(if named { " }" } else { ")" }));
    parts
}

/// The text of the instance for `d`, with placeholders for the type's and the
/// constructors' names.
///
/// The `tag`th type of its source; with `go`, the function that shows it with
/// fuel comes first, and the instance calls it.
fn text(
    d: &DataDecl,
    need: &[bool],
    is_struct: bool,
    go: Option<Go>,
    fuel: bool,
    tag: usize,
) -> (Option<String>, String) {
    let display = last(&d.name);
    let ty = type_placeholder(tag);
    let fuel_fn = fuel_placeholder(tag);
    // A type of a module shows with the module in front (`math::Eqn`).
    let shown_name = d.name.as_str().to_string();
    let generics: Vec<&str> = d.generics.iter().map(|g| g.as_str()).collect();
    let head = if generics.is_empty() {
        ty.clone()
    } else {
        format!("{ty}({})", generics.join(", "))
    };
    let binders = if generics.is_empty() {
        String::new()
    } else {
        format!("<{}>", generics.join(", "))
    };
    let constraints: Vec<String> = generics
        .iter()
        .zip(need)
        .filter(|(_, n)| **n)
        .map(|(g, _)| format!("Debug({g})"))
        .collect();
    let where_ = if constraints.is_empty() {
        String::new()
    } else {
        format!(" where {}", constraints.join(", "))
    };
    let body = if !shows_inside(d) {
        quote(&format!("{shown_name} {{ .. }}"))
    } else if is_struct && d.constructors.len() == 1 && (go.is_none() || fuel) {
        let c = &d.constructors[0];
        let fields: Vec<String> = c
            .fields
            .iter()
            .enumerate()
            .map(|(i, (n, _))| match n {
                // The fields of a struct with a `coerce` field are its own only by
                // the qualified name.
                Some(n) if d.coerce.is_some() => {
                    format!("a.{display}::r#{}", n.trim_start_matches("r#"))
                }
                Some(n) => format!("a.r#{}", n.trim_start_matches("r#")),
                None => format!("a.{i}"),
            })
            .collect();
        concat(&shown_fields(
            &shown_name,
            &c.fields,
            &|i| fields[i].clone(),
            go,
        ))
    } else if d.constructors.is_empty() {
        quote(&shown_name)
    } else {
        let arms: Vec<String> = d
            .constructors
            .iter()
            .enumerate()
            .map(|(ci, c)| {
                let placeholder = ctor_placeholder(tag, ci);
                let named = !c.fields.is_empty() && c.fields.iter().all(|(n, _)| n.is_some());
                let pattern = if c.fields.is_empty() {
                    placeholder.clone()
                } else if named {
                    let fs: Vec<String> = c
                        .fields
                        .iter()
                        .enumerate()
                        .map(|(i, (n, _))| {
                            format!(
                                "r#{}: b{i}",
                                n.as_deref().unwrap_or("").trim_start_matches("r#")
                            )
                        })
                        .collect();
                    format!("{placeholder} {{ {} }}", fs.join(", "))
                } else {
                    let bs: Vec<String> = (0..c.fields.len()).map(|i| format!("b{i}")).collect();
                    format!("{placeholder}({})", bs.join(", "))
                };
                let ctor_name = if is_struct {
                    shown_name.clone()
                } else {
                    last(&c.name)
                };
                let shown = concat(&shown_fields(
                    &ctor_name,
                    &c.fields,
                    &|i| format!("b{i}"),
                    go,
                ));
                format!("    {pattern} => {shown}\n")
            })
            .collect();
        format!("match a {{\n{}  }}", arms.concat())
    };
    let instance = |body: &str| {
        format!(
            "instance{binders} Debug({head}){where_} {{\n  fn debug(a: &{head}): Text {{\n  {body}\n  }}\n}}\n"
        )
    };
    if go.is_some() && !fuel {
        // A group of types recursive through each other: top-level functions
        // that take their parameter apart by `match`, which the row check
        // sees end.
        (
            Some(format!(
                "fn {fuel_fn}{binders}(a: &{head}): Text{where_} {{\n  {body}\n}}\n"
            )),
            instance(&format!("{fuel_fn}(a)")),
        )
    } else if go.is_some() {
        // A top-level function: the row check sees its fuel go down, which it
        // does not for a local one.
        (
            Some(format!(
                "fn {fuel_fn}{binders}(a: &{head}, debug__fuel: u64): Text{where_} {{\n  if debug__fuel == 0 {{ \"..\" }} else {{\n  let {FUEL_LEFT} := U64::wrapping_sub(debug__fuel, 1)\n  {body}\n  }}\n}}\n"
            )),
            instance(&format!("{fuel_fn}(a, {FUEL})")),
        )
    } else {
        (None, instance(&body))
    }
}

/// A container whose elements are types of a fueled group, shown by a
/// function of the group's: `List(T)` or `Option(T)` of the `i`th member.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Container {
    List,
    Option,
}

impl Container {
    fn of(name: &str) -> Option<Self> {
        match name {
            "List" => Some(Container::List),
            "Option" => Some(Container::Option),
            _ => None,
        }
    }
    fn tag(self) -> &'static str {
        match self {
            Container::List => "list",
            Container::Option => "option",
        }
    }
}

/// The member of `members` a field type is, or the container of one.
fn shown_by(t: &SurfaceTerm, members: &[&DataDecl]) -> Option<(Option<Container>, usize)> {
    let at = |n: &Name| members.iter().position(|m| key(&m.name) == key(n));
    match &*t.kind {
        TermKind::Var(n) => at(n).map(|i| (None, i)),
        TermKind::App {
            function,
            arguments,
        } => {
            let TermKind::Var(h) = &*function.kind else {
                return None;
            };
            if let Some(i) = at(h) {
                return Some((None, i));
            }
            let c = Container::of(&last(h))?;
            match arguments.as_slice() {
                [a] => match &*a.kind {
                    TermKind::Var(n) => at(n).map(|i| (Some(c), i)),
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

fn container_placeholder(c: Container, i: usize) -> String {
    format!("debug__{}{i}", c.tag())
}

/// The functions that show the elements of a `List` of the `i`th member: the
/// items, after a first one, each taking its list apart by `match`.
fn items_text(i: usize) -> String {
    let item = type_placeholder(i);
    let go = fuel_placeholder(i);
    let this = container_placeholder(Container::List, i);
    format!(
        "fn {this}_items(xs: &List({item})): Text {{\n  match xs {{\n    Nil => \"\"\n    Cons(x, rest) => concat({go}(&x), {this}_after(&rest))\n  }}\n}}\n\
         fn {this}_after(xs: &List({item})): Text {{\n  match xs {{\n    Nil => \"\"\n    Cons(x, rest) => concat(\", \", concat({go}(&x), {this}_after(&rest)))\n  }}\n}}\n"
    )
}

/// The instances for `members`, which are the types of a recursive group,
/// with the functions they call, written as one function each. The functions
/// of a group take their parameter apart by `match` and call one another on
/// its parts, which the row check sees end; a type recursive through itself
/// alone is shown with `fuel` instead. Without `group`, `members` is one
/// type. Placeholders are replaced by the names of the types.
fn instance(
    members: &[(&DataDecl, &[bool], bool)],
    group: bool,
    fuel: bool,
    base: u32,
    resolved: bool,
) -> Option<Vec<Stmt>> {
    let _ = base;
    let decls: Vec<&DataDecl> = members.iter().map(|m| m.0).collect();
    let names: HashSet<String> = decls.iter().map(|d| key(&d.name)).collect();
    let go = |t: &SurfaceTerm| -> Option<Shown> {
        let shown = shown_by(t, &decls);
        if shown.is_none() {
            let mut all = HashSet::new();
            mentioned(t, &mut all);
            return all
                .iter()
                .any(|n| names.contains(n))
                .then_some(Shown::Hidden);
        }
        shown.map(|(c, i)| match c {
            None => Shown::Call(fuel_placeholder(i), fuel),
            Some(Container::List) => Shown::List(format!(
                "{}_items",
                container_placeholder(Container::List, i)
            )),
            Some(Container::Option) => Shown::Option(fuel_placeholder(i)),
        })
    };
    let mut fns = String::new();
    let mut instances = String::new();
    for (tag, (d, need, is_struct)) in members.iter().enumerate() {
        let (f, i) = text(d, need, *is_struct, group.then_some(&go as Go), fuel, tag);
        fns.extend(f);
        instances.push_str(&i);
    }
    let mut helpers: Vec<usize> = Vec::new();
    if group {
        for (d, _, _) in members {
            for (_, t) in d.constructors.iter().flat_map(|c| &c.fields) {
                if let Some((Some(Container::List), i)) = shown_by(t, &decls)
                    && !helpers.contains(&i)
                {
                    helpers.push(i);
                }
            }
        }
    }
    for i in &helpers {
        fns.push_str(&items_text(*i));
    }
    let last = *decls.iter().max_by_key(|d| d.span.start)?;
    // Top-level functions, which call each other whichever is declared first.
    let source = format!("{fns}{instances}");
    let base = place(last, &source);
    let program = crate::surface::parse_program_unresolved_at(&source, base).ok()?;
    let (mut stmts, errors) = crate::surface::modules::resolve(program.stmts);
    if !errors.is_empty() || !program.errors.is_empty() {
        return None;
    }
    let instances = stmts
        .iter()
        .filter(|s| matches!(s, Stmt::Instance(_)))
        .count();
    let shape_ok = instances == members.len() && stmts.len() > instances
        || !group
            && stmts
                .iter()
                .take(stmts.len() - instances)
                .all(|s| matches!(s, Stmt::Fn(_)));
    if !shape_ok {
        return None;
    }
    // Named with `@`, as the functions of instances are: no file can write
    // it or declare it again.
    let mut names: HashMap<String, Name> = HashMap::new();
    for (tag, d) in decls.iter().enumerate() {
        names.insert(type_placeholder(tag), d.name.clone());
        names.insert(
            fuel_placeholder(tag),
            format!("debug@fuel@{}@{}", key(&d.name), d.span.start).into(),
        );
        for (i, c) in d.constructors.iter().enumerate() {
            names.insert(ctor_placeholder(tag, i), c.name.clone());
        }
    }
    for i in &helpers {
        let d = decls[*i];
        for suffix in ["_items", "_after"] {
            names.insert(
                format!("{}{suffix}", container_placeholder(Container::List, *i)),
                format!("debug@fuel@list{suffix}@{}@{}", key(&d.name), d.span.start).into(),
            );
        }
    }
    for s in &mut stmts {
        if let Stmt::Fn(f) = s {
            rename_fn(f, &names);
        }
        walk::stmt(s, &mut |t| rename(t, &names));
    }
    if resolved {
        tauto_surface::resolve::Resolver::new(
            tauto_surface::bindings::library_definition_bindings(),
        )
        .statements(&mut stmts);
    }
    Some(stmts)
}

fn rename_fn(f: &mut tauto_surface::surface::FnDecl, names: &HashMap<String, Name>) {
    if let Some(n) = names.get(f.name.as_str()) {
        f.name = n.clone();
    }
}

fn rename(t: &mut SurfaceTerm, names: &HashMap<String, Name>) {
    let kind = Arc::make_mut(&mut t.kind);
    match kind {
        TermKind::Var(n) | TermKind::Record { name: n, .. } => {
            if let Some(r) = names.get(n.as_str()) {
                *n = r.clone();
            }
        }
        TermKind::Match { arms, .. } => {
            for a in arms {
                rename_pattern(&mut a.pattern, names);
            }
        }
        _ => {}
    }
}

fn rename_pattern(p: &mut Pattern, names: &HashMap<String, Name>) {
    match p {
        Pattern::Bind { name: n, .. } => {
            if let Some(r) = names.get(n.as_str()) {
                *p = Pattern::Ctor {
                    name: r.clone(),
                    args: Vec::new(),
                };
            }
        }
        Pattern::Ctor { name, args } => {
            if let Some(r) = names.get(name.as_str()) {
                *name = r.clone();
            }
            args.iter_mut().for_each(|a| rename_pattern(a, names));
        }
        Pattern::Record { name, fields } => {
            if let Some(r) = names.get(name.as_str()) {
                *name = r.clone();
            }
            fields
                .iter_mut()
                .for_each(|(_, a)| rename_pattern(a, names));
        }
        _ => {}
    }
}

fn declares_debug(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Class(c) => is_debug(&c.name),
        Stmt::Mutual { items, .. } => declares_debug(items),
        _ => false,
    })
}

/// The instances the compiler writes for the types of `program`, after the
/// statement that declares each type, in `program` and in the file of
/// `per_file` that declares it. `prelude` is where the class and the
/// instances of the types the program does not declare are; `None` when
/// `program` is the prelude.
pub(super) fn add_instances(
    program: &mut Program,
    per_file: &mut [Vec<Stmt>],
    prelude: Option<&Program>,
) {
    let outer = prelude.map(|p| p.stmts.as_slice()).unwrap_or(&[]);
    if !declares_debug(&program.stmts) && !declares_debug(outer) {
        return;
    }
    let mut table = Table::new();
    if let Some(p) = prelude {
        // The prelude's own types have theirs already, written or made.
        written(&p.stmts, &mut table);
    }
    // A program that holds the prelude's declarations again (a library read
    // with the prelude it is checked against) makes none for them twice.
    // A head is the same type when it is the same declaration; a program
    // whose names are not resolved yet has only their spellings.
    let prelude_heads: HashSet<String> = table.keys().cloned().collect();
    let prelude_names: HashSet<Name> = prelude.map(|p| heads(&p.stmts)).unwrap_or_default();
    // A type the program declares in its own text is its own, though a
    // prelude type is spelled the same: only a copy of the prelude's
    // declarations (at the prelude's spans) is the prelude's.
    let in_prelude = |n: &Name, at: u32| {
        if n.as_global().is_some() {
            prelude_names.contains(n)
        } else {
            at >= crate::surface::PRELUDE_BASE && prelude_heads.contains(&key(n))
        }
    };
    let mut ids = Ids::new();
    if let Some(p) = prelude {
        written_ids(&p.stmts, &mut ids);
    }
    written_ids(&program.stmts, &mut ids);
    let mut own_written = Table::new();
    written(&program.stmts, &mut own_written);
    table.extend(own_written.clone());
    let mut candidates = Vec::new();
    datas(&program.stmts, &mut candidates);
    // A type with `struct &T` is not shown by a derived `Debug`: its `&T`
    // does not hold the fields.
    let lent: HashSet<String> = candidates
        .iter()
        .filter(|d| d.borrowed)
        .map(|d| d.name.as_str().trim_start_matches('&').to_string())
        .collect();
    candidates.retain(|d| !d.borrowed && !lent.contains(d.name.as_str()));
    let mut seen = HashSet::new();
    candidates.retain(|d| seen.insert((d.span.start, d.span.end, key(&d.name))));
    // A `Slice` is only ever borrowed, so it cannot be an instance's head.
    candidates.retain(|d| {
        (!own_written.contains_key(&key(&d.name)) || other(&d.name, &ids))
            && !in_prelude(&d.name, d.span.start)
            && !tauto_surface::bindings::is_library(&d.name, "Slice")
    });
    if candidates.is_empty() {
        return;
    }
    let resolved = super::has_references(program);
    let structs: HashSet<String> = struct_names(&program.stmts);
    let nested = nested(&candidates);
    // A group of types recursive only through each other (and `List`s and
    // `Option`s of them) gets instances with fuel; one recursive through
    // other types gets none.
    let groups: Vec<(Vec<String>, bool)> = components(&candidates)
        .into_iter()
        .filter_map(|g| {
            let fuel = fuelable(&candidates, &g, &nested)?;
            Some((g.iter().map(|&i| key(&candidates[i].name)).collect(), fuel))
        })
        .collect();
    let fueled: HashSet<String> = groups.iter().flat_map(|g| g.0.clone()).collect();
    candidates.retain(|d| !nested.contains(&key(&d.name)) || fueled.contains(&key(&d.name)));
    // A type the instance is written for is the type its fields name by its
    // spelling, though a prelude type is spelled the same.
    for d in &candidates {
        if let Some(r) = d.name.as_global() {
            ids.entry(key(&d.name))
                .or_default()
                .insert(format!("{r:?}"));
        }
    }
    // A field of a group that its functions do not show (it is recursive in
    // a way they do not follow) shows as `..`, asking nothing.
    let hidden = |d: &DataDecl, t: &SurfaceTerm| {
        let Some((members, false)) = groups
            .iter()
            .find(|(g, _)| g.contains(&key(&d.name)))
            .map(|(g, fuel)| (g, *fuel))
        else {
            return false;
        };
        let decls: Vec<&DataDecl> = candidates
            .iter()
            .filter(|c| members.contains(&key(&c.name)))
            .collect();
        let mut all = HashSet::new();
        mentioned(t, &mut all);
        shown_by(t, &decls).is_none() && all.iter().any(|n| members.contains(n))
    };
    let inferred = infer(&candidates, table, &ids, &hidden);
    let mut made: Vec<(tauto_parol::Span, Stmt)> = Vec::new();
    // The prelude's instances and a program's must not share spans.
    let mut base = if prelude.is_some() {
        BASE + (1 << 27)
    } else {
        BASE
    };
    let need_of = |d: &DataDecl| {
        let need = inferred.get(&key(&d.name))?;
        Some(if shows_inside(d) {
            need.clone()
        } else {
            vec![false; d.generics.len()]
        })
    };
    for d in &candidates {
        if fueled.contains(&key(&d.name)) {
            continue;
        }
        let Some(need) = need_of(d) else {
            continue;
        };
        if let Some(stmts) = instance(
            &[(d, &need, structs.contains(&key(&d.name)))],
            false,
            false,
            base,
            resolved,
        ) {
            base += 1 << 14;
            made.extend(stmts.into_iter().map(|s| (d.span, s)));
        }
    }
    // A group is made in one place, after the last type it declares, where
    // all of them are known. It gets none when one of its types gets none.
    for (g, fuel) in &groups {
        let members: Vec<&DataDecl> = g
            .iter()
            .filter_map(|k| candidates.iter().find(|d| key(&d.name) == *k))
            .collect();
        let needs: Vec<Option<Vec<bool>>> = members.iter().map(|d| need_of(d)).collect();
        if needs.iter().any(|n| n.is_none()) || members.len() != g.len() {
            continue;
        }
        let parts: Vec<(&DataDecl, &[bool], bool)> = members
            .iter()
            .zip(&needs)
            .map(|(d, n)| {
                (
                    *d,
                    n.as_deref().unwrap_or(&[]),
                    structs.contains(&key(&d.name)),
                )
            })
            .collect();
        let Some(last) = members.iter().map(|d| d.span).max_by_key(|s| s.start) else {
            continue;
        };
        if let Some(stmts) = instance(&parts, true, *fuel, base, resolved) {
            base += 1 << 14;
            made.extend(stmts.into_iter().map(|s| (last, s)));
        }
    }
    insert(&mut program.stmts, &made);
    for file in per_file {
        insert(file, &made);
    }
}

fn struct_names(stmts: &[Stmt]) -> HashSet<String> {
    let mut out = HashSet::new();
    for s in stmts {
        match s {
            Stmt::Struct(d) => {
                out.insert(key(&d.name));
            }
            Stmt::Mutual { items, .. } => out.extend(struct_names(items)),
            _ => {}
        }
    }
    out
}

/// Where the spans of the instance made for `d` from `source` start: the
/// same place each time it is made in a process, and a place no other made
/// instance has, so that the instances of programs read apart and checked
/// together (a tote and its dependencies) have no term in common.
fn place(d: &DataDecl, source: &str) -> u32 {
    type Places = (u32, HashMap<(u32, u32, String, String), u32>);
    static PLACES: std::sync::Mutex<Option<Places>> = std::sync::Mutex::new(None);
    let mut places = PLACES.lock().expect("instance places");
    let (next, made) = places.get_or_insert_with(|| (BASE, HashMap::new()));
    let k = (d.span.start, d.span.end, key(&d.name), source.to_string());
    if let Some(&at) = made.get(&k) {
        return at;
    }
    let at = *next;
    *next += source.len() as u32 + 1;
    made.insert(k, at);
    at
}

/// Each instance after the top-level statement that declares its type.
fn insert(stmts: &mut Vec<Stmt>, made: &[(tauto_parol::Span, Stmt)]) {
    let mut out = Vec::with_capacity(stmts.len() + made.len());
    // A declaration read twice (a library that holds the prelude again) gets
    // its instance once.
    let mut placed = vec![false; made.len()];
    for s in std::mem::take(stmts) {
        let spans = declared_spans(&s);
        out.push(s);
        for (k, (span, i)) in made.iter().enumerate() {
            if spans.contains(span) && !placed[k] {
                placed[k] = true;
                out.push(i.clone());
            }
        }
    }
    *stmts = out;
}

fn declared_spans(s: &Stmt) -> Vec<tauto_parol::Span> {
    match s {
        Stmt::Struct(d) | Stmt::Enum(d) => vec![d.span],
        Stmt::Mutual { items, .. } => items.iter().flat_map(declared_spans).collect(),
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::super::{check_program, expand_classes};

    fn errors(source: &str) -> Vec<String> {
        let program = expand_classes(
            crate::surface::parse_program_as_written(source).expect("parses"),
            1 << 30,
        );
        check_program(&program)
            .errors
            .iter()
            .map(|e| e.message.to_string())
            .collect()
    }

    #[test]
    fn a_struct_and_an_enum_get_instances() {
        tauto_parse::install();
        let found = errors(
            "struct Point { x: i64, y: i64 }
             enum Shape { Circle(i64), Square { side: Point }, Empty }
             fn f(s: Shape): Text { debug(&s) }",
        );
        assert!(found.is_empty(), "{found:?}");
    }

    #[test]
    fn types_recursive_through_each_other_and_lists_get_instances() {
        tauto_parse::install();
        let found = errors(
            "enum Tree { Leaf(u64), Node(Forest) }
             struct Forest { kids: List(Tree), extra: Option(Tree) }
             fn f(t: Tree): Text { debug(&t) }",
        );
        assert!(found.is_empty(), "{found:?}");
    }

    #[test]
    fn an_asked_parameter_must_be_debug() {
        tauto_parse::install();
        let found = errors(
            "struct Boxed(A: Type) { item: List(A) }
             fn f<A>(b: Boxed(A)): Text { debug(&b) }",
        );
        assert!(!found.is_empty());
    }

    #[test]
    fn a_written_instance_is_the_one() {
        tauto_parse::install();
        let found = errors(
            "struct Point { x: i64 }
             instance Debug(Point) { fn debug(a: &Point): Text { \"p\" } }
             fn f(p: Point): Text { debug(&p) }",
        );
        assert!(found.is_empty(), "{found:?}");
    }
}
