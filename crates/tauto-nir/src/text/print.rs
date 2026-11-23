//! The printer: a package, or one function of it, as text.

use std::collections::HashMap;
use std::fmt::Write;

use super::*;

mod blocks;
pub use blocks::print_blocks;

/// The package as text. `Err` says what the text cannot state: a reference
/// that names nothing in the package, or two things under one name.
pub fn print(pkg: &Package) -> Result<String, String> {
    check(pkg)?;
    let mut p = Printer::new(pkg);
    p.package()?;
    Ok(p.out)
}

/// One function of the package as text: what `print` writes for it.
pub fn print_fn(pkg: &Package, f: &FnInst) -> Result<String, String> {
    let mut p = Printer::new(pkg);
    p.function(f)?;
    Ok(p.out)
}

/// One expression as text, as it is written inside a function.
pub fn print_expr(pkg: &Package, e: &Expr) -> Result<String, String> {
    let mut p = Printer::new(pkg);
    p.expr(e)?;
    Ok(p.out)
}

/// One data type of the package as text: what `print` writes for it.
pub fn print_data(pkg: &Package, d: &DataDef) -> String {
    let mut p = Printer::new(pkg);
    p.data(d);
    p.out
}

/// The evidence of the package as text: the `evidence` lines `print` writes.
pub fn print_evidence(pkg: &Package) -> Result<String, String> {
    let mut p = Printer::new(pkg);
    p.evidence()?;
    Ok(p.out)
}

/// What reading the text back relies on: every name the text refers to by
/// its spelling names one thing.
fn check(pkg: &Package) -> Result<(), String> {
    let mut seen = std::collections::HashSet::new();
    for d in &pkg.datas {
        if !seen.insert(d.name.as_str()) {
            return Err(format!("two data types are named {}", d.name));
        }
    }
    let mut seen = std::collections::HashSet::new();
    for c in pkg.datas.iter().flat_map(|d| &d.ctors) {
        if !seen.insert(c.name.as_str()) {
            return Err(format!("two constructors are named {}", c.name));
        }
    }
    let mut seen = std::collections::HashSet::new();
    for o in &pkg.ops {
        if !seen.insert(o.name.as_str()) {
            return Err(format!("two operations are named {}", o.name));
        }
    }
    for (i, f) in pkg.fns.iter().enumerate() {
        if f.id != i {
            return Err(format!("function {} of the package has the id {}", i, f.id));
        }
    }
    for (i, u) in pkg.unions.iter().enumerate() {
        if u.id != i {
            return Err(format!("union {} of the package has the id {}", i, u.id));
        }
    }
    Ok(())
}

pub(super) struct Printer<'a> {
    pkg: &'a Package,
    pub(super) out: String,
    indent: usize,
    /// How each local was bound: its representation and its type.
    bound: HashMap<u32, (Repr, Option<Ty>)>,
}

type R = Result<(), String>;

fn name(out: &mut String, n: &str) {
    if is_bare(n) {
        out.push_str(n);
    } else {
        write!(out, "${n:?}").unwrap();
    }
}

impl<'a> Printer<'a> {
    pub(super) fn new(pkg: &'a Package) -> Self {
        Printer {
            pkg,
            out: String::new(),
            indent: 0,
            bound: HashMap::new(),
        }
    }

    fn s(&mut self, text: &str) {
        self.out.push_str(text);
    }

    fn name(&mut self, n: &str) {
        name(&mut self.out, n);
    }

    fn line(&mut self) {
        self.out.push('\n');
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
    }

    fn list<T>(&mut self, items: &[T], mut each: impl FnMut(&mut Self, &T) -> R) -> R {
        for (i, x) in items.iter().enumerate() {
            if i > 0 {
                self.s(", ");
            }
            each(self, x)?;
        }
        Ok(())
    }

    fn package(&mut self) -> R {
        let pkg = self.pkg;
        if !pkg.declarations.is_empty() {
            self.s("declarations(");
            self.list(&pkg.declarations, |p, d| {
                p.name(d.display());
                Ok(())
            })?;
            self.s(")\n\n");
        }
        for s in &pkg.syntax_parsers {
            self.s("syntax ");
            write!(self.out, "{:?} sha {:?} result ", s.name, s.sha).unwrap();
            self.ty(&s.result);
            write!(self.out, " tables {:?} data(", s.tables).unwrap();
            let datas: Vec<_> = s.data_bindings.iter().collect();
            self.list(&datas, |p, (label, n)| {
                write!(p.out, "{label:?} = ").unwrap();
                p.name(n);
                Ok(())
            })?;
            self.s(") constructors(");
            let ctors: Vec<_> = s.constructor_bindings.iter().collect();
            self.list(&ctors, |p, ((data, ctor), n)| {
                write!(p.out, "{data:?}.{ctor:?} = ").unwrap();
                p.name(n);
                Ok(())
            })?;
            self.s(")\n\n");
        }
        for d in &pkg.datas {
            self.data(d);
        }
        for u in &pkg.unions {
            write!(self.out, "union {} {} (", u.id, u.kind).unwrap();
            self.tys(&u.members);
            self.s(")\n\n");
        }
        for o in &pkg.ops {
            write!(self.out, "op {} ", o.id).unwrap();
            self.name(&o.name);
            self.generics(&o.generics);
            self.s("(");
            self.tys(&o.params);
            self.s("): ");
            self.ty(&o.result);
            self.s(" ");
            self.quant(o.quant);
            self.s("\n\n");
        }
        for e in &pkg.externs {
            self.s("extern fn ");
            self.name(&e.name);
            self.generics(&e.generics);
            self.s("(");
            self.list(&e.params, |p, (n, t, pass)| {
                match pass {
                    Pass::Value => {}
                    Pass::Ref => p.s("ref "),
                    Pass::RefMut => p.s("refmut "),
                }
                p.name(n);
                p.s(": ");
                p.ty(t);
                Ok(())
            })?;
            self.s("): ");
            self.ty(&e.ret);
            if let Some(lends) = &e.lends {
                self.s(" lends(");
                for (i, l) in lends.iter().enumerate() {
                    if i > 0 {
                        self.s(", ");
                    }
                    write!(self.out, "{l}").unwrap();
                }
                self.s(")");
            }
            if e.waits {
                self.s(" waits");
            }
            self.s("\n\n");
        }
        for f in &pkg.fns {
            self.function(f)?;
            self.s("\n\n");
        }
        if let Some(top) = pkg.top {
            self.s("top ");
            self.inst(top)?;
            self.s("\n");
        }
        for e in &pkg.exports {
            write!(self.out, "export {:?} = ", e.name).unwrap();
            self.inst(e.inst)?;
            self.s(" row(");
            self.list(&e.row, |p, r| {
                write!(p.out, "{r:?}").unwrap();
                Ok(())
            })?;
            self.s(") foreign_row(");
            self.list(&e.foreign_row, |p, r| {
                write!(p.out, "{r:?}").unwrap();
                Ok(())
            })?;
            self.s(") pure_borrow_callbacks(");
            self.list(&e.pure_borrow_callbacks, |p, i| {
                write!(p.out, "{i}").unwrap();
                Ok(())
            })?;
            self.s(")\n");
        }
        if pkg.sync {
            self.s("sync\n");
        }
        if !pkg.permissions.is_empty() {
            self.s("permissions(");
            self.list(&pkg.permissions, |p, x| {
                write!(p.out, "{x:?}").unwrap();
                Ok(())
            })?;
            self.s(")\n");
        }
        if let Some(u) = &pkg.rust_unsupported {
            self.s("unsupported ");
            self.message(&u.what);
            self.s("\n");
        }
        self.evidence()
    }

    fn evidence(&mut self) -> R {
        let pkg = self.pkg;
        let ev = &pkg.evidence;
        for (op, (params, answer)) in &ev.ops {
            self.s("evidence op ");
            self.op(*op)?;
            self.s("(");
            self.tys(params);
            self.s("): ");
            self.ty(answer);
            self.s("\n");
        }
        let mut fns: Vec<_> = ev.fns.iter().collect();
        fns.sort();
        for (f, ops) in fns {
            self.s("evidence fn ");
            self.inst(*f)?;
            self.s("(");
            self.list(ops, |p, o| p.op(*o))?;
            self.s(")\n");
        }
        let mut handles: Vec<_> = ev.handles.iter().collect();
        handles.sort();
        for (h, ops) in handles {
            write!(self.out, "evidence handle {h}(").unwrap();
            self.list(ops, |p, o| p.op(*o))?;
            self.s(")\n");
        }
        Ok(())
    }

    fn message(&mut self, m: &Message) {
        write!(self.out, "{:?}(", m.id).unwrap();
        for (i, (k, v)) in m.args.iter().enumerate() {
            if i > 0 {
                self.s(", ");
            }
            write!(self.out, "{k:?} = ").unwrap();
            match v {
                tauto_message::Value::Text(t) => write!(self.out, "{t:?}").unwrap(),
                tauto_message::Value::Number(n) => write!(self.out, "{n}").unwrap(),
                tauto_message::Value::Message(m) => self.message(m),
            }
        }
        self.s(")");
    }

    fn generics(&mut self, generics: &[String]) {
        if generics.is_empty() {
            return;
        }
        self.s("<");
        for (i, g) in generics.iter().enumerate() {
            if i > 0 {
                self.s(", ");
            }
            self.param(g);
        }
        self.s(">");
    }

    fn quant(&mut self, q: Quant) {
        self.s(match q {
            Quant::Zero => "resume 0",
            Quant::AtMostOne => "resume <=1",
            Quant::One => "resume 1",
            Quant::Many => "resume ω",
            Quant::Direct => "direct",
        });
    }

    fn indirect(&mut self, i: Indirect) {
        match i {
            Indirect::None => {}
            Indirect::Shared => self.s("shared "),
            Indirect::Unique => self.s("unique "),
        }
    }

    fn data(&mut self, d: &DataDef) {
        write!(
            self.out,
            "data {} {} ",
            d.kind,
            if d.is_struct { "struct" } else { "enum" }
        )
        .unwrap();
        self.name(&d.name);
        self.generics(&d.generics);
        for (on, word) in [
            (d.clone, "clone"),
            (d.copy, "copy"),
            (d.linear, "linear"),
            (d.view, "view"),
            (d.host, "host"),
        ] {
            if on {
                self.s(" ");
                self.s(word);
            }
        }
        if d.is_struct {
            write!(self.out, " as {:?}", d.shown).unwrap();
        }
        self.s(" {");
        self.indent += 1;
        for c in &d.ctors {
            self.line();
            self.name(&c.name);
            if !c.fields.is_empty() {
                self.s("(");
                for (i, f) in c.fields.iter().enumerate() {
                    if i > 0 {
                        self.s(", ");
                    }
                    self.indirect(f.indirect);
                    if let Some(n) = &f.name {
                        self.name(n);
                        self.s(": ");
                    }
                    self.ty(&f.ty);
                }
                self.s(")");
            }
            self.s(",");
        }
        self.indent -= 1;
        self.line();
        self.s("}\n\n");
    }

    fn inst(&mut self, id: InstId) -> R {
        let f = self
            .pkg
            .fns
            .get(id)
            .ok_or_else(|| format!("no function has the id {id}"))?;
        self.name(&f.source);
        write!(self.out, "@{id}").unwrap();
        Ok(())
    }

    fn op(&mut self, index: OpIndex) -> R {
        let o = self
            .pkg
            .ops
            .get(index)
            .ok_or_else(|| format!("no operation has the index {index}"))?;
        self.name(&o.name);
        Ok(())
    }

    fn tys(&mut self, tys: &[Ty]) {
        for (i, t) in tys.iter().enumerate() {
            if i > 0 {
                self.s(", ");
            }
            self.ty(t);
        }
    }

    pub(super) fn ty(&mut self, t: &Ty) {
        let one = |p: &mut Self, word: &str, a: &Ty| {
            p.s(word);
            p.s("(");
            p.ty(a);
            p.s(")");
        };
        let two = |p: &mut Self, word: &str, a: &Ty, b: &Ty| {
            p.s(word);
            p.s("(");
            p.ty(a);
            p.s(", ");
            p.ty(b);
            p.s(")");
        };
        match t {
            Ty::Int(w) => self.s(width_word(*w)),
            Ty::Bool => self.s("Bool"),
            Ty::Text => self.s("Text"),
            Ty::Unit => self.s("Unit"),
            Ty::Never => self.s("Never"),
            Ty::Float => self.s("Float"),
            Ty::Float32 => self.s("Float32"),
            Ty::Buf => self.s("Buf"),
            Ty::Shown => self.s("Shown"),
            Ty::Vec(a) => one(self, "Vec", a),
            Ty::Array(a) => one(self, "Array", a),
            Ty::Slice(a) => one(self, "Slice", a),
            Ty::Option(a) => one(self, "Option", a),
            Ty::Info(a) => one(self, "Info", a),
            Ty::BudgetAnswer(a) => one(self, "BudgetAnswer", a),
            Ty::Result(a, b) => two(self, "Result", a, b),
            Ty::Pair(a, b) => two(self, "Pair", a, b),
            Ty::SharedVar(copy, a) => {
                self.s("SharedVar(");
                if *copy {
                    self.s("copy, ");
                }
                self.ty(a);
                self.s(")");
            }
            Ty::Std(s, args) => {
                self.s("std ");
                self.s(s.name());
                if !args.is_empty() {
                    self.s("(");
                    self.tys(args);
                    self.s(")");
                }
            }
            Ty::Data(n, args) => {
                self.name(n);
                if !args.is_empty() {
                    self.s("(");
                    self.tys(args);
                    self.s(")");
                }
            }
            Ty::Union(id) => write!(self.out, "union({id})").unwrap(),
            Ty::Param(p) => {
                self.param(p);
            }
            Ty::Fn(f) => self.fn_ty(f),
            Ty::Ref(a) => {
                self.s("&");
                self.ty(a);
            }
            Ty::RefMut(a) => {
                self.s("&mut ");
                self.ty(a);
            }
        }
    }

    /// A type parameter. The mark tells it from a data type where the
    /// text of one function is read without the package's data types.
    fn param(&mut self, p: &str) {
        self.s("'");
        self.name(p);
    }

    fn fn_ty(&mut self, f: &FnTy) {
        self.s("fn(");
        self.tys(&f.params);
        self.s(") -> ");
        self.ty(&f.ret);
        write!(self.out, " {} {}", f.kind, tier_word(f.tier)).unwrap();
    }

    /// A local where it is bound.
    fn bind(&mut self, l: &Local, ty: Option<&Ty>) {
        if l.repr != Repr::Plain {
            self.s(repr_word(l.repr));
            self.s(" ");
        }
        self.local_name(l);
        self.bound.insert(l.id, (l.repr, ty.cloned()));
    }

    fn local_name(&mut self, l: &Local) {
        self.name(&l.name);
        write!(self.out, "#{}", l.id).unwrap();
    }

    /// A local where it is used: its representation is written when it is
    /// not the one it was bound with.
    fn local(&mut self, l: &Local) {
        if self.bound.get(&l.id).map(|b| b.0) != Some(l.repr) {
            self.s(repr_word(l.repr));
            self.s(" ");
        }
        self.local_name(l);
    }

    fn locals(&mut self, word: &str, ls: &[Local]) {
        if ls.is_empty() {
            return;
        }
        self.s(" ");
        self.s(word);
        self.s("(");
        for (i, l) in ls.iter().enumerate() {
            if i > 0 {
                self.s(", ");
            }
            self.local(l);
        }
        self.s(")");
    }

    fn function(&mut self, f: &FnInst) -> R {
        self.head(f);
        self.s(" = ");
        self.expr(&f.body)
    }

    /// A function up to its `=`.
    fn head(&mut self, f: &FnInst) {
        self.s("fn ");
        self.name(&f.source);
        write!(self.out, "@{}", f.id).unwrap();
        if !f.generics.is_empty() {
            self.s("<");
            for (i, (g, bounds)) in f.generics.iter().enumerate() {
                if i > 0 {
                    self.s(", ");
                }
                self.param(g);
                for (j, b) in bounds.iter().enumerate() {
                    self.s(if j == 0 { ": " } else { " + " });
                    self.s(bound_word(*b));
                }
            }
            self.s(">");
        }
        self.s("(");
        for (i, p) in f.params.iter().enumerate() {
            if i > 0 {
                self.s(", ");
            }
            self.bind(&p.local, Some(&p.ty));
            self.s(": ");
            self.ty(&p.ty);
        }
        self.s("): ");
        self.ty(&f.ret);
        self.s(" ");
        self.s(tier_word(f.tier));
        if let Some(lends) = &f.lends {
            self.s(" lends(");
            for (i, l) in lends.iter().enumerate() {
                if i > 0 {
                    self.s(", ");
                }
                write!(self.out, "{l}").unwrap();
            }
            self.s(")");
        }
        if f.fn_region {
            self.s(" fn_region");
        }
    }

    fn step(&mut self, f: &FieldRef) {
        self.s(".");
        self.name(&f.name);
        if let Some(i) = f.index {
            write!(self.out, "[{i}]").unwrap();
        }
        match f.indirect {
            Indirect::None => {}
            Indirect::Shared => self.s(" shared"),
            Indirect::Unique => self.s(" unique"),
        }
    }

    fn place(&mut self, p: &Place) {
        if p.path.is_empty() && self.bound_ty(&p.local).as_ref() == Some(&p.ty) {
            self.local(&p.local);
            return;
        }
        self.s("(");
        self.local(&p.local);
        for f in &p.path {
            self.step(f);
        }
        self.s(": ");
        self.ty(&p.ty);
        self.s(")");
    }

    fn block(&mut self, b: &Block) -> R {
        if b.stmts.is_empty() && b.tail.is_none() {
            self.s("{}");
            return Ok(());
        }
        self.s("{");
        self.indent += 1;
        for s in &b.stmts {
            self.line();
            self.stmt(s)?;
        }
        if let Some(t) = &b.tail {
            self.line();
            self.expr(t)?;
        }
        self.indent -= 1;
        self.line();
        self.s("}");
        Ok(())
    }

    fn unwind(&mut self, stmts: &[Stmt]) -> R {
        if stmts.is_empty() {
            return Ok(());
        }
        self.s(" unwind {");
        self.indent += 1;
        for s in stmts {
            self.line();
            self.stmt(s)?;
        }
        self.indent -= 1;
        self.line();
        self.s("}");
        Ok(())
    }

    fn stmt(&mut self, s: &Stmt) -> R {
        match s {
            Stmt::Let {
                local,
                ty,
                init,
                stack,
                ..
            } => {
                self.s(if *stack { "let stack " } else { "let " });
                self.binding(local, ty, init)?;
            }
            Stmt::Var {
                local, ty, init, ..
            } => {
                self.s("var ");
                self.binding(local, ty, init)?;
            }
            Stmt::Assign { target, value, .. } => {
                self.s("set ");
                self.place(target);
                self.s(" := ");
                self.expr(value)?;
            }
            Stmt::Expr(e) => self.expr(e)?,
            Stmt::While {
                cond, body, tick, ..
            } => {
                self.s("while ");
                self.expr(cond)?;
                self.tick(*tick);
                self.s(" do ");
                self.block(body)?;
            }
            Stmt::Return { value, .. } => {
                self.s("return");
                if let Some(v) = value {
                    self.s(" ");
                    self.expr(v)?;
                }
            }
        }
        self.s(";");
        Ok(())
    }

    /// `x#1 := e`, with the type when it is not the type of `e`.
    fn binding(&mut self, local: &Local, ty: &Ty, init: &Expr) -> R {
        self.bind(local, Some(ty));
        if *ty != init.ty {
            self.s(": ");
            self.ty(ty);
        }
        self.s(" := ");
        self.expr(init)
    }

    fn tick(&mut self, t: Tick) {
        match t {
            Tick::None => {}
            Tick::Host => self.s(" tick host"),
            Tick::Budget => self.s(" tick budget"),
        }
    }

    fn args(&mut self, args: &[Expr]) -> R {
        self.s("(");
        self.list(args, |p, a| p.expr(a))?;
        self.s(")");
        Ok(())
    }

    fn pat(&mut self, pat: &Pat) -> R {
        match pat {
            Pat::Wild => self.s("_"),
            Pat::Bind(l, t) => {
                self.bind(l, Some(t));
                self.s(": ");
                self.ty(t);
            }
            Pat::Int(n) => write!(self.out, "{n}").unwrap(),
            Pat::Nat(n) => write!(self.out, "{n}nat").unwrap(),
            Pat::Bool(b) => write!(self.out, "{b}").unwrap(),
            Pat::Text(t) => write!(self.out, "{t:?}").unwrap(),
            Pat::Ctor { ctor, fields } => {
                self.ctor(ctor)?;
                if !fields.is_empty() {
                    self.s("(");
                    self.list(fields, |p, f| p.pat(f))?;
                    self.s(")");
                }
            }
            Pat::Variant {
                union,
                variant,
                pat,
            } => {
                write!(self.out, "inject({union}, {variant}, ").unwrap();
                self.pat(pat)?;
                self.s(")");
            }
        }
        Ok(())
    }

    /// A constructor by name. What else a `CtorRef` holds is read from the
    /// data type it belongs to, so it must say the same.
    fn ctor(&mut self, c: &CtorRef) -> R {
        let differs = |what: &str| {
            Err(format!(
                "the constructor {} is referred to with another {what} than it is declared with",
                c.name
            ))
        };
        match &c.data {
            DataRef::Gen(data) => {
                // The text of one function may refer to a data type the
                // package does not hold; the whole package may not.
                if let Some(d) = self.pkg.datas.iter().find(|d| d.name == *data) {
                    let Some(def) = d.ctors.get(c.index) else {
                        return differs("index");
                    };
                    if def.name != c.name {
                        return differs("index");
                    }
                    if def
                        .fields
                        .iter()
                        .map(|f| f.indirect)
                        .ne(c.indirect.iter().copied())
                    {
                        return differs("field storage");
                    }
                    if def.fields.iter().map(|f| &f.name).ne(c.fields.iter()) {
                        return differs("field names");
                    }
                    if d.linear != c.linear {
                        return differs("linearity");
                    }
                    if (def.fields.is_empty() && !d.is_struct) != c.nullary {
                        return differs("arity");
                    }
                }
                self.name(&c.name);
            }
            data => {
                let Some((word, ..)) = LIBRARY_CTORS
                    .iter()
                    .find(|(_, d, i)| d == data && *i == c.index)
                else {
                    return differs("index");
                };
                let like = library_ctor(word).expect("a library constructor");
                if like.indirect != c.indirect {
                    return differs("field storage");
                }
                if like.fields != c.fields {
                    return differs("field names");
                }
                if like.linear != c.linear {
                    return differs("linearity");
                }
                if like.nullary != c.nullary {
                    return differs("arity");
                }
                if c.name.as_str() != *word {
                    return differs("name");
                }
                if self
                    .pkg
                    .datas
                    .iter()
                    .flat_map(|d| &d.ctors)
                    .any(|x| x.name.as_str() == *word)
                {
                    return Err(format!(
                        "a data type declares {word}, and the library's {word} is referred to"
                    ));
                }
                self.s(word);
            }
        }
        Ok(())
    }

    fn how(&mut self, how: Use) {
        if let Some(w) = use_word(how) {
            self.s(w);
            self.s(" ");
        }
    }

    /// The type a use of a local shows.
    fn bound_ty(&self, l: &Local) -> Option<Ty> {
        let (repr, ty) = self.bound.get(&l.id)?;
        Some(local_ty(*repr, ty.as_ref()?))
    }

    /// Whether `e` is written as `(e: T)`: its text does not show its type.
    fn overridden(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Int(_) => !matches!(e.ty, Ty::Int(_)),
            kind => !writes_ty(kind) && self.default(e).as_ref() != Some(&e.ty),
        }
    }

    /// `e` in parentheses, which `(e: T)` already has.
    fn grouped(&mut self, e: &Expr) -> R {
        if self.overridden(e) {
            return self.expr(e);
        }
        self.s("(");
        self.expr(e)?;
        self.s(")");
        Ok(())
    }

    /// The type an expression has when none is written for it.
    fn default(&self, e: &Expr) -> Option<Ty> {
        default_ty(&e.kind, &|l| self.bound_ty(l))
    }

    /// Whether the text of `e` ends with an `if` that has no `else`, which
    /// would take an `else` written after it.
    fn open_if(&self, e: &Expr) -> bool {
        if self.overridden(e) {
            return false;
        }
        match &e.kind {
            ExprKind::If {
                otherwise: None, ..
            } => true,
            ExprKind::If {
                otherwise: Some(o), ..
            } => self.open_if(o),
            ExprKind::Closure(c) => self.open_if(&c.body),
            _ => false,
        }
    }

    fn expr(&mut self, e: &Expr) -> R {
        if let ExprKind::Int(n) = &e.kind {
            match &e.ty {
                Ty::Int(w) => write!(self.out, "{n}{}", width_word(*w)).unwrap(),
                t => {
                    write!(self.out, "({n}: ").unwrap();
                    self.ty(t);
                    self.s(")");
                }
            }
            return Ok(());
        }
        if writes_ty(&e.kind) {
            self.kind(e)?;
            self.s(": ");
            self.ty(&e.ty);
            return Ok(());
        }
        // The default is asked before the expression is written: what it
        // binds is not in scope for it.
        if self.default(e).as_ref() == Some(&e.ty) {
            return self.kind(e);
        }
        self.s("(");
        self.kind(e)?;
        self.s(": ");
        self.ty(&e.ty);
        self.s(")");
        Ok(())
    }

    /// The base of a field: a local as it is, anything else in parentheses.
    fn base(&mut self, e: &Expr) -> R {
        if let ExprKind::Read {
            local,
            how: Use::Place,
        } = &e.kind
            && self.default(e).as_ref() == Some(&e.ty)
        {
            self.local(local);
            return Ok(());
        }
        self.grouped(e)
    }

    fn kind(&mut self, e: &Expr) -> R {
        match &e.kind {
            ExprKind::Declaration(i) => write!(self.out, "declaration({i})").unwrap(),
            ExprKind::Unit => self.s("()"),
            ExprKind::Int(n) => write!(self.out, "{n}").unwrap(),
            ExprKind::Float(x) => {
                if x.is_nan() {
                    self.s("nan");
                } else if x.is_infinite() {
                    self.s(if *x > 0.0 { "inf" } else { "-inf" });
                } else {
                    write!(self.out, "{x:?}").unwrap();
                }
            }
            ExprKind::Bool(b) => write!(self.out, "{b}").unwrap(),
            ExprKind::Text(t) => write!(self.out, "{t:?}").unwrap(),
            ExprKind::Read { local, how } => {
                self.how(*how);
                self.local(local);
            }
            ExprKind::FnValue { inst, targs } => {
                self.inst(*inst)?;
                self.targs(targs);
            }
            ExprKind::Call(c) => {
                match &c.callee {
                    Callee::Inst(i) => self.inst(*i)?,
                    Callee::Builtin(n) => {
                        self.s("builtin ");
                        self.name(n);
                    }
                    Callee::Extern(n) => {
                        self.s("extern ");
                        self.name(n);
                    }
                    Callee::Local(l) => self.local(l),
                    Callee::Cont(l) => {
                        self.s("resume ");
                        self.local(l);
                    }
                    Callee::Value(f) => self.grouped(f)?,
                }
                self.targs(&c.targs);
                self.args(&c.args)?;
                if c.tier != Tier::S {
                    self.s(" tier ");
                    self.s(tier_word(c.tier));
                }
                self.tick(c.tick);
                if c.recur {
                    self.s(" recur");
                }
                self.unwind(&c.unwind)?;
            }
            ExprKind::Arith { op, args, num } => {
                write!(self.out, "{}<{}>", arith_word(*op), num_word(*num)).unwrap();
                self.args(args)?;
            }
            ExprKind::Cmp { op, args } => {
                self.s(cmp_word(*op));
                self.args(args)?;
            }
            ExprKind::Eq { negate, args } => {
                self.s(if *negate { "ne" } else { "eq" });
                self.args(args)?;
            }
            ExprKind::Not(a) => {
                self.s("not(");
                self.expr(a)?;
                self.s(")");
            }
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                self.s(if matches!(e.kind, ExprKind::And(..)) {
                    "and("
                } else {
                    "or("
                });
                self.expr(a)?;
                self.s(", ");
                self.expr(b)?;
                self.s(")");
            }
            ExprKind::Ctor { ctor, fields } => {
                self.ctor(ctor)?;
                if !fields.is_empty() {
                    self.s("(");
                    self.list(fields, |p, (label, value)| {
                        if let Some(l) = label {
                            p.name(l);
                            p.s(" = ");
                        }
                        p.expr(value)
                    })?;
                    self.s(")");
                }
            }
            ExprKind::Field {
                base,
                field,
                how,
                indirect,
            } => {
                self.how(*how);
                self.base(base)?;
                self.step(field);
                if indirect != &field.indirect {
                    self.s(match indirect {
                        Indirect::None => " read direct",
                        Indirect::Shared => " read shared",
                        Indirect::Unique => " read unique",
                    });
                }
            }
            ExprKind::Match(m) => {
                self.s("match ");
                if m.by_ref {
                    self.s("by_ref ");
                }
                if !m.exhaustive {
                    self.s("partial ");
                }
                self.expr(&m.scrut)?;
                self.s(" {");
                self.indent += 1;
                for arm in &m.arms {
                    self.line();
                    self.pat(&arm.pat)?;
                    if let Some(g) = &arm.guard {
                        self.s(" if ");
                        self.expr(g)?;
                    }
                    self.s(" => ");
                    self.expr(&arm.body)?;
                    self.s(",");
                }
                self.indent -= 1;
                self.line();
                self.s("}");
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.s("if ");
                self.expr(cond)?;
                self.s(" then ");
                if otherwise.is_some() && self.open_if(then) {
                    self.s("(");
                    self.expr(then)?;
                    self.s(")");
                } else {
                    self.expr(then)?;
                }
                if let Some(o) = otherwise {
                    self.s(" else ");
                    self.expr(o)?;
                }
            }
            ExprKind::Block(b) => self.block(b)?,
            ExprKind::Closure(c) => {
                self.s("closure");
                if c.borrowed {
                    self.s(" borrowed");
                }
                if c.pure {
                    self.s(" pure");
                }
                self.s("(");
                self.list(&c.params, |p, (l, t)| {
                    p.bind(l, Some(t));
                    p.s(": ");
                    p.ty(t);
                    Ok(())
                })?;
                self.s(") -> ");
                self.ty(&c.ret);
                self.s(" as ");
                self.fn_ty(&c.fn_ty);
                self.locals("clones", &c.clones);
                if !c.refs.is_empty() {
                    self.s(" refs(");
                    self.list(&c.refs, |p, r| {
                        p.bind(&r.inner, None);
                        p.s(if r.mutable { " = &mut " } else { " = &" });
                        p.local(&r.outer);
                        Ok(())
                    })?;
                    self.s(")");
                }
                self.locals("owned_refs", &c.owned_refs);
                self.s(" => ");
                self.expr(&c.body)?;
            }
            ExprKind::Perform(p) => {
                self.s("perform ");
                self.op(p.op)?;
                self.args(&p.args)?;
                self.s(" ");
                self.quant(p.quant);
                if p.detached {
                    self.s(" detached");
                }
                self.instance(&p.instance);
                self.unwind(&p.unwind)?;
                self.s(": ");
                self.ty(&p.result);
            }
            ExprKind::Handle(h) => self.handle(h)?,
            ExprKind::Inject {
                union,
                variant,
                value,
            } => {
                write!(self.out, "inject({union}, {variant}, ").unwrap();
                self.expr(value)?;
                self.s(")");
            }
            ExprKind::Remap { from, to, value } => {
                write!(self.out, "remap({from}, ").unwrap();
                self.ty(to);
                self.s(", ");
                self.expr(value)?;
                self.s(")");
            }
            ExprKind::Ref(p) => {
                self.s("&");
                self.place(p);
            }
            ExprKind::RefMut(p) => {
                self.s("&mut ");
                self.place(p);
            }
            ExprKind::TempRef(a) => self.wrapped("tempref", a)?,
            ExprKind::Deref { value, how } => {
                self.how(*how);
                self.wrapped("deref", value)?;
            }
            ExprKind::Shown(a) => self.wrapped("shown", a)?,
            ExprKind::Budget(b) => {
                write!(self.out, "budget {}", b.id).unwrap();
                if b.memory {
                    self.s(" memory");
                }
                if b.m {
                    self.s(" m");
                }
                self.s("(");
                self.expr(&b.steps)?;
                self.s(", ");
                self.expr(&b.body)?;
                self.s(")");
            }
            ExprKind::Unreachable(a) => self.wrapped("unreachable", a)?,
            ExprKind::FnCast(a) => self.wrapped("fncast", a)?,
        }
        Ok(())
    }

    fn wrapped(&mut self, word: &str, a: &Expr) -> R {
        self.s(word);
        self.s("(");
        self.expr(a)?;
        self.s(")");
        Ok(())
    }

    fn targs(&mut self, targs: &[Ty]) {
        if !targs.is_empty() {
            self.s("<");
            self.tys(targs);
            self.s(">");
        }
    }

    fn instance(&mut self, instance: &Option<OperationInstance>) {
        let Some(i) = instance else { return };
        self.s(" instance");
        self.targs(&i.type_args);
        self.s("(");
        self.tys(&i.params);
        self.s(") -> ");
        self.ty(&i.answer);
        self.s(" ");
        let word = ADMISSIONS
            .iter()
            .find(|(a, _)| *a == i.admission)
            .expect("every admission has a word")
            .1;
        self.s(word);
    }

    fn handle(&mut self, h: &HandleNode) -> R {
        write!(self.out, "handle {} {}", h.id, tier_word(h.body_tier)).unwrap();
        for (on, word) in [(h.m, "m"), (h.kept, "kept"), (h.detached, "detached")] {
            if on {
                self.s(" ");
                self.s(word);
            }
        }
        if let Some(t) = &h.host_ret {
            self.s(" host_ret ");
            self.ty(t);
        }
        self.locals("captures", &h.captures);
        self.locals("clones", &h.clones);
        self.s(" do ");
        self.expr(&h.body)?;
        if h.body_ty != h.body.ty {
            self.s(" as ");
            self.ty(&h.body_ty);
        }
        self.s(" with {");
        self.indent += 1;
        if let Some(r) = &h.ret {
            self.line();
            self.s("return ");
            self.pat(&r.pat)?;
            self.s(" => ");
            self.expr(&r.body)?;
            self.s(",");
        }
        for (word, arms) in [
            ("direct", &h.direct),
            ("abort", &h.aborts),
            ("suspend", &h.susp),
        ] {
            for a in arms {
                self.line();
                self.s(word);
                self.s(" ");
                self.op(a.op)?;
                self.s("(");
                self.list(&a.pats, |p, x| p.pat(x))?;
                self.s(") params(");
                self.tys(&a.params);
                self.s(") answer ");
                self.ty(&a.k_ans);
                if let Some(k) = &a.k {
                    self.s(" k ");
                    self.bind(k, None);
                }
                self.instance(&a.instance);
                if a.instantiated {
                    self.s(" instantiated");
                }
                if let Some(g) = &a.guard {
                    self.s(" if ");
                    self.expr(g)?;
                }
                self.s(" => ");
                self.expr(&a.body)?;
                self.s(",");
            }
        }
        self.indent -= 1;
        self.line();
        self.s("}: ");
        self.ty(&h.result);
        Ok(())
    }
}

/// The constructor of the library's `Option`, `Result` or `Pair` that the
/// text calls `word`.
pub(crate) fn library_ctor(word: &str) -> Option<CtorRef> {
    let (_, data, index) = LIBRARY_CTORS.iter().find(|(n, ..)| *n == word)?;
    let fields: Vec<Option<String>> = match word {
        "Option::None" => vec![],
        "Pair::Mk" => vec![Some("fst".into()), Some("snd".into())],
        _ => vec![None],
    };
    Some(CtorRef {
        data: data.clone(),
        name: Name::from(word),
        index: *index,
        indirect: vec![Indirect::None; fields.len()],
        linear: false,
        nullary: fields.is_empty(),
        fields,
    })
}
