//! The parser: text as a package.

use std::collections::HashMap;

use super::lex::{Tok, lex};
use super::print::library_ctor;
use super::*;

/// Why a text is not a package, and where.
#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub message: String,
    /// The place in the text.
    pub span: Span,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (byte {})", self.message, self.span.start)
    }
}

type R<T> = Result<T, ParseError>;

/// Reads a package. A node has the span it is written at in `text`.
mod blocks;
pub use blocks::parse_blocks;

pub fn parse(text: &str) -> Result<Package, ParseError> {
    let toks = lex(text).map_err(|(message, span)| ParseError { message, span })?;
    let mut p = Parser {
        toks,
        at: 0,
        names: HashMap::new(),
        bound: HashMap::new(),
        insts: Vec::new(),
        pkg: Package::default(),
    };
    p.package()?;
    Ok(p.pkg)
}

struct Parser {
    toks: Vec<(Tok, Span)>,
    at: usize,
    /// One reference for each name the text spells.
    names: HashMap<String, Name>,
    /// How each local was bound: its representation and its type.
    bound: HashMap<u32, (Repr, Option<Ty>)>,
    /// The functions referred to, checked once all are read.
    insts: Vec<(String, usize, Span)>,
    pkg: Package,
}

/// An expression whose type may still be missing: one that neither writes
/// its type nor shows it.
struct Draft {
    kind: ExprKind,
    ty: Option<Ty>,
    span: Span,
}

impl Parser {
    fn tok(&self) -> &Tok {
        &self.toks[self.at].0
    }

    fn span(&self) -> Span {
        self.toks[self.at].1
    }

    /// The span from `start` to the end of the last token read.
    fn since(&self, start: Span) -> Span {
        let end = self.toks[self.at.saturating_sub(1)].1.end;
        Span::new(start.start, end.max(start.start))
    }

    fn err<T>(&self, message: impl Into<String>) -> R<T> {
        Err(ParseError {
            message: message.into(),
            span: self.span(),
        })
    }

    fn bump(&mut self) -> Tok {
        let t = self.toks[self.at].0.clone();
        if self.at + 1 < self.toks.len() {
            self.at += 1;
        }
        t
    }

    fn is(&self, punct: &str) -> bool {
        matches!(self.tok(), Tok::Punct(p) if *p == punct)
    }

    fn word(&self, word: &str) -> bool {
        matches!(self.tok(), Tok::Word(w) if w == word)
    }

    fn eat(&mut self, punct: &str) -> bool {
        let yes = self.is(punct);
        if yes {
            self.bump();
        }
        yes
    }

    fn eat_word(&mut self, word: &str) -> bool {
        let yes = self.word(word);
        if yes {
            self.bump();
        }
        yes
    }

    fn expect(&mut self, punct: &str) -> R<()> {
        if self.eat(punct) {
            Ok(())
        } else {
            self.err(format!("expected `{punct}`"))
        }
    }

    fn expect_word(&mut self, word: &str) -> R<()> {
        if self.eat_word(word) {
            Ok(())
        } else {
            self.err(format!("expected `{word}`"))
        }
    }

    /// A name as it is spelled: a word that is not reserved, or `$"…"`.
    fn spelling(&mut self) -> R<String> {
        match self.tok() {
            Tok::Word(w) if !KEYWORDS.contains(&w.as_str()) => {}
            Tok::Quoted(_) => {}
            _ => return self.err("expected a name"),
        }
        match self.bump() {
            Tok::Word(w) | Tok::Quoted(w) => Ok(w),
            _ => unreachable!(),
        }
    }

    fn is_name(&self) -> bool {
        match self.tok() {
            Tok::Word(w) => !KEYWORDS.contains(&w.as_str()),
            Tok::Quoted(_) => true,
            _ => false,
        }
    }

    /// The reference a spelling stands for: the same one each time.
    fn global(&mut self, spelling: &str) -> Name {
        self.names
            .entry(spelling.to_string())
            .or_insert_with(|| Name::Global(DeclRef::fresh(spelling)))
            .clone()
    }

    fn name(&mut self) -> R<Name> {
        let s = self.spelling()?;
        Ok(self.global(&s))
    }

    fn string(&mut self) -> R<String> {
        match self.tok() {
            Tok::Str(_) => match self.bump() {
                Tok::Str(s) => Ok(s),
                _ => unreachable!(),
            },
            _ => self.err("expected a string"),
        }
    }

    fn number<T: TryFrom<i128>>(&mut self) -> R<T> {
        if let Tok::Int(n, None) = self.tok()
            && let Ok(n) = T::try_from(*n)
        {
            self.bump();
            return Ok(n);
        }
        self.err("expected a number")
    }

    /// Items between `(` and `)`, separated by commas.
    fn parens<T>(&mut self, mut each: impl FnMut(&mut Self) -> R<T>) -> R<Vec<T>> {
        self.expect("(")?;
        self.until(")", &mut each)
    }

    fn until<T>(&mut self, close: &str, each: &mut impl FnMut(&mut Self) -> R<T>) -> R<Vec<T>> {
        let mut out = Vec::new();
        while !self.eat(close) {
            if !out.is_empty() {
                self.expect(",")?;
            }
            out.push(each(self)?);
        }
        Ok(out)
    }

    // ---- The package ----

    fn package(&mut self) -> R<()> {
        while *self.tok() != Tok::End {
            let Tok::Word(w) = self.tok().clone() else {
                return self.err("expected an item of a package");
            };
            self.bump();
            match w.as_str() {
                "declarations" => {
                    let names = self.parens(|p| p.spelling())?;
                    for n in names {
                        let Name::Global(d) = self.global(&n) else {
                            unreachable!()
                        };
                        self.pkg.declarations.push(d);
                    }
                }
                "syntax" => self.syntax()?,
                "data" => self.data()?,
                "union" => {
                    let id = self.number()?;
                    let kind = self.kind()?;
                    let members = self.parens(|p| p.ty())?;
                    self.pkg.unions.push(UnionDef { id, members, kind });
                }
                "op" => {
                    let id = self.number()?;
                    let name = self.name()?;
                    let generics = self.generics()?;
                    let params = self.parens(|p| p.ty())?;
                    self.expect(":")?;
                    let result = self.ty()?;
                    let quant = self.quant()?;
                    self.pkg.ops.push(OpDef {
                        id,
                        name,
                        quant,
                        generics,
                        params,
                        result,
                    });
                }
                "extern" => self.extern_fn()?,
                "fn" => self.function()?,
                "top" => {
                    let id = self.inst()?;
                    self.pkg.top = Some(id);
                }
                "export" => {
                    let name = self.string()?;
                    self.expect("=")?;
                    let inst = self.inst()?;
                    self.expect_word("row")?;
                    let row = self.parens(|p| p.string())?;
                    self.expect_word("foreign_row")?;
                    let foreign_row = self.parens(|p| p.string())?;
                    self.expect_word("pure_borrow_callbacks")?;
                    let pure_borrow_callbacks = self.parens(|p| p.number())?;
                    self.pkg.exports.push(Export {
                        inst,
                        name,
                        row,
                        foreign_row,
                        pure_borrow_callbacks,
                    });
                }
                "sync" => self.pkg.sync = true,
                "permissions" => self.pkg.permissions = self.parens(|p| p.string())?,
                "unsupported" => {
                    let what = self.message()?;
                    self.pkg.rust_unsupported = Some(Unsupported { what, span: None });
                }
                "evidence" => self.evidence()?,
                _ => {
                    self.at -= 1;
                    return self.err("expected an item of a package");
                }
            }
        }
        for (i, f) in self.pkg.fns.iter().enumerate() {
            if f.id != i {
                return Err(ParseError {
                    message: format!(
                        "the function {}@{} is the {i}th of the package: its id is its place",
                        f.source, f.id
                    ),
                    span: f.span,
                });
            }
        }
        for (name, id, span) in &self.insts {
            if self.pkg.fns.get(*id).map(|f| f.source.as_str()) != Some(name) {
                return Err(ParseError {
                    message: format!("no function is {name}@{id}"),
                    span: *span,
                });
            }
        }
        Ok(())
    }

    fn syntax(&mut self) -> R<()> {
        let name = self.string()?;
        self.expect_word("sha")?;
        let sha = self.string()?;
        self.expect_word("result")?;
        let result = self.ty()?;
        self.expect_word("tables")?;
        let tables = self.string()?;
        self.expect_word("data")?;
        let data_bindings = self
            .parens(|p| {
                let label = p.string()?;
                p.expect("=")?;
                Ok((label, p.name()?))
            })?
            .into_iter()
            .collect();
        self.expect_word("constructors")?;
        let constructor_bindings = self
            .parens(|p| {
                let data = p.string()?;
                p.expect(".")?;
                let ctor = p.string()?;
                p.expect("=")?;
                Ok(((data, ctor), p.name()?))
            })?
            .into_iter()
            .collect();
        self.pkg.syntax_parsers.push(SyntaxParser {
            data_bindings,
            constructor_bindings,
            name,
            sha,
            tables,
            result,
        });
        Ok(())
    }

    fn message(&mut self) -> R<Message> {
        let id = self.string()?;
        let args = self.parens(|p| {
            let key = p.string()?;
            p.expect("=")?;
            let value = match p.tok() {
                Tok::Int(..) => tauto_message::Value::Number(p.number()?),
                Tok::Str(_) if matches!(p.toks[p.at + 1].0, Tok::Punct("(")) => {
                    tauto_message::Value::Message(Box::new(p.message()?))
                }
                _ => tauto_message::Value::Text(p.string()?),
            };
            Ok((key.into(), value))
        })?;
        Ok(Message {
            id: id.into(),
            args,
        })
    }

    fn evidence(&mut self) -> R<()> {
        if self.eat_word("op") {
            let op = self.op()?;
            let params = self.parens(|p| p.ty())?;
            self.expect(":")?;
            let answer = self.ty()?;
            self.pkg.evidence.ops.insert(op, (params, answer));
        } else if self.eat_word("fn") {
            let f = self.inst()?;
            let ops = self.parens(|p| p.op())?;
            self.pkg.evidence.fns.insert(f, ops);
        } else {
            self.expect_word("handle")?;
            let h = self.number()?;
            let ops = self.parens(|p| p.op())?;
            self.pkg.evidence.handles.insert(h, ops);
        }
        Ok(())
    }

    fn kind(&mut self) -> R<Kind> {
        if let Tok::Word(w) = self.tok()
            && let Some(k) = Kind::parse(w)
        {
            self.bump();
            return Ok(k);
        }
        self.err("expected a kind: copy, shared, affine or linear")
    }

    fn tier(&mut self) -> R<Tier> {
        if let Tok::Word(w) = self.tok()
            && let Some(t) = tier_of(w)
        {
            self.bump();
            return Ok(t);
        }
        self.err("expected a tier: S, A, O or M")
    }

    fn quant(&mut self) -> R<Quant> {
        if self.eat_word("direct") {
            return Ok(Quant::Direct);
        }
        self.expect_word("resume")?;
        if self.eat("<") {
            self.expect("=")?;
            if self.number::<u8>()? != 1 {
                self.at -= 1;
                return self.err("expected `resume <=1`");
            }
            return Ok(Quant::AtMostOne);
        }
        if self.eat_word("ω") {
            return Ok(Quant::Many);
        }
        match self.number::<u8>()? {
            0 => Ok(Quant::Zero),
            1 => Ok(Quant::One),
            _ => {
                self.at -= 1;
                self.err("expected `resume 0`, `resume <=1`, `resume 1` or `resume ω`")
            }
        }
    }

    fn param(&mut self) -> R<String> {
        self.expect("'")?;
        self.spelling()
    }

    fn generics(&mut self) -> R<Vec<String>> {
        if !self.eat("<") {
            return Ok(Vec::new());
        }
        self.until(">", &mut |p| p.param())
    }

    fn indirect(&mut self) -> Indirect {
        if self.eat_word("shared") {
            Indirect::Shared
        } else if self.eat_word("unique") {
            Indirect::Unique
        } else {
            Indirect::None
        }
    }

    fn data(&mut self) -> R<()> {
        let kind = self.kind()?;
        let is_struct = if self.eat_word("struct") {
            true
        } else {
            self.expect_word("enum")?;
            false
        };
        let name = self.name()?;
        let generics = self.generics()?;
        let flag = |p: &mut Self, word: &str| p.eat_word(word);
        let clone = flag(self, "clone");
        let copy = flag(self, "copy");
        let linear = flag(self, "linear");
        let view = flag(self, "view");
        let host = flag(self, "host");
        let shown = if self.eat_word("as") {
            self.string()?
        } else {
            String::new()
        };
        self.expect("{")?;
        let mut ctors = Vec::new();
        while !self.eat("}") {
            let name = self.name()?;
            let fields = if self.is("(") {
                self.parens(|p| {
                    let indirect = p.indirect();
                    let labelled = p.is_name() && matches!(p.toks[p.at + 1].0, Tok::Punct(":"));
                    let name = if labelled {
                        let n = p.spelling()?;
                        p.expect(":")?;
                        Some(n)
                    } else {
                        None
                    };
                    Ok(FieldDef {
                        name,
                        ty: p.ty()?,
                        indirect,
                    })
                })?
            } else {
                Vec::new()
            };
            self.expect(",")?;
            ctors.push(CtorDef { name, fields });
        }
        self.pkg.datas.push(DataDef {
            name,
            generics,
            kind,
            is_struct,
            ctors,
            clone,
            copy,
            linear,
            view,
            host,
            shown,
        });
        Ok(())
    }

    fn extern_fn(&mut self) -> R<()> {
        let start = self.toks[self.at - 1].1;
        self.expect_word("fn")?;
        let name = self.name()?;
        let generics = self.generics()?;
        let params = self.parens(|p| {
            let pass = if p.eat_word("ref") {
                Pass::Ref
            } else if p.eat_word("refmut") {
                Pass::RefMut
            } else {
                Pass::Value
            };
            let name = p.spelling()?;
            p.expect(":")?;
            Ok((name, p.ty()?, pass))
        })?;
        self.expect(":")?;
        let ret = self.ty()?;
        let lends = if self.eat_word("lends") {
            Some(self.parens(|p| p.boolean())?)
        } else {
            None
        };
        let waits = self.eat_word("waits");
        self.pkg.externs.push(ExternDef {
            name,
            generics,
            params,
            ret,
            lends,
            waits,
            span: self.since(start),
        });
        Ok(())
    }

    fn function(&mut self) -> R<()> {
        let mut f = self.fn_head()?;
        self.expect("=")?;
        let start = f.span;
        f.body = self.expr()?;
        f.span = self.since(start);
        self.pkg.fns.push(f);
        Ok(())
    }

    /// A function up to its `=`, with a unit body for the caller to replace.
    /// The `fn` is read.
    fn fn_head(&mut self) -> R<FnInst> {
        let start = self.toks[self.at - 1].1;
        let Tok::Inst(source, id) = self.tok().clone() else {
            return self.err("expected a function: name@id");
        };
        self.bump();
        let source = self.global(&source);
        let mut generics = Vec::new();
        if self.eat("<") {
            generics = self.until(">", &mut |p| {
                let g = p.param()?;
                let mut bounds = BTreeSet::new();
                if p.eat(":") {
                    loop {
                        let Tok::Word(w) = p.tok() else {
                            return p.err("expected a bound");
                        };
                        let Some(b) = bound_of(w) else {
                            return p.err("expected a bound: Clone, Show, Eq, Hash or Static");
                        };
                        bounds.insert(b);
                        p.bump();
                        if !p.eat("+") {
                            break;
                        }
                    }
                }
                Ok((g, bounds))
            })?;
        }
        let params = self.parens(|p| {
            let local = p.binding()?;
            p.expect(":")?;
            let ty = p.ty()?;
            p.bind(&local, Some(&ty));
            Ok(Param { local, ty })
        })?;
        self.expect(":")?;
        let ret = self.ty()?;
        let tier = self.tier()?;
        let lends = if self.eat_word("lends") {
            Some(self.parens(|p| p.boolean())?)
        } else {
            None
        };
        let fn_region = self.eat_word("fn_region");
        Ok(FnInst {
            id,
            source,
            tier,
            generics,
            params,
            ret,
            lends,
            fn_region,
            body: Expr {
                kind: ExprKind::Unit,
                ty: Ty::Unit,
                span: start,
            },
            span: start,
        })
    }

    fn boolean(&mut self) -> R<bool> {
        if self.eat_word("true") {
            Ok(true)
        } else if self.eat_word("false") {
            Ok(false)
        } else {
            self.err("expected `true` or `false`")
        }
    }

    fn inst(&mut self) -> R<InstId> {
        let Tok::Inst(name, id) = self.tok().clone() else {
            return self.err("expected a function: name@id");
        };
        self.insts.push((name, id, self.span()));
        self.bump();
        Ok(id)
    }

    fn op(&mut self) -> R<OpIndex> {
        let at = self.span();
        let name = self.spelling()?;
        match self.pkg.ops.iter().position(|o| o.name.as_str() == name) {
            Some(i) => Ok(i),
            None => Err(ParseError {
                message: format!("no operation is named {name}"),
                span: at,
            }),
        }
    }

    // ---- Types ----

    fn ty(&mut self) -> R<Ty> {
        if self.eat("&") {
            let mutable = self.eat_word("mut");
            let inner = Box::new(self.ty()?);
            return Ok(if mutable {
                Ty::RefMut(inner)
            } else {
                Ty::Ref(inner)
            });
        }
        if self.is("'") {
            return Ok(Ty::Param(self.param()?));
        }
        if let Tok::Quoted(_) = self.tok() {
            return self.data_ty();
        }
        let Tok::Word(w) = self.tok().clone() else {
            return self.err("expected a type");
        };
        if !KEYWORDS.contains(&w.as_str()) && w != "_" {
            return self.data_ty();
        }
        self.bump();
        let one = |p: &mut Self| -> R<Box<Ty>> {
            p.expect("(")?;
            let t = p.ty()?;
            p.expect(")")?;
            Ok(Box::new(t))
        };
        let two = |p: &mut Self| -> R<(Box<Ty>, Box<Ty>)> {
            p.expect("(")?;
            let a = p.ty()?;
            p.expect(",")?;
            let b = p.ty()?;
            p.expect(")")?;
            Ok((Box::new(a), Box::new(b)))
        };
        Ok(match w.as_str() {
            "Bool" => Ty::Bool,
            "Text" => Ty::Text,
            "Unit" => Ty::Unit,
            "Never" => Ty::Never,
            "Float" => Ty::Float,
            "Float32" => Ty::Float32,
            "Buf" => Ty::Buf,
            "Shown" => Ty::Shown,
            "Vec" => Ty::Vec(one(self)?),
            "Array" => Ty::Array(one(self)?),
            "Slice" => Ty::Slice(one(self)?),
            "Option" => Ty::Option(one(self)?),
            "Info" => Ty::Info(one(self)?),
            "BudgetAnswer" => Ty::BudgetAnswer(one(self)?),
            "Result" => {
                let (a, b) = two(self)?;
                Ty::Result(a, b)
            }
            "Pair" => {
                let (a, b) = two(self)?;
                Ty::Pair(a, b)
            }
            "SharedVar" => {
                self.expect("(")?;
                let copy = self.eat_word("copy");
                if copy {
                    self.expect(",")?;
                }
                let t = self.ty()?;
                self.expect(")")?;
                Ty::SharedVar(copy, Box::new(t))
            }
            "std" => {
                let Tok::Word(name) = self.tok().clone() else {
                    return self.err("expected the name of a standard type");
                };
                let Some(s) = STD_TYPES.iter().find(|s| s.name() == name) else {
                    return self.err("expected the name of a standard type");
                };
                self.bump();
                let args = if self.is("(") {
                    self.parens(|p| p.ty())?
                } else {
                    Vec::new()
                };
                Ty::Std(*s, args)
            }
            "union" => {
                self.expect("(")?;
                let id = self.number()?;
                self.expect(")")?;
                Ty::Union(id)
            }
            "fn" => Ty::Fn(Box::new(self.fn_ty()?)),
            w => match width_of(w) {
                Some(width) => Ty::Int(width),
                None => {
                    self.at -= 1;
                    return self.err("expected a type");
                }
            },
        })
    }

    fn data_ty(&mut self) -> R<Ty> {
        let name = self.name()?;
        let args = if self.is("(") {
            self.parens(|p| p.ty())?
        } else {
            Vec::new()
        };
        Ok(Ty::Data(name, args))
    }

    /// A function type, after its `fn`.
    fn fn_ty(&mut self) -> R<FnTy> {
        let params = self.parens(|p| p.ty())?;
        self.expect("->")?;
        let ret = self.ty()?;
        let kind = self.kind()?;
        let tier = self.tier()?;
        Ok(FnTy {
            params,
            ret,
            kind,
            tier,
        })
    }

    // ---- Locals ----

    fn repr(&mut self) -> Option<Repr> {
        if let Tok::Word(w) = self.tok()
            && let Some(r) = repr_of(w)
            && matches!(self.toks[self.at + 1].0, Tok::Local(..))
        {
            self.bump();
            return Some(r);
        }
        None
    }

    fn is_local(&self) -> bool {
        match self.tok() {
            Tok::Local(..) => true,
            Tok::Word(w) => {
                repr_of(w).is_some() && matches!(self.toks[self.at + 1].0, Tok::Local(..))
            }
            _ => false,
        }
    }

    /// A local where it is bound: plain unless a representation is written.
    fn binding(&mut self) -> R<Local> {
        let repr = self.repr().unwrap_or(Repr::Plain);
        let Tok::Local(name, id) = self.tok().clone() else {
            return self.err("expected a local: name#id");
        };
        self.bump();
        Ok(Local { id, name, repr })
    }

    fn bind(&mut self, l: &Local, ty: Option<&Ty>) {
        self.bound.insert(l.id, (l.repr, ty.cloned()));
    }

    /// A local where it is used: as it was bound unless a representation is
    /// written.
    fn local(&mut self) -> R<Local> {
        let written = self.repr();
        let Tok::Local(name, id) = self.tok().clone() else {
            return self.err("expected a local: name#id");
        };
        let repr = match written.or(self.bound.get(&id).map(|b| b.0)) {
            Some(r) => r,
            None => {
                return self.err(format!(
                    "the local {name}#{id} is not bound before: its representation is written"
                ));
            }
        };
        self.bump();
        Ok(Local { id, name, repr })
    }

    fn locals(&mut self, word: &str) -> R<Vec<Local>> {
        if self.eat_word(word) {
            self.parens(|p| p.local())
        } else {
            Ok(Vec::new())
        }
    }

    fn step(&mut self) -> R<FieldRef> {
        self.expect(".")?;
        let name = self.spelling()?;
        let index = if self.eat("[") {
            let i = self.number()?;
            self.expect("]")?;
            Some(i)
        } else {
            None
        };
        Ok(FieldRef {
            name,
            index,
            indirect: self.indirect(),
        })
    }

    fn place(&mut self) -> R<Place> {
        if self.eat("(") {
            let local = self.local()?;
            let mut path = Vec::new();
            while self.is(".") {
                path.push(self.step()?);
            }
            self.expect(":")?;
            let ty = self.ty()?;
            self.expect(")")?;
            return Ok(Place { local, path, ty });
        }
        let at = self.span();
        let local = self.local()?;
        match self.bound_ty(&local) {
            Some(ty) => Ok(Place {
                local,
                path: Vec::new(),
                ty,
            }),
            None => Err(ParseError {
                message: format!(
                    "the local {}#{} is bound without a type: the place writes its type",
                    local.name, local.id
                ),
                span: at,
            }),
        }
    }

    // ---- Statements ----

    fn block(&mut self) -> R<Block> {
        self.expect("{")?;
        let mut stmts = Vec::new();
        let mut tail = None;
        while !self.eat("}") {
            if let Some(s) = self.stmt()? {
                self.expect(";")?;
                stmts.push(s);
                continue;
            }
            let e = self.expr()?;
            if self.eat(";") {
                stmts.push(Stmt::Expr(e));
            } else {
                tail = Some(Box::new(e));
                self.expect("}")?;
                break;
            }
        }
        Ok(Block { stmts, tail })
    }

    fn unwind(&mut self) -> R<Vec<Stmt>> {
        if !self.eat_word("unwind") {
            return Ok(Vec::new());
        }
        self.expect("{")?;
        let mut stmts = Vec::new();
        while !self.eat("}") {
            let s = match self.stmt()? {
                Some(s) => s,
                None => Stmt::Expr(self.expr()?),
            };
            self.expect(";")?;
            stmts.push(s);
        }
        Ok(stmts)
    }

    /// A statement that starts with its own word; `None` at an expression.
    fn stmt(&mut self) -> R<Option<Stmt>> {
        let start = self.span();
        let Tok::Word(w) = self.tok().clone() else {
            return Ok(None);
        };
        Ok(Some(match w.as_str() {
            "let" | "var" => {
                self.bump();
                let stack = w == "let" && self.eat_word("stack");
                let local = self.binding()?;
                let written = if self.eat(":") {
                    Some(self.ty()?)
                } else {
                    None
                };
                self.expect(":=")?;
                let init = self.expr()?;
                let ty = written.unwrap_or_else(|| init.ty.clone());
                self.bind(&local, Some(&ty));
                let span = self.since(start);
                if w == "let" {
                    Stmt::Let {
                        local,
                        ty,
                        init,
                        span,
                        stack,
                    }
                } else {
                    Stmt::Var {
                        local,
                        ty,
                        init,
                        span,
                    }
                }
            }
            "set" => {
                self.bump();
                let target = self.place()?;
                self.expect(":=")?;
                let value = self.expr()?;
                Stmt::Assign {
                    target,
                    value,
                    span: self.since(start),
                }
            }
            "while" => {
                self.bump();
                let cond = self.expr()?;
                let tick = self.tick()?;
                self.expect_word("do")?;
                let body = self.block()?;
                Stmt::While {
                    cond,
                    body,
                    tick,
                    span: self.since(start),
                }
            }
            "return" => {
                self.bump();
                let value = if self.is(";") {
                    None
                } else {
                    Some(self.expr()?)
                };
                Stmt::Return {
                    value,
                    span: self.since(start),
                }
            }
            _ => return Ok(None),
        }))
    }

    fn tick(&mut self) -> R<Tick> {
        if !self.eat_word("tick") {
            return Ok(Tick::None);
        }
        if self.eat_word("host") {
            Ok(Tick::Host)
        } else if self.eat_word("budget") {
            Ok(Tick::Budget)
        } else {
            self.err("expected `tick host` or `tick budget`")
        }
    }

    // ---- Patterns ----

    fn pat(&mut self) -> R<Pat> {
        if self.is_local() {
            let local = self.binding()?;
            self.expect(":")?;
            let ty = self.ty()?;
            self.bind(&local, Some(&ty));
            return Ok(Pat::Bind(local, ty));
        }
        match self.tok().clone() {
            Tok::Word(w) if w == "_" => {
                self.bump();
                Ok(Pat::Wild)
            }
            Tok::Word(w) if w == "true" || w == "false" => {
                self.bump();
                Ok(Pat::Bool(w == "true"))
            }
            // `inject(union, variant, p)`: what the union holds at `variant`.
            Tok::Word(w) if w == "inject" => {
                self.bump();
                self.expect("(")?;
                let union = self.number()?;
                self.expect(",")?;
                let variant = self.number()?;
                self.expect(",")?;
                let pat = Box::new(self.pat()?);
                self.expect(")")?;
                Ok(Pat::Variant {
                    union,
                    variant,
                    pat,
                })
            }
            Tok::Str(s) => {
                self.bump();
                Ok(Pat::Text(s))
            }
            Tok::Int(n, suffix) => {
                let Ok(n) = i64::try_from(n) else {
                    return self.err("the number is too large for a pattern");
                };
                let pat = match suffix.as_deref() {
                    None => Pat::Int(n),
                    Some("nat") => Pat::Nat(n),
                    Some(_) => return self.err("a number in a pattern is plain or `nat`"),
                };
                self.bump();
                Ok(pat)
            }
            _ => {
                let ctor = self.ctor()?;
                let fields = if self.is("(") {
                    self.parens(|p| p.pat())?
                } else {
                    Vec::new()
                };
                Ok(Pat::Ctor { ctor, fields })
            }
        }
    }

    fn declared_ctor(&self, name: &str) -> Option<CtorRef> {
        for d in &self.pkg.datas {
            for (index, c) in d.ctors.iter().enumerate() {
                if c.name.as_str() == name {
                    return Some(CtorRef {
                        data: DataRef::Gen(d.name.clone()),
                        name: c.name.clone(),
                        index,
                        indirect: c.fields.iter().map(|f| f.indirect).collect(),
                        linear: d.linear,
                        fields: c.fields.iter().map(|f| f.name.clone()).collect(),
                        nullary: c.fields.is_empty() && !d.is_struct,
                    });
                }
            }
        }
        None
    }

    fn ctor(&mut self) -> R<CtorRef> {
        let found = match self.tok() {
            Tok::Word(w) if KEYWORDS.contains(&w.as_str()) => None,
            Tok::Word(w) | Tok::Quoted(w) => self.declared_ctor(w).or_else(|| library_ctor(w)),
            _ => None,
        };
        match found {
            Some(c) => {
                self.bump();
                Ok(c)
            }
            None => self.err("no data type above declares this constructor"),
        }
    }

    // ---- Expressions ----

    fn expr(&mut self) -> R<Expr> {
        let at = self.span();
        let d = self.draft()?;
        match d.ty {
            Some(ty) => Ok(Expr {
                kind: d.kind,
                ty,
                span: d.span,
            }),
            None => Err(ParseError {
                message: "the expression does not show its type: write it as `(e: T)`".into(),
                span: at,
            }),
        }
    }

    /// The type a use of a local shows.
    fn bound_ty(&self, l: &Local) -> Option<Ty> {
        let (repr, ty) = self.bound.get(&l.id)?;
        Some(local_ty(*repr, ty.as_ref()?))
    }

    /// An expression in parentheses, after the `(`: `e)` or `e: T)`.
    fn grouped(&mut self, start: Span) -> R<Expr> {
        let inner = self.draft()?;
        if self.eat(":") {
            let ty = self.ty()?;
            self.expect(")")?;
            return Ok(Expr {
                kind: inner.kind,
                ty,
                span: self.since(start),
            });
        }
        self.expect(")")?;
        match inner.ty {
            Some(ty) => Ok(Expr {
                kind: inner.kind,
                ty,
                span: inner.span,
            }),
            None => {
                self.at -= 1;
                self.err("the expression does not show its type: write `(e: T)`")
            }
        }
    }

    /// An expression with the type its text shows.
    fn shown(&self, kind: ExprKind, start: Span) -> Draft {
        let ty = default_ty(&kind, &|l| self.bound_ty(l));
        Draft {
            kind,
            ty,
            span: self.since(start),
        }
    }

    /// An expression whose text ends with its type.
    fn typed(&mut self, kind: ExprKind, start: Span) -> R<Draft> {
        self.expect(":")?;
        let ty = self.ty()?;
        Ok(Draft {
            kind,
            ty: Some(ty),
            span: self.since(start),
        })
    }

    fn args(&mut self) -> R<Vec<Expr>> {
        self.parens(|p| p.expr())
    }

    fn targs(&mut self) -> R<Vec<Ty>> {
        if self.eat("<") {
            self.until(">", &mut |p| p.ty())
        } else {
            Ok(Vec::new())
        }
    }

    /// The rest of a call, from its type arguments on.
    fn call(&mut self, callee: Callee, start: Span) -> R<Draft> {
        let targs = self.targs()?;
        let args = self.args()?;
        let tier = if self.eat_word("tier") {
            self.tier()?
        } else {
            Tier::S
        };
        let tick = self.tick()?;
        let recur = self.eat_word("recur");
        let unwind = self.unwind()?;
        let span = self.since(start);
        self.typed(
            ExprKind::Call(Box::new(CallNode {
                callee,
                args,
                tier,
                targs,
                tick,
                recur,
                unwind,
                span,
            })),
            start,
        )
    }

    /// The rest of a field read, from its `.` on.
    fn field(&mut self, base: Expr, how: Use, start: Span) -> R<Draft> {
        let field = self.step()?;
        let indirect = if self.eat_word("read") {
            if self.eat_word("direct") {
                Indirect::None
            } else if self.eat_word("shared") {
                Indirect::Shared
            } else if self.eat_word("unique") {
                Indirect::Unique
            } else {
                return self.err("expected `read direct`, `read shared` or `read unique`");
            }
        } else {
            field.indirect
        };
        self.typed(
            ExprKind::Field {
                base: Box::new(base),
                field,
                how,
                indirect,
            },
            start,
        )
    }

    fn wrapped(&mut self) -> R<Box<Expr>> {
        self.expect("(")?;
        let e = self.expr()?;
        self.expect(")")?;
        Ok(Box::new(e))
    }

    /// What follows a use (`move`, `copy`, `clone`, or none for a place):
    /// a local, a field of a local or of an expression in parentheses, or
    /// `deref(e)`.
    fn used(&mut self, how: Use, start: Span) -> R<Draft> {
        if self.eat_word("deref") {
            let value = self.wrapped()?;
            return self.typed(ExprKind::Deref { value, how }, start);
        }
        if self.is_local() {
            let local = self.local()?;
            if self.is(".") {
                let kind = ExprKind::Read {
                    local,
                    how: Use::Place,
                };
                let at = self.since(start);
                let Some(ty) = default_ty(&kind, &|l| self.bound_ty(l)) else {
                    return self
                        .err("the local is bound without a type: write the base as `(x#1: T)`");
                };
                let base = Expr { kind, ty, span: at };
                return self.field(base, how, start);
            }
            return Ok(self.shown(ExprKind::Read { local, how }, start));
        }
        if how != Use::Place && self.eat("(") {
            let base = self.grouped(start)?;
            return self.field(base, how, start);
        }
        self.err("expected a local, a field or `deref(…)`")
    }

    fn draft(&mut self) -> R<Draft> {
        let start = self.span();
        if self.is_local() {
            let callee = matches!(self.toks[self.at + 1].0, Tok::Punct("(" | "<"))
                || (matches!(self.toks[self.at + 1].0, Tok::Local(..))
                    && matches!(self.toks[self.at + 2].0, Tok::Punct("(" | "<")));
            if callee {
                let l = self.local()?;
                return self.call(Callee::Local(l), start);
            }
            return self.used(Use::Place, start);
        }
        match self.tok().clone() {
            Tok::Punct("(") => {
                self.bump();
                if self.eat(")") {
                    return Ok(self.shown(ExprKind::Unit, start));
                }
                let inner = self.grouped(start)?;
                if self.is(".") {
                    return self.field(inner, Use::Place, start);
                }
                if self.is("(") || self.is("<") {
                    return self.call(Callee::Value(Box::new(inner)), start);
                }
                // Parentheses that only group.
                Ok(Draft {
                    kind: inner.kind,
                    ty: Some(inner.ty),
                    span: inner.span,
                })
            }
            Tok::Punct("{") => {
                let b = self.block()?;
                Ok(self.shown(ExprKind::Block(b), start))
            }
            Tok::Punct("&") => {
                self.bump();
                let mutable = self.eat_word("mut");
                let place = self.place()?;
                Ok(self.shown(
                    if mutable {
                        ExprKind::RefMut(place)
                    } else {
                        ExprKind::Ref(place)
                    },
                    start,
                ))
            }
            Tok::Int(n, suffix) => {
                self.bump();
                let ty = match suffix.as_deref() {
                    None => None,
                    Some(s) => match width_of(s) {
                        Some(w) => Some(Ty::Int(w)),
                        None => {
                            self.at -= 1;
                            return self.err("expected a width after the number");
                        }
                    },
                };
                Ok(Draft {
                    kind: ExprKind::Int(n),
                    ty,
                    span: self.since(start),
                })
            }
            Tok::Float(x) => {
                self.bump();
                Ok(self.shown(ExprKind::Float(x), start))
            }
            Tok::Str(s) => {
                self.bump();
                Ok(self.shown(ExprKind::Text(s), start))
            }
            Tok::Inst(..) => {
                let inst = self.inst()?;
                if self.is("(")
                    || (self.is("<") && {
                        // Type arguments, then `(` for a call.
                        let mut depth = 0usize;
                        let mut i = self.at;
                        loop {
                            match &self.toks[i].0 {
                                Tok::Punct("<") => depth += 1,
                                Tok::Punct(">") => {
                                    depth -= 1;
                                    if depth == 0 {
                                        break;
                                    }
                                }
                                Tok::End => break,
                                _ => {}
                            }
                            i += 1;
                        }
                        matches!(self.toks.get(i + 1), Some((Tok::Punct("("), _)))
                    })
                {
                    return self.call(Callee::Inst(inst), start);
                }
                let targs = self.targs()?;
                self.typed(ExprKind::FnValue { inst, targs }, start)
            }
            Tok::Quoted(_) => self.named(start),
            Tok::Word(w) => self.worded(&w, start),
            _ => self.err("expected an expression"),
        }
    }

    /// An expression that starts with a name: a constructor.
    fn named(&mut self, start: Span) -> R<Draft> {
        let ctor = self.ctor()?;
        let fields = if self.is("(") {
            self.parens(|p| {
                let labelled = p.is_name() && matches!(p.toks[p.at + 1].0, Tok::Punct("="));
                let label = if labelled {
                    let l = p.spelling()?;
                    p.expect("=")?;
                    Some(l)
                } else {
                    None
                };
                Ok((label, p.expr()?))
            })?
        } else {
            Vec::new()
        };
        self.typed(ExprKind::Ctor { ctor, fields }, start)
    }

    fn worded(&mut self, w: &str, start: Span) -> R<Draft> {
        if !KEYWORDS.contains(&w) {
            return self.named(start);
        }
        if let Some(how) = use_of(w) {
            self.bump();
            return self.used(how, start);
        }
        if w == "deref" {
            return self.used(Use::Place, start);
        }
        self.bump();
        let arith = [Arith::Add, Arith::Sub, Arith::Mul, Arith::Neg, Arith::Div]
            .into_iter()
            .find(|op| arith_word(*op) == w);
        if let Some(op) = arith {
            self.expect("<")?;
            let Tok::Word(num) = self.tok().clone() else {
                return self.err("expected a number type");
            };
            let Some(num) = num_of(&num) else {
                return self.err("expected a number type");
            };
            self.bump();
            self.expect(">")?;
            let args = self.args()?;
            return Ok(self.shown(ExprKind::Arith { op, args, num }, start));
        }
        let cmp = [Cmp::Lt, Cmp::Gt, Cmp::Le, Cmp::Ge]
            .into_iter()
            .find(|op| cmp_word(*op) == w);
        if let Some(op) = cmp {
            let args = self.args()?;
            return Ok(self.shown(ExprKind::Cmp { op, args }, start));
        }
        let kind = match w {
            "true" => ExprKind::Bool(true),
            "false" => ExprKind::Bool(false),
            "nan" => ExprKind::Float(f64::NAN),
            "inf" => ExprKind::Float(f64::INFINITY),
            "declaration" => {
                self.expect("(")?;
                let i = self.number()?;
                self.expect(")")?;
                return self.typed(ExprKind::Declaration(i), start);
            }
            "eq" | "ne" => ExprKind::Eq {
                negate: w == "ne",
                args: self.args()?,
            },
            "not" => ExprKind::Not(self.wrapped()?),
            "and" | "or" => {
                self.expect("(")?;
                let a = Box::new(self.expr()?);
                self.expect(",")?;
                let b = Box::new(self.expr()?);
                self.expect(")")?;
                if w == "and" {
                    ExprKind::And(a, b)
                } else {
                    ExprKind::Or(a, b)
                }
            }
            "extern" => {
                let name = self.name()?;
                return self.call(Callee::Extern(name), start);
            }
            "builtin" => {
                let name = self.spelling()?;
                return self.call(Callee::Builtin(name), start);
            }
            "resume" => {
                let k = self.local()?;
                return self.call(Callee::Cont(k), start);
            }
            "match" => {
                let by_ref = self.eat_word("by_ref");
                let exhaustive = !self.eat_word("partial");
                let scrut = self.expr()?;
                self.expect("{")?;
                let mut arms = Vec::new();
                while !self.eat("}") {
                    let pat = self.pat()?;
                    let guard = if self.eat_word("if") {
                        Some(self.expr()?)
                    } else {
                        None
                    };
                    self.expect("=>")?;
                    let body = self.expr()?;
                    self.expect(",")?;
                    arms.push(MatchArm { pat, guard, body });
                }
                ExprKind::Match(Box::new(MatchNode {
                    scrut,
                    by_ref,
                    arms,
                    exhaustive,
                    span: self.since(start),
                }))
            }
            "if" => {
                let cond = Box::new(self.expr()?);
                self.expect_word("then")?;
                let then = Box::new(self.expr()?);
                let otherwise = if self.eat_word("else") {
                    Some(Box::new(self.expr()?))
                } else {
                    None
                };
                ExprKind::If {
                    cond,
                    then,
                    otherwise,
                }
            }
            "closure" => self.closure(start)?,
            "perform" => {
                let op = self.op()?;
                let args = self.args()?;
                let quant = self.quant()?;
                let detached = self.eat_word("detached");
                let instance = self.instance()?;
                let unwind = self.unwind()?;
                self.expect(":")?;
                let result = self.ty()?;
                ExprKind::Perform(Box::new(PerformNode {
                    op,
                    instance,
                    quant,
                    detached,
                    unwind,
                    args,
                    result,
                    span: self.since(start),
                }))
            }
            "handle" => self.handle(start)?,
            "inject" => {
                self.expect("(")?;
                let union = self.number()?;
                self.expect(",")?;
                let variant = self.number()?;
                self.expect(",")?;
                let value = Box::new(self.expr()?);
                self.expect(")")?;
                ExprKind::Inject {
                    union,
                    variant,
                    value,
                }
            }
            "remap" => {
                self.expect("(")?;
                let from = self.number()?;
                self.expect(",")?;
                let to = self.ty()?;
                self.expect(",")?;
                let value = Box::new(self.expr()?);
                self.expect(")")?;
                ExprKind::Remap { from, to, value }
            }
            "tempref" => ExprKind::TempRef(self.wrapped()?),
            "shown" => ExprKind::Shown(self.wrapped()?),
            "budget" => {
                let id = self.number()?;
                let memory = self.eat_word("memory");
                let m = self.eat_word("m");
                self.expect("(")?;
                let steps = self.expr()?;
                self.expect(",")?;
                let body = self.expr()?;
                self.expect(")")?;
                ExprKind::Budget(Box::new(BudgetNode {
                    id,
                    memory,
                    steps,
                    body,
                    m,
                    span: self.since(start),
                }))
            }
            "unreachable" => {
                let e = self.wrapped()?;
                return self.typed(ExprKind::Unreachable(e), start);
            }
            "fncast" => {
                let e = self.wrapped()?;
                return self.typed(ExprKind::FnCast(e), start);
            }
            _ => {
                self.at -= 1;
                return self.err("expected an expression");
            }
        };
        Ok(self.shown(kind, start))
    }

    fn closure(&mut self, start: Span) -> R<ExprKind> {
        let borrowed = self.eat_word("borrowed");
        let pure = self.eat_word("pure");
        let params = self.parens(|p| {
            let l = p.binding()?;
            p.expect(":")?;
            let t = p.ty()?;
            p.bind(&l, Some(&t));
            Ok((l, t))
        })?;
        self.expect("->")?;
        let ret = self.ty()?;
        self.expect_word("as")?;
        self.expect_word("fn")?;
        let fn_ty = self.fn_ty()?;
        let clones = self.locals("clones")?;
        let refs = if self.eat_word("refs") {
            self.parens(|p| {
                let inner = p.binding()?;
                p.bind(&inner, None);
                p.expect("=")?;
                p.expect("&")?;
                let mutable = p.eat_word("mut");
                let outer = p.local()?;
                Ok(CapturedRef {
                    inner,
                    outer,
                    mutable,
                })
            })?
        } else {
            Vec::new()
        };
        let owned_refs = self.locals("owned_refs")?;
        self.expect("=>")?;
        let body = self.expr()?;
        Ok(ExprKind::Closure(Box::new(ClosureNode {
            params,
            ret,
            body,
            fn_ty,
            borrowed,
            clones,
            pure,
            refs,
            owned_refs,
            span: self.since(start),
        })))
    }

    fn instance(&mut self) -> R<Option<OperationInstance>> {
        if !self.eat_word("instance") {
            return Ok(None);
        }
        let type_args = self.targs()?;
        let params = self.parens(|p| p.ty())?;
        self.expect("->")?;
        let answer = self.ty()?;
        let Tok::Word(w) = self.tok().clone() else {
            return self.err("expected an admission");
        };
        let Some((admission, _)) = ADMISSIONS.iter().find(|(_, word)| *word == w) else {
            return self.err("expected an admission");
        };
        self.bump();
        Ok(Some(OperationInstance {
            type_args,
            params,
            answer,
            admission: *admission,
        }))
    }

    fn handle(&mut self, start: Span) -> R<ExprKind> {
        let id = self.number()?;
        let body_tier = self.tier()?;
        let m = self.eat_word("m");
        let kept = self.eat_word("kept");
        let detached = self.eat_word("detached");
        let host_ret = if self.eat_word("host_ret") {
            Some(self.ty()?)
        } else {
            None
        };
        let captures = self.locals("captures")?;
        let clones = self.locals("clones")?;
        self.expect_word("do")?;
        let body = self.expr()?;
        let body_ty = if self.eat_word("as") {
            self.ty()?
        } else {
            body.ty.clone()
        };
        self.expect_word("with")?;
        self.expect("{")?;
        let mut ret = None;
        let (mut direct, mut aborts, mut susp) = (Vec::new(), Vec::new(), Vec::new());
        while !self.eat("}") {
            let arm_start = self.span();
            if self.eat_word("return") {
                let pat = self.pat()?;
                self.expect("=>")?;
                let body = self.expr()?;
                self.expect(",")?;
                if ret.is_some() {
                    self.at -= 1;
                    return self.err("a handler has one return arm");
                }
                ret = Some(ReturnArm { pat, body });
                continue;
            }
            let arms = if self.eat_word("direct") {
                &mut direct
            } else if self.eat_word("abort") {
                &mut aborts
            } else if self.eat_word("suspend") {
                &mut susp
            } else {
                return self.err("expected an arm: return, direct, abort or suspend");
            };
            let op = self.op()?;
            let pats = self.parens(|p| p.pat())?;
            self.expect_word("params")?;
            let params = self.parens(|p| p.ty())?;
            self.expect_word("answer")?;
            let k_ans = self.ty()?;
            let k = if self.eat_word("k") {
                let k = self.binding()?;
                self.bind(&k, None);
                Some(k)
            } else {
                None
            };
            let instance = self.instance()?;
            let instantiated = self.eat_word("instantiated");
            let guard = if self.eat_word("if") {
                Some(self.expr()?)
            } else {
                None
            };
            self.expect("=>")?;
            let body = self.expr()?;
            self.expect(",")?;
            arms.push(OpArm {
                op,
                instance,
                params,
                pats,
                guard,
                body,
                k,
                k_ans,
                instantiated,
                span: self.since(arm_start),
            });
        }
        self.expect(":")?;
        let result = self.ty()?;
        Ok(ExprKind::Handle(Box::new(HandleNode {
            id,
            body,
            body_ty,
            result,
            ret,
            direct,
            aborts,
            susp,
            captures,
            clones,
            body_tier,
            m,
            host_ret,
            kept,
            detached,
            span: self.since(start),
        })))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::text::STD_TYPES;

    /// Every standard type the printer writes as `std Name(…)` reads back as
    /// the same type: the printer and the parser agree on the set.
    #[test]
    fn every_std_type_round_trips_through_text() {
        let all = [
            StdType::SynDeclaration,
            StdType::Ref,
            StdType::Weak,
            StdType::Mutex,
            StdType::MutexGuard,
            StdType::Atomic,
            StdType::Bytes,
            StdType::Pending,
            StdType::Secret,
            StdType::Signal,
            StdType::CancelSource,
            StdType::Region,
            StdType::Place,
            StdType::RcRegion,
            StdType::RcPlace,
            StdType::Slots,
            StdType::OpaqueHost,
        ];
        // Adding a variant without listing it above stops compiling here.
        for s in all {
            match s {
                StdType::SynDeclaration
                | StdType::Ref
                | StdType::Weak
                | StdType::Mutex
                | StdType::MutexGuard
                | StdType::Atomic
                | StdType::Bytes
                | StdType::Pending
                | StdType::Secret
                | StdType::Signal
                | StdType::CancelSource
                | StdType::Region
                | StdType::Place
                | StdType::RcRegion
                | StdType::RcPlace
                | StdType::Slots
                | StdType::OpaqueHost => {}
            }
        }
        assert_eq!(STD_TYPES.len(), all.len());
        let pkg = Package::default();
        for s in all {
            for args in [vec![], vec![Ty::Text]] {
                let ty = Ty::Std(s, args);
                let mut printer = crate::text::print::Printer::new(&pkg);
                printer.ty(&ty);
                let text = printer.out;
                let toks = lex(&text).unwrap();
                let mut p = Parser {
                    toks,
                    at: 0,
                    names: HashMap::new(),
                    bound: HashMap::new(),
                    insts: Vec::new(),
                    pkg: Package::default(),
                };
                let back = p.ty().unwrap_or_else(|e| panic!("`{text}`: {}", e.message));
                assert_eq!(back, ty, "`{text}`");
            }
        }
    }
}
