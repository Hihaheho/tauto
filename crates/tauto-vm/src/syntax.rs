//! `syn_parse` on the machines. The parse runs in Tauto, on the machine of `totes/vm`
//! (`src/syn.taut`): what is written here is the grammar's tables and, for each production,
//! what its node becomes (`tauto_syntax::Shape`), with the machine's constructors already
//! chosen, so that the machine decides nothing about the schema itself. The machine of this
//! crate (`TAUTO_VM=rust`) parses with `tauto_syntax`, as the other backends do.

use tauto_nir::{Name, Package, SyntaxParser};
use tauto_syntax::{Element, Payload, Shape, Sym, Tables, TypeDef};

use crate::wire::Writer;

type Rs<T> = Result<T, String>;

/// A constructor of the package's data type `data` whose name is `ctor` (or whose full name
/// ends in it), with its full name and its fields' names; `default` when the package has no
/// such data type (the parse never makes its values).
fn ctor_of<'a>(
    pkg: &'a Package,
    parser: &SyntaxParser,
    data: &str,
    ctor: &str,
    default: &'a [&'a str],
) -> Rs<(Name, Name, Vec<Option<String>>, bool)> {
    let Some(d) = pkg
        .datas
        .iter()
        .find(|d| parser.data_bindings.get(data) == Some(&d.name))
    else {
        return Ok((
            Name::from(data),
            Name::from(ctor),
            default.iter().map(|n| Some(n.to_string())).collect(),
            true,
        ));
    };
    let c = d
        .ctors
        .iter()
        .find(|c| {
            d.is_struct
                || parser
                    .constructor_bindings
                    .get(&(data.to_string(), ctor.to_string()))
                    == Some(&c.name)
        })
        .ok_or_else(|| format!("a runtime syntax parser whose type {data} has no {ctor}"))?;
    Ok((
        d.name.clone(),
        c.name.clone(),
        c.fields.iter().map(|f| f.name.clone()).collect(),
        d.is_struct,
    ))
}

/// The machine's number of the constructor.
fn id(
    w: &mut Writer,
    pkg: &Package,
    parser: &SyntaxParser,
    data: &str,
    ctor: &str,
    default: &[&str],
) -> Rs<u32> {
    let (data, name, names, is_struct) = ctor_of(pkg, parser, data, ctor, default)?;
    let names: Vec<Option<&str>> = names.iter().map(Option::as_deref).collect();
    Ok(w.ctor(&data, &name, &names, is_struct))
}

/// The parser as the machine reads it (`syn_read` in `totes/vm/src/syn.taut`), after the tag of
/// the operation.
pub(crate) fn write(w: &mut Writer, pkg: &Package, p: &SyntaxParser) -> Rs<String> {
    let tables = Tables::read(&p.tables).map_err(|e| e.to_string())?;
    if tables.embed_terminal().is_some() {
        return Err("a runtime syntax parser of a grammar with TautoExpr".into());
    }
    // The constructors first: they are written as numbers.
    let span = id(w, pkg, p, "SynSpan", "SynSpan", &["id"])?;
    let ctx = id(w, pkg, p, "SynCtx", "SynCtx", &["scopes"])?;
    let token = id(w, pkg, p, "SynToken", "SynToken", &["text", "span", "ctx"])?;
    let diag = id(
        w,
        pkg,
        p,
        "SynDiag",
        "SynDiag",
        &["message", "at", "expected", "code", "args"],
    )?;
    let arg = id(w, pkg, p, "SynArg", "SynArg", &["name", "value"])?;
    let schema = &tables.schema().types;
    // (machine constructor, whether its first field is the span) by (type, constructor).
    let node = |w: &mut Writer, ty: u32, c: u32| -> Rs<(u32, bool)> {
        let def = schema
            .get(ty as usize)
            .ok_or("a runtime syntax parser whose tables name no type")?;
        let (name, ctor, spanned) = match def {
            TypeDef::Struct { name, .. } => (name, name.as_str(), true),
            TypeDef::Enum { name, ctors } => {
                let c = ctors
                    .get(c as usize)
                    .ok_or("a runtime syntax parser whose tables name no constructor")?;
                (
                    name,
                    c.name.as_str(),
                    matches!(c.payload, Payload::Record(_)),
                )
            }
        };
        let data = tauto_syntax::type_name(&p.name, name);
        Ok((id(w, pkg, p, &data, ctor, &[])?, spanned))
    };
    let shapes = tables.shapes();
    let mut nodes = Vec::with_capacity(shapes.len());
    for s in &shapes {
        let e = match s {
            Shape::Node { ty, ctor, .. }
            | Shape::Some(Element::Node { ty, ctor, .. })
            | Shape::More(Element::Node { ty, ctor, .. }) => Some(node(w, *ty, *ctor)?),
            _ => None,
        };
        nodes.push(e);
    }

    let saved = std::mem::take(&mut w.out);
    w.text(&p.name);
    for t in tables.scan_texts() {
        w.text(&t);
    }
    let terminals = tables.terminals();
    w.num(terminals.len());
    for t in terminals {
        w.text(t);
    }
    w.num(terminals.len());
    for t in 0..terminals.len() {
        w.yn(tables.is_skipped(t as u32));
    }
    w.num(tables.start());
    match tables.lr_states() {
        None => {
            w.yn(false);
            let n = tables.non_terminals().len();
            w.num(n);
            for nt in 0..n {
                match tables.lookahead_of(nt as u32) {
                    None => w.yn(false),
                    Some((prod0, k, transitions)) => {
                        w.yn(true);
                        w.num(plus_one(prod0));
                        w.num(k);
                        w.num(transitions.len());
                        for &(from, term, to, prod) in transitions {
                            w.num(from);
                            w.num(term);
                            w.num(to);
                            w.num(plus_one(prod));
                        }
                    }
                }
            }
        }
        Some(states) => {
            w.yn(true);
            w.num(states.len());
            for (actions, gotos) in states {
                w.num(actions.len());
                for &(term, kind, arg) in actions {
                    w.num(term);
                    w.num(kind);
                    w.num(arg);
                }
                w.num(gotos.len());
                for &(nt, to) in gotos {
                    w.num(nt);
                    w.num(to);
                }
            }
        }
    }
    let productions = tables.productions();
    w.num(productions.len());
    for ((prod, shape), node) in productions.iter().zip(&shapes).zip(&nodes) {
        w.num(prod.lhs);
        w.num(prod.rhs.len());
        for s in &prod.rhs {
            match *s {
                Sym::Nt(n) => {
                    w.yn(false);
                    w.num(n);
                }
                Sym::Term(t) => {
                    w.yn(true);
                    w.num(t);
                }
            }
        }
        let element = |w: &mut Writer, e: &Element| match e {
            Element::Item => w.num(0),
            Element::Node { keep, .. } => {
                let (c, spanned) = node.expect("a node's constructor");
                w.num(1);
                w.num(c);
                w.yn(spanned);
                bools(w, keep);
            }
        };
        match shape {
            Shape::Node { keep, .. } => {
                let (c, spanned) = node.expect("a node's constructor");
                w.num(0);
                w.num(c);
                w.yn(spanned);
                bools(w, keep);
            }
            Shape::Pass => w.num(1),
            Shape::Some(e) => {
                w.num(2);
                element(w, e);
            }
            Shape::None => w.num(3),
            Shape::Empty => w.num(4),
            Shape::More(e) => {
                w.num(5);
                element(w, e);
            }
            Shape::Bad(m) => {
                w.num(6);
                w.text(m);
            }
        }
    }
    for c in [span, ctx, token, diag, arg] {
        w.num(c);
    }
    Ok(std::mem::replace(&mut w.out, saved))
}

fn plus_one(n: i64) -> u64 {
    u64::try_from(n).map_or(0, |n| n + 1)
}

fn bools(w: &mut Writer, bs: &[bool]) {
    w.num(bs.len());
    for b in bs {
        w.yn(*b);
    }
}

/// A parser of the machine of this crate: the tables, and the constructors of each type of
/// the schema (with whether the first field is the span) and of the values of a parse.
pub struct SynRt {
    name: String,
    tables: Tables,
    types: Vec<Vec<(std::rc::Rc<crate::code::Ctor>, bool)>>,
    span: std::rc::Rc<crate::code::Ctor>,
    ctx: std::rc::Rc<crate::code::Ctor>,
    token: std::rc::Rc<crate::code::Ctor>,
    diag: std::rc::Rc<crate::code::Ctor>,
    arg: std::rc::Rc<crate::code::Ctor>,
}

/// The parser of `p`, with its constructors made in the program.
pub(crate) fn prepare(
    prog: &mut crate::code::Program,
    pkg: &Package,
    p: &SyntaxParser,
) -> Rs<SynRt> {
    let tables = Tables::read(&p.tables).map_err(|e| e.to_string())?;
    let mut make = |data: &str, ctor: &str, default: &[&str]| -> Rs<_> {
        let (data, name, names, is_struct) = ctor_of(pkg, p, data, ctor, default)?;
        let names: Vec<Option<&str>> = names.iter().map(Option::as_deref).collect();
        let c = prog.ctor(&data, &name, &names, is_struct);
        Ok(c)
    };
    let mut types = Vec::new();
    for t in &tables.schema().types {
        types.push(match t {
            TypeDef::Struct { name, .. } => {
                vec![(
                    make(&tauto_syntax::type_name(&p.name, name), name, &[])?,
                    true,
                )]
            }
            TypeDef::Enum { name, ctors } => {
                let data = tauto_syntax::type_name(&p.name, name);
                ctors
                    .iter()
                    .map(|c| {
                        Ok((
                            make(&data, &c.name, &[])?,
                            matches!(c.payload, Payload::Record(_)),
                        ))
                    })
                    .collect::<Rs<Vec<_>>>()?
            }
        });
    }
    Ok(SynRt {
        name: p.name.clone(),
        span: make("SynSpan", "SynSpan", &["id"])?,
        ctx: make("SynCtx", "SynCtx", &["scopes"])?,
        token: make("SynToken", "SynToken", &["text", "span", "ctx"])?,
        diag: make(
            "SynDiag",
            "SynDiag",
            &["message", "at", "expected", "code", "args"],
        )?,
        arg: make("SynArg", "SynArg", &["name", "value"])?,
        tables,
        types,
    })
}

impl SynRt {
    fn data(
        &self,
        ctor: &std::rc::Rc<crate::code::Ctor>,
        fields: Vec<crate::value::Value>,
    ) -> crate::value::Value {
        crate::value::Value::Data(std::rc::Rc::new(crate::value::Data {
            ctor: ctor.clone(),
            fields,
        }))
    }

    fn span_of(&self, at: u32) -> crate::value::Value {
        self.data(&self.span, vec![crate::value::Value::Int(at as i128)])
    }

    fn value(
        &self,
        k: &crate::builtins::Known,
        text: &str,
        ast: &tauto_syntax::Ast,
    ) -> crate::value::Value {
        use crate::value::Value;
        use tauto_syntax::Ast;
        match ast {
            Ast::Token(t) => {
                let s = text.get(t.start as usize..t.end as usize).unwrap_or("");
                let ctx = self.data(&self.ctx, vec![k.list(std::iter::empty::<Value>())]);
                self.data(
                    &self.token,
                    vec![Value::text(s), self.span_of(t.start), ctx],
                )
            }
            Ast::List(items) => k.list(
                items
                    .iter()
                    .map(|i| self.value(k, text, i))
                    .collect::<Vec<_>>()
                    .into_iter(),
            ),
            Ast::Opt(None) => k.none(),
            Ast::Opt(Some(v)) => k.some(self.value(k, text, v)),
            Ast::Node {
                ty,
                ctor,
                span,
                fields,
            } => {
                let (c, spanned) = &self.types[*ty as usize][*ctor as usize];
                let mut out = Vec::with_capacity(fields.len() + 1);
                if *spanned {
                    out.push(self.span_of(span.0));
                }
                out.extend(fields.iter().map(|f| self.value(k, text, f)));
                self.data(c, out)
            }
        }
    }

    /// `Ok` of the values of the text, or `Err` of the diagnostic.
    pub(crate) fn parse(&self, k: &crate::builtins::Known, text: &str) -> crate::value::Value {
        use crate::value::Value;
        match tauto_syntax::parse_ast(&self.name, &self.tables, text) {
            Ok(ast) => k.ok(self.value(k, text, &ast)),
            Err(d) => {
                let expected = k.list(
                    d.expected
                        .iter()
                        .map(|e| Value::text(e))
                        .collect::<Vec<_>>()
                        .into_iter(),
                );
                k.err(self.data(
                    &self.diag,
                    vec![
                        Value::text(&d.message),
                        Value::Int(d.at as i128),
                        expected,
                        Value::text("macro.syntax_error"),
                        k.list(
                            d.args
                                .iter()
                                .map(|(n, v)| {
                                    self.data(&self.arg, vec![Value::text(n), Value::text(v)])
                                })
                                .collect::<Vec<_>>()
                                .into_iter(),
                        ),
                    ],
                ))
            }
        }
    }
}
