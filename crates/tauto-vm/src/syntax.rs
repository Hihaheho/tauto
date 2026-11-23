//! `syn_parse` on the machines. The parse runs in Tauto, on the machine of `totes/vm`, with
//! the parser of `totes/synrun`: what is written here is the parser as
//! `Tables::runtime_text` writes it, with the machine's constructors already chosen, so that
//! the machine decides nothing about the schema itself. The machine of this
//! crate (`TAUTO_VM=rust`) parses with `tauto_syntax`, as the other backends do.

use tauto_nir::{Name, Package, SyntaxParser};
use tauto_syntax::{Payload, RuntimeIds, Tables, TypeDef};

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

/// The parser as the machine reads it (`w_syn_parser` in `totes/synrun/src/read.taut`), after
/// the tag of the operation.
pub(crate) fn write(w: &mut Writer, pkg: &Package, p: &SyntaxParser) -> Rs<String> {
    let tables = Tables::read(&p.tables).map_err(|e| e.to_string())?;
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
    let text = tables.runtime_text(
        &p.name,
        &mut |ty, c| {
            let (name, ctor, _) = tables.runtime_constructor(ty, c)?;
            let data = tauto_syntax::type_name(&p.name, name);
            id(w, pkg, p, &data, ctor, &[])
        },
        RuntimeIds {
            span,
            ctx,
            token,
            diag,
            arg,
        },
    )?;
    Ok(text)
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
