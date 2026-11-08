//! Embedded runtime tables and schema-directed conversion to native AST types.
use crate::{
    Gen,
    expr::field_ident,
    tok::{Rs, id, lit, num, raw},
};
use quote::quote;
use tauto_nir::Indirect;
use tauto_syntax::{FieldTy, Payload, Tables, TypeDef};

impl Gen<'_> {
    fn syntax_ctor(&self, parser: usize, data: &str, ctor: &str, values: Vec<Rs>) -> Rs {
        let d = self
            .data(&self.pkg.syntax_parsers[parser].data_bindings[data])
            .expect("runtime syntax data is retained by NIR");
        let c = d
            .ctors
            .iter()
            .find(|c| {
                d.is_struct
                    || self.pkg.syntax_parsers[parser]
                        .constructor_bindings
                        .get(&(data.to_string(), ctor.to_string()))
                        == Some(&c.name)
            })
            .unwrap_or_else(|| panic!("schema constructor {data}::{ctor}: {:?}", d.ctors));
        assert_eq!(values.len(), c.fields.len());
        let path = self.ctor_path(&d.name, &c.name, d.is_struct);
        let values: Vec<_> = values
            .into_iter()
            .zip(&c.fields)
            .map(|(v, f)| match f.indirect {
                Indirect::Shared => quote!(Rc::new(#v).into()),
                Indirect::Unique => quote!(Box::new(#v).into()),
                _ => v,
            })
            .collect();
        if c.fields.iter().any(|f| f.name.is_some()) {
            let fields = c.fields.iter().zip(values).map(|(f, v)| {
                let n = field_ident(f.name.as_deref().unwrap());
                quote!(#n: #v)
            });
            quote!(#path { #(#fields),* })
        } else if values.is_empty() {
            if d.is_struct { quote!(#path {}) } else { path }
        } else {
            quote!(#path(#(#values),*))
        }
    }

    fn syntax_list(&self, parser: usize, items: Rs) -> Rs {
        let nil = self.syntax_ctor(parser, "List", "Nil", vec![]);
        let cons = self.syntax_ctor(parser, "List", "Cons", vec![quote!(item), quote!(tail)]);
        quote!((#items).into_iter().rev().fold(#nil, |tail, item| #cons))
    }

    fn syntax_field(&self, parser: usize, syntax: &str, ty: &FieldTy, ast: Rs) -> Rs {
        match ty {
            FieldTy::Named(name) => {
                let f = id(&format!("__tauto_syn_{parser}_{name}"));
                quote!(#f(#ast, text))
            }
            FieldTy::Token => {
                let span = self.syntax_ctor(
                    parser,
                    "SynSpan",
                    "SynSpan",
                    vec![quote!(token.start as u64)],
                );
                let empty = self.syntax_ctor(parser, "List", "Nil", vec![]);
                let ctx = self.syntax_ctor(parser, "SynCtx", "SynCtx", vec![empty]);
                let token = self.syntax_ctor(
                    parser,
                    "SynToken",
                    "SynToken",
                    vec![
                        quote!(Text::from(
                            text.get(token.start as usize..token.end as usize)
                                .unwrap_or("")
                        )),
                        span,
                        ctx,
                    ],
                );
                quote!({ let __tauto_syntax_runtime::Ast::Token(token) = #ast else { unreachable!("validated token schema") }; #token })
            }
            FieldTy::List(inner) => {
                let value = self.syntax_field(parser, syntax, inner, quote!(item));
                let list = self.syntax_list(
                    parser,
                    quote!(items.into_iter().map(|item| #value).collect::<Vec<_>>()),
                );
                quote!({ let __tauto_syntax_runtime::Ast::List(items) = #ast else { unreachable!("validated list schema") }; #list })
            }
            FieldTy::Opt(inner) => {
                let value = self.syntax_field(parser, syntax, inner, quote!(*item));
                quote!({ let __tauto_syntax_runtime::Ast::Opt(item) = #ast else { unreachable!("validated option schema") }; item.map(|item| #value) })
            }
            // Expression holes are compile-time syntax literals, not runtime tokens.
            FieldTy::Expr => unreachable!("NIR rejects runtime expression holes"),
        }
    }

    pub(crate) fn syntax_parsers(&self) -> Rs {
        if self.pkg.syntax_parsers.is_empty() {
            return Rs::new();
        }
        let mut out = embedded_runtime();
        for (i, parser) in self.pkg.syntax_parsers.iter().enumerate() {
            let tables = Tables::read(&parser.tables).expect("NIR validates embedded tables");
            for (index, ty) in tables.schema().types.iter().enumerate() {
                let (name, ctors): (&str, Vec<(&str, bool, Vec<&FieldTy>)>) = match ty {
                    TypeDef::Struct { name, fields, .. } => (
                        name,
                        vec![(name, true, fields.iter().map(|(_, t)| t).collect())],
                    ),
                    TypeDef::Enum { name, ctors } => (
                        name,
                        ctors
                            .iter()
                            .map(|c| match &c.payload {
                                Payload::Record(fields) => (
                                    c.name.as_str(),
                                    true,
                                    fields.iter().map(|(_, t)| t).collect(),
                                ),
                                Payload::Single(field) => (c.name.as_str(), false, vec![field]),
                            })
                            .collect(),
                    ),
                };
                let data = tauto_syntax::type_name(&parser.name, name);
                let result = Self::data_name(self.pkg, &parser.data_bindings[&data]);
                let fun = id(&format!("__tauto_syn_{i}_{name}"));
                let mut arms = Vec::new();
                for (ctor_index, (ctor, span, fields)) in ctors.into_iter().enumerate() {
                    let mut values = Vec::new();
                    if span {
                        values.push(self.syntax_ctor(
                            i,
                            "SynSpan",
                            "SynSpan",
                            vec![quote!(span.0 as u64)],
                        ));
                    }
                    for field in fields {
                        values.push(self.syntax_field(
                            i,
                            &parser.name,
                            field,
                            quote!(fields.next().expect("validated schema field")),
                        ));
                    }
                    let value = self.syntax_ctor(i, &data, ctor, values);
                    let c = num(ctor_index as u64);
                    arms.push(quote!(#c => #value));
                }
                let index = num(index as u64);
                out.extend(quote! {
                    fn #fun(ast: __tauto_syntax_runtime::Ast, text: &str) -> #result {
                        let __tauto_syntax_runtime::Ast::Node { ty, ctor, span, fields } = ast else { unreachable!("validated node schema") };
                        assert_eq!(ty, #index);
                        let mut fields = fields.into_iter();
                        match ctor { #(#arms,)* _ => unreachable!("validated constructor") }
                    }
                });
            }
            let start = tables.start_type().expect("syntax start type");
            let start_name = match &tables.schema().types[start as usize] {
                TypeDef::Struct { name, .. } | TypeDef::Enum { name, .. } => name,
            };
            let convert = id(&format!("__tauto_syn_{i}_{start_name}"));
            let fun = id(&format!("__tauto_parse_{i}"));
            let name = lit(&parser.name);
            let source = lit(&parser.tables);
            let result = self.ty(&parser.result);
            let expected = self.syntax_list(
                i,
                quote!(d.expected.into_iter().map(Text::from).collect::<Vec<_>>()),
            );
            let arg = self.syntax_ctor(
                i,
                "SynArg",
                "SynArg",
                vec![quote!(Text::from(n)), quote!(Text::from(v))],
            );
            let args = self.syntax_list(
                i,
                quote!(d.args.into_iter().map(|(n, v)| #arg).collect::<Vec<_>>()),
            );
            let diag = self.syntax_ctor(
                i,
                "SynDiag",
                "SynDiag",
                vec![
                    quote!(Text::from(d.message)),
                    quote!(d.at as u64),
                    expected,
                    quote!(Text::from("macro.syntax_error")),
                    args,
                ],
            );
            out.extend(quote! {
                fn #fun(text: Text) -> #result {
                    static TABLES: std::sync::OnceLock<__tauto_syntax_runtime::Tables> = std::sync::OnceLock::new();
                    let tables = TABLES.get_or_init(|| __tauto_syntax_runtime::Tables::read(#source).expect("build-time validated tables"));
                    match __tauto_syntax_runtime::parse_ast(#name, tables, &text) {
                        Ok(ast) => Ok(#convert(ast, &text)),
                        Err(d) => Err(#diag),
                    }
                }
            });
        }
        out
    }
}

fn embedded_runtime() -> Rs {
    let modules = [
        ("ast", include_str!("../../tauto-syntax/src/ast.rs")),
        ("parse", include_str!("../../tauto-syntax/src/parse.rs")),
        ("scan", include_str!("../../tauto-syntax/src/scan.rs")),
        ("tables", include_str!("../../tauto-syntax/src/tables.rs")),
        ("runtime", include_str!("../../tauto-syntax/src/runtime.rs")),
    ]
    .into_iter()
    .map(|(name, source)| {
        let name = id(name);
        let source = raw(&source.replace("crate::", "super::"));
        quote!(mod #name { #source })
    });
    quote! {
        mod __tauto_syntax_runtime {
            #(#modules)*
            pub use ast::{Ast, build_ast};
            pub use parse::{Limits, ParseError, parse};
            pub use tables::Tables;
            pub use runtime::parse_ast;
            pub const END_OF_INPUT: u32 = 0;
        }
    }
}
