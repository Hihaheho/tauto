//! Validate the native runtime parser boundary before code generation.
use super::*;
use tauto_syntax::{FieldTy, Payload, Tables, TypeDef};
impl Lowerer<'_> {
    pub(super) fn runtime_syntax(&mut self, args: &[Expr], ty: &Ty, span: Span) -> R<()> {
        let [
            Expr {
                kind: ExprKind::Text(syntax),
                ..
            },
            Expr {
                kind: ExprKind::Text(sha),
                ..
            },
            _,
        ] = args
        else {
            return unsupported(msg!("nir-runtime-syn-parse-needs-a-literal"), span);
        };
        if !self
            .syntax_parsers
            .iter()
            .any(|p| p.name == *syntax && p.sha == *sha && p.result == *ty)
        {
            let tables = tauto::syntax::tables_of(sha).map_err(|m| Unsupported {
                what: m,
                span: Some(span),
            })?;
            let Some(start) = tables
                .start_type()
                .and_then(|i| tables.schema().types.get(i as usize))
            else {
                return unsupported(msg!("nir-runtime-syntax-parsing-needs-a-generated"), span);
            };
            let (tauto_syntax::TypeDef::Struct {
                name: start_name, ..
            }
            | tauto_syntax::TypeDef::Enum {
                name: start_name, ..
            }) = start;
            let result = Ty::Result(
                Box::new(Ty::Data(
                    tauto_syntax::type_name(syntax, start_name),
                    vec![],
                )),
                Box::new(Ty::Data("SynDiag".into(), vec![])),
            );
            if *ty != result {
                return unsupported(msg!("nir-runtime-syn-parse-result-must-match"), span);
            }
            fn has_expr(t: &tauto_syntax::FieldTy) -> bool {
                match t {
                    tauto_syntax::FieldTy::Expr => true,
                    tauto_syntax::FieldTy::List(t) | tauto_syntax::FieldTy::Opt(t) => has_expr(t),
                    _ => false,
                }
            }
            let expr = tables.schema().types.iter().any(|t| match t {
                tauto_syntax::TypeDef::Struct { fields, .. } => {
                    fields.iter().any(|(_, t)| has_expr(t))
                }
                tauto_syntax::TypeDef::Enum { ctors, .. } => {
                    ctors.iter().any(|c| match &c.payload {
                        tauto_syntax::Payload::Record(fields) => {
                            fields.iter().any(|(_, t)| has_expr(t))
                        }
                        tauto_syntax::Payload::Single(t) => has_expr(t),
                    })
                }
            });
            if expr {
                return unsupported(msg!("nir-runtime-syntax-parsing-does-not-support"), span);
            }
            self.validate_syntax_schema(syntax, &tables, span)?;
            self.syntax_parsers.push(SyntaxParser {
                name: syntax.clone(),
                sha: sha.clone(),
                tables: tables.source().to_owned(),
                result: ty.clone(),
            });
        }
        Ok(())
    }

    fn validate_syntax_schema(&self, syntax: &str, tables: &Tables, span: Span) -> R<()> {
        let named = |name: &str| Ty::Data(name.into(), vec![]);
        let list = |ty| Ty::Data("List".into(), vec![ty]);
        let field = |name: &str, ty| (Some(name.to_owned()), ty);
        let token = tables.schema().types.iter().any(|t| match t {
            TypeDef::Struct { fields, .. } => fields.iter().any(|(_, t)| has_token(t)),
            TypeDef::Enum { ctors, .. } => ctors.iter().any(|c| match &c.payload {
                Payload::Record(fields) => fields.iter().any(|(_, t)| has_token(t)),
                Payload::Single(t) => has_token(t),
            }),
        });
        self.syntax_data(
            "SynSpan",
            true,
            &[],
            vec![("SynSpan".into(), vec![field("id", Ty::Int(Width::U64))])],
            span,
        )?;
        self.syntax_data(
            "SynDiag",
            true,
            &[],
            vec![(
                "SynDiag".into(),
                vec![
                    field("message", Ty::Text),
                    field("at", Ty::Int(Width::U64)),
                    field("expected", list(Ty::Text)),
                    field("code", Ty::Text),
                ],
            )],
            span,
        )?;
        self.syntax_data(
            "List",
            false,
            &["A".into()],
            vec![
                ("Nil".into(), vec![]),
                (
                    "Cons".into(),
                    vec![
                        (None, Ty::Param("A".into())),
                        (None, list(Ty::Param("A".into()))),
                    ],
                ),
            ],
            span,
        )?;
        if token {
            self.syntax_data(
                "SynCtx",
                true,
                &[],
                vec![(
                    "SynCtx".into(),
                    vec![field("scopes", list(Ty::Int(Width::U64)))],
                )],
                span,
            )?;
            self.syntax_data(
                "SynToken",
                true,
                &[],
                vec![(
                    "SynToken".into(),
                    vec![
                        field("text", Ty::Text),
                        field("span", named("SynSpan")),
                        field("ctx", named("SynCtx")),
                    ],
                )],
                span,
            )?;
        }
        let record = |fields: &[(String, FieldTy)]| {
            let mut out = vec![field("span", named("SynSpan"))];
            out.extend(fields.iter().map(|(n, t)| field(n, field_ty(syntax, t))));
            out
        };
        for ty in &tables.schema().types {
            match ty {
                TypeDef::Struct { name, fields, .. } => {
                    let name = tauto_syntax::type_name(syntax, name);
                    self.syntax_data(&name, true, &[], vec![(name.clone(), record(fields))], span)?;
                }
                TypeDef::Enum { name, ctors } => {
                    let cs = ctors
                        .iter()
                        .map(|c| {
                            (
                                c.name.clone(),
                                match &c.payload {
                                    Payload::Record(fields) => record(fields),
                                    Payload::Single(t) => vec![(None, field_ty(syntax, t))],
                                },
                            )
                        })
                        .collect();
                    self.syntax_data(&tauto_syntax::type_name(syntax, name), false, &[], cs, span)?;
                }
            }
        }
        Ok(())
    }

    fn syntax_data(
        &self,
        name: &str,
        is_struct: bool,
        generics: &[String],
        ctors: Vec<(String, Vec<(Option<String>, Ty)>)>,
        span: Span,
    ) -> R<()> {
        let valid = self
            .data_index
            .get(name)
            .and_then(|i| self.datas.get(*i))
            .is_some_and(|d| {
                d.is_struct == is_struct
                    && d.generics == generics
                    && !d.linear
                    && !d.view
                    && d.ctors.len() == ctors.len()
                    && d.ctors.iter().zip(&ctors).all(|(actual, (ctor, fields))| {
                        // A constructor whose name the prelude also has (`True`,
                        // `Eq`, …) has its full name `m::True`, and one of a type
                        // under the syntax's name has `calc::Atom::Num`; it is
                        // still the terminal written in the grammar. Either may also
                        // sit under the module of the file (`main::calc::Atom::Num`).
                        let short = tauto::surface::qualify::short(&actual.name);
                        (short == ctor || short == format!("{name}::{ctor}"))
                            && actual.fields.len() == fields.len()
                            && actual
                                .fields
                                .iter()
                                .zip(fields)
                                .all(|(a, (n, t))| a.name == *n && a.ty == *t)
                    })
            });
        if valid {
            Ok(())
        } else {
            unsupported(
                msg!(
                    "nir-runtime-syntax-schema-does-not-match",
                    name = name.to_string()
                ),
                span,
            )
        }
    }
}

fn has_token(t: &FieldTy) -> bool {
    match t {
        FieldTy::Token => true,
        FieldTy::List(t) | FieldTy::Opt(t) => has_token(t),
        _ => false,
    }
}

fn field_ty(syntax: &str, t: &FieldTy) -> Ty {
    match t {
        FieldTy::Token => Ty::Data("SynToken".into(), vec![]),
        FieldTy::Named(name) => Ty::Data(tauto_syntax::type_name(syntax, name), vec![]),
        FieldTy::List(t) => Ty::Data("List".into(), vec![field_ty(syntax, t)]),
        FieldTy::Opt(t) => Ty::Option(Box::new(field_ty(syntax, t))),
        FieldTy::Expr => unreachable!("expression holes rejected before schema validation"),
    }
}
