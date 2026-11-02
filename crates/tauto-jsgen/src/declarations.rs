//! Type declarations for the generated module's host boundary.
use std::collections::{BTreeMap, BTreeSet};
use tauto_message::msg;
use tauto_nir::{Package, Pass, Ty};

use crate::{R, cps::Crossing, quote};

/// Describes `run` and its host bindings, without exporting internal NIR functions.
/// Unsupported boundary representations are errors rather than erased types.
pub fn generate_declarations(pkg: &Package) -> R<String> {
    generate_declarations_with(pkg, &crate::Options::default())
}

/// As `generate_declarations`; a host type crosses as the host's own object.
pub fn generate_declarations_with(pkg: &Package, options: &crate::Options) -> R<String> {
    let host = |ty: &Ty| match ty {
        Ty::Ref(inner) | Ty::RefMut(inner) => {
            matches!(&**inner, Ty::Data(n, a) if a.is_empty() && options.host_types.contains(n))
        }
        Ty::Data(n, a) => a.is_empty() && options.host_types.contains(n),
        _ => false,
    };
    let mut g = Declarations {
        pkg,
        pending: BTreeSet::new(),
        emitted: BTreeSet::new(),
    };
    let mut externs = String::from("export interface Externs {\n");
    for ext in &pkg.externs {
        let scope: BTreeMap<_, _> = ext
            .generics
            .iter()
            .enumerate()
            .map(|(i, name)| (name.clone(), format!("T{i}")))
            .collect();
        let params = ext
            .params
            .iter()
            .enumerate()
            .map(|(i, (_, ty, pass))| {
                // The runtime adapts a directly passed function, including a
                // borrowed function, to an ordinary JavaScript callback.
                let t = match ty {
                    _ if host(ty) => "unknown".into(),
                    Ty::Fn(f) => g.callback(f, &scope)?,
                    _ => {
                        let t = g.ty(ty, &scope)?;
                        match pass {
                            Pass::Value => t,
                            Pass::Ref => format!("Borrow<{t}>"),
                            Pass::RefMut => format!("MutableBorrow<{t}>"),
                        }
                    }
                };
                Ok(format!("arg{i}: {t}"))
            })
            .collect::<R<Vec<_>>>()?;
        let ret = if host(&ext.ret) {
            "unknown".into()
        } else {
            g.ty(&ext.ret, &scope)?
        };
        let generics = if scope.is_empty() {
            String::new()
        } else {
            format!(
                "<{}>",
                (0..scope.len())
                    .map(|i| format!("T{i}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        externs.push_str(&format!(
            "  {}: {generics}({}) => {ret} | PromiseLike<{ret}>;\n",
            quote(&ext.name),
            params.join(", ")
        ));
    }
    externs.push_str("}\n");
    let ret = match pkg.top {
        Some(id) => {
            let f = pkg.fns.iter().find(|f| f.id == id).ok_or_else(|| {
                msg!("jsgen-declarations-missing-entry", id = id.to_string()).to_string()
            })?;
            g.ty(&f.ret, &BTreeMap::new())?
        }
        None => "null".into(),
    };
    let mut instance = String::new();
    if !options.exports.is_empty() {
        instance.push_str("export interface Instance {\n");
        for e in crate::cps::export_table(pkg, options)? {
            let scope = BTreeMap::new();
            let mut params = Vec::new();
            for (i, (p, crossing)) in e.f.params.iter().zip(&e.params).enumerate() {
                let t = match (crossing, &p.ty) {
                    (Crossing::Host(_) | Crossing::BorrowedHost(_), _) => "unknown".into(),
                    (Crossing::HostFn, Ty::Fn(f)) => g.host_function(f, &scope)?,
                    (Crossing::HostFn, Ty::Ref(inner)) if let Ty::Fn(f) = &**inner => {
                        g.host_function(f, &scope)?
                    }
                    _ => g.ty(&p.ty, &scope)?,
                };
                params.push(format!("arg{i}: {t}"));
            }
            let ret = match (&e.ret, &e.f.ret) {
                (Crossing::Host(_), _) => "unknown".into(),
                (Crossing::KeptFn, Ty::Fn(f)) => g.callback(f, &scope)?,
                _ => g.ty(&e.f.ret, &scope)?,
            };
            let ret = if e.sync {
                ret
            } else {
                format!("Promise<{ret}>")
            };
            instance.push_str(&format!(
                "  {}: ({}) => {ret};\n",
                quote(e.name),
                params.join(", ")
            ));
        }
        instance.push_str("  dispose(): void;\n}\nexport declare function instantiate(externs?: Externs, options?: RunOptions & { show?: (text: string) => void; release?: Record<string, (value: unknown) => void> }): Instance;\n");
    }
    let mut aliases = String::new();
    while let Some(index) = g.pending.pop_first() {
        if !g.emitted.insert(index) {
            continue;
        }
        let data = &pkg.datas[index];
        if data.ctors.is_empty() {
            return Err(msg!("jsgen-declarations-opaque-data", name = &data.name).to_string());
        }
        let scope: BTreeMap<_, _> = data
            .generics
            .iter()
            .enumerate()
            .map(|(i, name)| (name.clone(), format!("T{i}")))
            .collect();
        let generics = if scope.is_empty() {
            String::new()
        } else {
            format!(
                "<{}>",
                (0..scope.len())
                    .map(|i| format!("T{i}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        let variants = data
            .ctors
            .iter()
            .map(|ctor| {
                let fields = ctor
                    .fields
                    .iter()
                    .map(|f| g.ty(&f.ty, &scope))
                    .collect::<R<Vec<_>>>()?;
                let names = ctor
                    .fields
                    .iter()
                    .map(|f| f.name.as_ref().map(|n| quote(n)).unwrap_or("null".into()))
                    .collect::<Vec<_>>();
                Ok(constructor(
                    &data.name,
                    &ctor.name,
                    &names,
                    &fields,
                    data.is_struct,
                ))
            })
            .collect::<R<Vec<_>>>()?;
        // Names are generated rather than copied into identifiers, so source
        // keywords, qualified names and Unicode cannot collide with helpers.
        aliases.push_str(&format!(
            "export type TautoData{index}{generics} = {};\n",
            variants.join(" | ")
        ));
    }
    let args = if pkg.externs.is_empty() {
        "show?: (text: string) => void, externs?: Externs, options?: RunOptions"
    } else {
        "show: ((text: string) => void) | undefined, externs: Externs, options?: RunOptions"
    };
    Ok(format!(
        "{PRELUDE}\n{aliases}\n{externs}\nexport declare function run({args}): Promise<{ret}>;\n{instance}"
    ))
}

const PRELUDE: &str =
    "// Generated by Tauto. This describes values, not ownership or borrow lifetimes.
export interface Borrow<T> { readonly ref: true; get(): T; }
export interface MutableBorrow<T> extends Borrow<T> { set(value: T): void; }
export interface RunOptions {
  steps?: number;
  args?: string[];
  os_print?: (text: string) => void;
  os_eprint?: (text: string) => void;
  os_read_file?: (path: string) => string | PromiseLike<string>;
  os_write_file?: (path: string, text: string) => void | PromiseLike<void>;
  os_read_bytes?: (path: string) => Uint8Array | PromiseLike<Uint8Array>;
  os_write_bytes?: (path: string, bytes: Uint8Array) => void | PromiseLike<void>;
  /** Makes a directory and its missing parents; one already there is fine. */
  os_create_dir?: (path: string) => void | PromiseLike<void>;
  os_list_dir?: (path: string) => string[] | PromiseLike<string[]>;
  /** Removes a file, or a directory and all it holds. */
  os_remove?: (path: string) => void | PromiseLike<void>;
  os_stat?: (path: string) => { kind: 'file' | 'dir' | 'other'; size: number; modified_ms: number } | null | PromiseLike<{ kind: 'file' | 'dir' | 'other'; size: number; modified_ms: number } | null>;
  os_move_path?: (from: string, to: string) => void | PromiseLike<void>;
  os_copy_file?: (from: string, to: string) => void | PromiseLike<void>;
  os_canonicalize?: (path: string) => string | PromiseLike<string>;
  /** Makes a new empty directory for temporary files; the run may read and write under it. */
  os_temp_dir?: () => string | PromiseLike<string>;
  /** Runs a program to its end: its exit status (`null` when a signal ended it) and output. */
  os_run?: (program: string, args: string[], dir: string, env: [string, string][], stdin: Uint8Array) => { status: number | null; stdout: Uint8Array; stderr: string } | PromiseLike<{ status: number | null; stdout: Uint8Array; stderr: string }>;
  /** Starts a program and goes on while it runs; its number. `env` is [name, value] pairs; `modes` are the input's, output's and error's: 0 a pipe, 1 the run's own. */
  os_child_spawn?: (program: string, args: string[], dir: string, env: [string, string][], stdin: Uint8Array, modes: number[]) => number[] | PromiseLike<number[]>;
  /** Up to `max` bytes of a piped output (`which` 1) or error (2), empty at the end; `null` when the deadline (`monotonic_clock` nanoseconds, or `null`) passed first. */
  os_child_read?: (child: number, which: number, max: number, deadline: bigint | null) => Uint8Array | null | PromiseLike<Uint8Array | null>;
  os_child_write?: (child: number, bytes: Uint8Array) => void | PromiseLike<void>;
  os_child_close_stdin?: (child: number) => void | PromiseLike<void>;
  /** The exit status as `[code]`, `[]` when a signal ended it; `null` when the deadline passed first. */
  os_child_wait?: (child: number, deadline: bigint | null) => number[] | null | PromiseLike<number[] | null>;
  /** Ends a program that still runs and lets go of it. */
  os_child_close?: (child: number) => void | PromiseLike<void>;
  /** A line of standard input without its line break; `null` at its end. */
  os_read_line?: () => string | null;
  /** Up to `max` bytes of standard input as soon as any arrive; none at its end. */
  os_read_stdin?: (max: number) => Uint8Array;
  /** Writes out what `os_print` and `os_eprint` were given. */
  os_flush?: () => void;
  /** What the standard effects may ask of the host; a kind left out is denied. */
  permissions?: { read?: true | string[]; write?: true | string[]; env?: true | string[]; net?: true | string[]; run?: true | string[]; div?: true };
  /** What `env` reads, behind `permissions.env`. */
  env?: Record<string, string | undefined>;
  /** What a relative path is resolved against for `permissions.read` and `permissions.write`. */
  cwd?: string;
  /** Makes a path absolute with its symbolic links followed. */
  resolvePath?: (path: string) => string;
  /** What `net` sends a request with; `globalThis.fetch` by default. */
  fetch?: (url: string, init: { method: string; headers: [string, string][]; body?: Uint8Array; redirect: 'manual' }) => PromiseLike<{ status: number; arrayBuffer(): PromiseLike<ArrayBuffer>; headers: { forEach(f: (value: string, name: string) => void): void } }>;
}
";

struct Declarations<'a> {
    pkg: &'a Package,
    pending: BTreeSet<usize>,
    emitted: BTreeSet<usize>,
}

impl Declarations<'_> {
    fn callback(&mut self, f: &tauto_nir::FnTy, scope: &BTreeMap<String, String>) -> R<String> {
        let params = f
            .params
            .iter()
            .enumerate()
            .map(|(i, t)| Ok(format!("arg{i}: {}", self.ty(t, scope)?)))
            .collect::<R<Vec<_>>>()?;
        let ret = self.ty(&f.ret, scope)?;
        Ok(format!(
            "(({}) => {ret} | Promise<{ret}>)",
            params.join(", ")
        ))
    }

    /// A host function that Nib calls, which may return a Promise.
    fn host_function(
        &mut self,
        f: &tauto_nir::FnTy,
        scope: &BTreeMap<String, String>,
    ) -> R<String> {
        let params = f
            .params
            .iter()
            .enumerate()
            .map(|(i, t)| Ok(format!("arg{i}: {}", self.ty(t, scope)?)))
            .collect::<R<Vec<_>>>()?;
        let ret = self.ty(&f.ret, scope)?;
        Ok(format!(
            "(({}) => {ret} | PromiseLike<{ret}>)",
            params.join(", ")
        ))
    }

    fn ty(&mut self, ty: &Ty, scope: &BTreeMap<String, String>) -> R<String> {
        Ok(match ty {
            Ty::Int(_) => "bigint".into(),
            Ty::Bool => "boolean".into(),
            Ty::Text => "string".into(),
            Ty::Unit => "null".into(),
            Ty::Never => "never".into(),
            Ty::Float | Ty::Float32 => "number".into(),
            Ty::Buf => "{ kind: \"Buf\"; text: string }".into(),
            Ty::Vec(t) | Ty::Array(t) | Ty::Slice(t) => {
                let item = self.ty(t, scope)?;
                let kind = if matches!(ty, Ty::Array(_)) {
                    "Array"
                } else {
                    "Vec"
                };
                format!("{{ kind: {kind:?}; items: Array<{item}> }}")
            }
            Ty::HashMap(k, v) => format!(
                "{{ kind: \"HashMap\"; items: Array<[{}, {}]> }}",
                self.ty(k, scope)?,
                self.ty(v, scope)?
            ),
            Ty::Option(t) => format!(
                "({} | {})",
                constructor("Option", "None", &[], &[], false),
                constructor(
                    "Option",
                    "Some",
                    &["null".into()],
                    &[self.ty(t, scope)?],
                    false
                )
            ),
            Ty::Result(a, b) => format!(
                "({} | {})",
                constructor(
                    "Result",
                    "Ok",
                    &["null".into()],
                    &[self.ty(a, scope)?],
                    false
                ),
                constructor(
                    "Result",
                    "Err",
                    &["null".into()],
                    &[self.ty(b, scope)?],
                    false
                )
            ),
            Ty::Product(ms) => format!(
                "{{ kind: \"Product\"; fields: readonly [{}] }}",
                ms.iter()
                    .map(|(_, m)| self.ty(m, scope))
                    .collect::<R<Vec<_>>>()?
                    .join(", ")
            ),
            Ty::Pair(a, b) => constructor(
                "Pair",
                "Pair",
                &[quote("fst"), quote("snd")],
                &[self.ty(a, scope)?, self.ty(b, scope)?],
                true,
            ),
            Ty::Data(name, args) => {
                let index = self
                    .pkg
                    .datas
                    .iter()
                    .position(|d| d.name == *name)
                    .ok_or_else(|| {
                        msg!("jsgen-declarations-unknown-data", name = name).to_string()
                    })?;
                if self.pkg.datas[index].generics.len() != args.len() {
                    return Err(
                        msg!("jsgen-declarations-type-argument-count", name = name).to_string()
                    );
                }
                self.pending.insert(index);
                let args = args
                    .iter()
                    .map(|t| self.ty(t, scope))
                    .collect::<R<Vec<_>>>()?;
                format!(
                    "TautoData{index}{}",
                    if args.is_empty() {
                        String::new()
                    } else {
                        format!("<{}>", args.join(", "))
                    }
                )
            }
            Ty::Union(id) => {
                let union = self
                    .pkg
                    .unions
                    .iter()
                    .find(|u| u.id == *id)
                    .ok_or_else(|| {
                        msg!("jsgen-declarations-unknown-union", id = id.to_string()).to_string()
                    })?;
                let members = union.members.clone();
                let variants = members
                    .iter()
                    .enumerate()
                    .map(|(i, t)| {
                        Ok(format!(
                            "{{ union: {id}; variant: {i}; value: {} }}",
                            self.ty(t, scope)?
                        ))
                    })
                    .collect::<R<Vec<_>>>()?;
                if variants.is_empty() {
                    "never".into()
                } else {
                    format!("({})", variants.join(" | "))
                }
            }
            Ty::Param(name) => scope.get(name).cloned().ok_or_else(|| {
                msg!("jsgen-declarations-unbound-parameter", name = name).to_string()
            })?,
            Ty::Ref(t) => format!("Borrow<{}>", self.ty(t, scope)?),
            Ty::RefMut(t) => format!("MutableBorrow<{}>", self.ty(t, scope)?),
            Ty::Shown => "{ kind: \"Shown\"; text: string }".into(),
            Ty::Info(_) => "{ kind: \"Info\"; resource: true }".into(),
            Ty::BudgetAnswer(t) => format!(
                "({{ answer: \"value\"; value: {} }} | {{ answer: \"more\"; steps: bigint | null }})",
                self.ty(t, scope)?
            ),
            Ty::Fn(_) => return Err(msg!("jsgen-declarations-function").to_string()),
            Ty::Std(name, _) => {
                return Err(msg!("jsgen-declarations-standard-type", name = name).to_string());
            }
            Ty::SharedVar(true, _) | Ty::SharedVar(false, _) | Ty::Infer => {
                return Err(
                    msg!("jsgen-declarations-internal-type", ty = format!("{ty:?}")).to_string(),
                );
            }
        })
    }
}

fn constructor(
    owner: &str,
    tag: &str,
    names: &[String],
    fields: &[String],
    is_struct: bool,
) -> String {
    format!(
        "{{ tag: {}; names: [{}]; fields: [{}]; struct: {is_struct}; owner: {} }}",
        quote(tag),
        names.join(", "),
        fields.join(", "),
        quote(owner)
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use tauto_nir::{CtorDef, DataDef, ExternDef, FieldDef, Indirect, Kind, Width};

    fn package(params: Vec<Ty>, ret: Ty) -> Package {
        Package {
            externs: vec![ExternDef {
                name: "host.value".into(),
                generics: Vec::new(),
                params: params
                    .into_iter()
                    .enumerate()
                    .map(|(i, ty)| (format!("x{i}"), ty, Pass::Value))
                    .collect(),
                ret,
                span: Default::default(),
            }],
            ..Package::default()
        }
    }

    #[test]
    fn empty_program_has_only_the_actual_runtime_export() {
        let text = generate_declarations(&Package::default()).unwrap();
        assert!(text.contains("run(show?: (text: string) => void, externs?: Externs, options?: RunOptions): Promise<null>"));
        assert!(!text.contains("any"));
    }

    #[test]
    fn host_numbers_constructors_borrows_and_callbacks() {
        let mut pkg = package(
            vec![
                Ty::Int(Width::W64),
                Ty::Pair(Box::new(Ty::Text), Box::new(Ty::Bool)),
                Ty::Fn(Box::new(tauto_nir::FnTy {
                    params: vec![Ty::Text],
                    ret: Ty::Int(Width::U64),
                    kind: Kind::Copy,
                    tier: tauto_nir::Tier::O,
                })),
            ],
            Ty::Option(Box::new(Ty::Unit)),
        );
        pkg.externs[0].params[0].2 = Pass::RefMut;
        pkg.externs[0].params[2].2 = Pass::Ref;
        let text = generate_declarations(&pkg).unwrap();
        assert!(text.contains("arg0: MutableBorrow<bigint>"));
        assert!(text.contains(
            "tag: \"Pair\"; names: [\"fst\", \"snd\"]; fields: [string, boolean]; struct: true"
        ));
        assert!(text.contains("arg2: ((arg0: string) => bigint | Promise<bigint>)"));
        assert!(text.contains("tag: \"Some\"; names: [null]; fields: [null]; struct: false"));
        assert!(text.contains("show: ((text: string) => void) | undefined, externs: Externs"));
    }

    #[test]
    fn generic_recursive_data_and_escaped_binding_names() {
        let mut pkg = package(
            vec![Ty::Data("Tree".into(), vec![Ty::Param("A".into())])],
            Ty::Param("A".into()),
        );
        pkg.externs[0].generics = vec!["A".into()];
        pkg.externs[0].name = "quoted\"binding".into();
        pkg.datas.push(DataDef {
            name: "Tree".into(),
            generics: vec!["Item".into()],
            kind: Kind::Shared,
            is_struct: false,
            clone: true,
            copy: false,
            linear: false,
            view: false,
            host: false,
            ctors: vec![
                CtorDef {
                    name: "Leaf".into(),
                    fields: vec![FieldDef {
                        name: None,
                        ty: Ty::Param("Item".into()),
                        indirect: Indirect::None,
                    }],
                },
                CtorDef {
                    name: "Branch".into(),
                    fields: vec![FieldDef {
                        name: None,
                        ty: Ty::Data("Tree".into(), vec![Ty::Param("Item".into())]),
                        indirect: Indirect::Shared,
                    }],
                },
            ],
        });
        let text = generate_declarations(&pkg).unwrap();
        assert_eq!(text.matches("export type TautoData0<T0>").count(), 1);
        assert!(text.contains("fields: [TautoData0<T0>]"));
        assert!(
            text.contains(
                "\"quoted\\\"binding\": <T0>(arg0: TautoData0<T0>) => T0 | PromiseLike<T0>"
            )
        );
    }

    #[test]
    fn unions_and_borrowed_collections_keep_their_runtime_shapes() {
        let mut pkg = package(vec![Ty::Union(7)], Ty::Vec(Box::new(Ty::Text)));
        pkg.externs[0].params.push((
            "items".into(),
            Ty::Slice(Box::new(Ty::Int(Width::U8))),
            Pass::Ref,
        ));
        pkg.unions.push(tauto_nir::UnionDef {
            id: 7,
            members: vec![Ty::Text, Ty::Int(Width::W64)],
            kind: Kind::Shared,
        });
        let text = generate_declarations(&pkg).unwrap();
        assert!(text.contains(
            "{ union: 7; variant: 0; value: string } | { union: 7; variant: 1; value: bigint }"
        ));
        assert!(text.contains("arg1: Borrow<{ kind: \"Vec\"; items: Array<bigint> }>"));
        assert!(text.contains("=> { kind: \"Vec\"; items: Array<string> } | PromiseLike<"));
    }

    #[test]
    fn unsupported_boundary_is_not_erased() {
        tauto_messages::install();
        for ty in [
            Ty::Infer,
            Ty::Std("OpaqueHost".into(), vec![]),
            Ty::Fn(Box::new(tauto_nir::FnTy {
                params: vec![],
                ret: Ty::Unit,
                kind: Kind::Copy,
                tier: tauto_nir::Tier::S,
            })),
        ] {
            let error = generate_declarations(&package(vec![], ty)).unwrap_err();
            assert!(error.starts_with("javascript declarations:"), "{error}");
        }
        let error =
            generate_declarations(&package(vec![Ty::Data("Missing".into(), vec![])], Ty::Unit))
                .unwrap_err();
        assert!(error.contains("unknown data type Missing"));
    }
}
