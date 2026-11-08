//! Portable JavaScript modules and target-specific host adapters.
mod specialize;
mod wasm;
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    process::ExitCode,
};
use tauto::manifest::Manifest;
use tauto_jsgen::NODE_OPTIONS;
use tauto_nir::{Callee, Expr, ExprKind, Package};
fn quote(s: &str) -> String {
    serde_json::to_string(s).unwrap()
}

pub fn execute(
    root: &Path,
    pkg: &Package,
    manifest: Option<&Manifest>,
    command: &str,
    out_dir: Option<String>,
    name: &str,
    target: &str,
    declarations: bool,
    timings: &mut super::timings::Timings,
    run_args: &[String],
) -> ExitCode {
    let dir = out_dir
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join("javascript").join(target).join(name));
    if let Err(e) = build(pkg, manifest, &dir, target, declarations, timings) {
        eprintln!("{e}");
        return ExitCode::FAILURE;
    }
    timings.phase("finish");
    let main = dir.join("main.mjs");
    if command == "build" {
        println!("{}", main.display());
        return ExitCode::SUCCESS;
    }
    match std::process::Command::new("node")
        .arg(&main)
        .args(run_args)
        .status()
    {
        Ok(s) => ExitCode::from(s.code().unwrap_or(1) as u8),
        Err(e) => {
            eprintln!("{}", crate::i18n::t!("js-node-failed", e = e.to_string()));
            ExitCode::FAILURE
        }
    }
}

/// The host types are the extern types (`extern { type T }`), each bound in
/// `javascript.types`.
fn check_host_types(
    pkg: &Package,
    types: &BTreeMap<String, tauto::manifest::Entry>,
) -> Result<(), String> {
    for name in types.keys() {
        if !pkg.datas.iter().any(|d| d.name.as_str() == name && d.host) {
            return Err(crate::i18n::t!(
                "js-type-not-extern",
                name = name.to_string()
            ));
        }
    }
    if let Some(d) = pkg
        .datas
        .iter()
        .find(|d| d.host && !types.contains_key(d.name.as_str()))
    {
        return Err(crate::i18n::t!(
            "js-type-unbound",
            name = d.name.to_string()
        ));
    }
    Ok(())
}

fn visit(e: &Expr, f: &mut impl FnMut(&Expr)) {
    e.walk(&mut |node| {
        f(node);
        if let ExprKind::Handle(h) = &node.kind {
            for arm in &h.susp {
                if let Some(g) = &arm.guard {
                    visit(g, f);
                }
                visit(&arm.body, f);
            }
        }
    });
}
fn direct_externs(
    pkg: &Package,
    e: &Expr,
    seen: &mut BTreeSet<usize>,
    names: &mut BTreeSet<tauto_nir::Name>,
) {
    visit(e, &mut |node| match &node.kind {
        ExprKind::Call(c) => match &c.callee {
            Callee::Extern(n) => {
                names.insert(n.clone());
            }
            Callee::Inst(i) => {
                if seen.insert(*i) {
                    direct_externs(pkg, &pkg.fns[*i].body, seen, names);
                }
            }
            _ => {}
        },
        ExprKind::FnValue { inst, .. } => {
            if seen.insert(*inst) {
                direct_externs(pkg, &pkg.fns[*inst].body, seen, names);
            }
        }
        _ => {}
    });
}
fn build(
    pkg: &Package,
    manifest: Option<&Manifest>,
    dir: &Path,
    target: &str,
    declarations: bool,
    timings: &mut super::timings::Timings,
) -> Result<(), String> {
    timings.phase("codegen_write");
    let mut bindings = BTreeMap::new();
    let mut asynchronous = BTreeSet::new();
    let mut sources = BTreeSet::new();
    if let Some(m) = manifest {
        let target_bindings = if target == "node" {
            &m.javascript.node
        } else {
            &m.javascript.browser
        };
        for declaration in &pkg.externs {
            if let Some(binding) = target_bindings
                .get(declaration.name.as_str())
                .or_else(|| m.javascript.externs.get(declaration.name.as_str()))
            {
                bindings.insert(declaration.name.clone(), binding);
            }
            if m.javascript
                .asynchronous
                .contains(&declaration.name.to_string())
            {
                asynchronous.insert(declaration.name.clone());
            }
        }
        sources.extend(m.javascript.sources.iter().cloned());
        for x in &pkg.externs {
            if !bindings.contains_key(&x.name)
                && (m.javascript.node.contains_key(x.name.as_str())
                    || m.javascript.browser.contains_key(x.name.as_str()))
            {
                return Err(crate::i18n::t!(
                    "js-extern-unavailable",
                    name = x.name.to_string(),
                    target = target
                ));
            }
        }
    }
    let mut direct = BTreeSet::new();
    let mut unavailable = None;
    for f in &pkg.fns {
        visit(&f.body, &mut |node| {
            if let ExprKind::Handle(h) = &node.kind {
                for arm in &h.direct {
                    direct_externs(pkg, &arm.body, &mut BTreeSet::new(), &mut direct);
                }
            }
            if target == "browser"
                && let ExprKind::Call(c) = &node.kind
                && let Callee::Builtin(n) = &c.callee
                && n.starts_with("Os::")
            {
                unavailable = Some(n.clone());
            }
        });
    }
    if let Some(n) = unavailable {
        return Err(crate::i18n::t!("js-builtin-browser", name = n.to_string()));
    }
    if let Some(n) = direct.intersection(&asynchronous).next() {
        return Err(crate::i18n::t!("js-async-direct", name = n.to_string()));
    }
    let native_names = pkg
        .externs
        .iter()
        .filter(|x| !bindings.contains_key(&x.name))
        .map(|x| x.name.clone())
        .collect();
    let (specialized, origins) = specialize::package(pkg, &native_names)?;
    let pkg = &specialized;
    let mut callback_error = None;
    for f in &pkg.fns {
        visit(&f.body, &mut |node| {
            if let ExprKind::Call(c) = &node.kind
                && let Callee::Extern(name) = &c.callee
                && !bindings.contains_key(name)
                && c.args.iter().any(|arg| {
                    let ty = match &arg.ty {
                        tauto_nir::Ty::Ref(t) | tauto_nir::Ty::RefMut(t) => t.as_ref(),
                        t => t,
                    };
                    matches!(ty, tauto_nir::Ty::Fn(_)) && specialize::abandoning_callback(pkg, arg)
                })
            {
                callback_error = Some(crate::i18n::t!(
                    "js-wasm-callback-abandons",
                    name = name.to_string()
                ));
            }
        });
    }
    if let Some(error) = callback_error {
        return Err(error);
    }
    let host_types = manifest
        .map(|m| m.javascript.types.clone())
        .unwrap_or_default();
    check_host_types(pkg, &host_types)?;
    let options = tauto_jsgen::Options {
        host_types: host_types.keys().cloned().collect(),
        exports: manifest
            .map(|m| m.javascript.exports.clone())
            .unwrap_or_default(),
        retain: manifest
            .map(|m| m.javascript.retain.iter().cloned().collect())
            .unwrap_or_default(),
        chunks: manifest
            .map(|m| m.javascript.chunks.clone())
            .unwrap_or_default(),
    };
    let modules = tauto_jsgen::generate_modules(pkg, &options)?;
    // Validate the declaration boundary before creating any output files.
    let types = declarations
        .then(|| tauto_jsgen::generate_declarations_with(pkg, &options))
        .transpose()?;
    let mut entry = String::from("import { run } from './program.mjs';\nconst externs = {};\n");
    for (i, x) in pkg.externs.iter().enumerate() {
        let Some(binding) = bindings.get(&x.name) else {
            continue;
        };
        let (module, export) = binding
            .value
            .rsplit_once('#')
            .ok_or_else(|| crate::i18n::t!("js-extern-binding-form", name = x.name.to_string()))?;
        if export.is_empty() {
            return Err(crate::i18n::t!(
                "js-extern-no-export",
                name = x.name.to_string()
            ));
        }
        valid_relative(module)?;
        sources.insert(module.to_owned());
        entry.push_str(&format!("import * as host{i} from {};\nconst binding{i} = host{i}[{}];\nif (typeof binding{i} !== 'function') throw new Error({});\n",quote(&format!("./host/{module}")),quote(export),quote(&format!("missing javascript export {export} for {}",x.name))));
        let check = if asynchronous.contains(&x.name) {
            String::new()
        } else {
            format!(
                "if (result && typeof result.then === 'function') {{ Promise.resolve(result).catch(()=>{{}});throw new Error({}); }}",
                quote(&format!(
                    "extern {} returned a Promise but is not listed in javascript.async",
                    x.name
                ))
            )
        };
        entry.push_str(&format!("externs[{}] = (...args) => {{ const result = binding{i}(...args); {check} return result; }};\n",quote(&x.name)));
    }
    for (i, (name, binding)) in host_types.iter().enumerate() {
        let (module, export) = binding
            .value
            .rsplit_once('#')
            .ok_or_else(|| crate::i18n::t!("js-type-binding-form", name = name.to_string()))?;
        if export.is_empty() {
            return Err(crate::i18n::t!(
                "js-type-no-export",
                name = name.to_string()
            ));
        }
        valid_relative(module)?;
        sources.insert(module.to_owned());
        entry.push_str(&format!(
            "import * as release{i} from {};
if (typeof release{i}[{}] !== 'function') throw new Error({});
externs[{}] = release{i}[{}];
",
            quote(&format!("./host/{module}")),
            quote(export),
            quote(&format!(
                "missing javascript export {export} for type {name}"
            )),
            quote(&format!("@release:{name}")),
            quote(export)
        ));
    }
    let mut native = pkg.clone();
    native.externs.retain(|x| !bindings.contains_key(&x.name));
    // An extern type bound in `javascript.types` is a JavaScript value; the
    // Wasm build is for the Rust externs, so it does not name the type.
    native
        .datas
        .retain(|d| !(d.host && host_types.contains_key(d.name.as_str())));
    native.fns.clear();
    native.exports.clear();
    native.top = None;
    std::fs::create_dir_all(dir).map_err(|e| e.to_string())?;
    if !native.externs.is_empty() {
        let m = manifest.ok_or_else(|| {
            crate::i18n::t!(
                "js-extern-no-binding",
                name = native.externs[0].name.to_string()
            )
        })?;
        wasm::build(&native, m, dir, &origins, timings)?;
        if target == "node" {
            entry.push_str("import { readFile } from 'node:fs/promises';\nconst wasmBytes = await readFile(new URL('./externs.wasm',import.meta.url));\n");
        } else {
            entry.push_str("const wasmResponse = await fetch(new URL('./externs.wasm',import.meta.url));\nif (!wasmResponse.ok) throw new Error('cannot load externs.wasm: '+wasmResponse.status);\nconst wasmBytes = await wasmResponse.arrayBuffer();\n");
        }
        entry.push_str("import { bindWasm } from './wasm.mjs';\nconst wasm = await bindWasm(wasmBytes);\nObject.assign(externs,wasm.externs);\n");
    }
    if let Some(m) = manifest {
        let base = m.file.parent().unwrap_or(Path::new("."));
        for source in sources {
            valid_relative(&source)?;
            copy_source(base, &source, &dir.join("host"))?;
        }
    }
    let opts = if target == "node" {
        entry.push_str(NODE_OPTIONS);
        "options"
    } else {
        "{}"
    };
    if target == "node" {
        entry.push_str(&format!("try {{ await runUntilIdle(run(console.log,externs,{opts})); }} catch(e) {{ if(e.exitCode === undefined || e.denied) console.error(e.message ?? String(e));process.exitCode=e.exitCode ?? 1; }} finally {{ closeServers(); }}"));
    } else {
        entry.push_str(&format!(
            "try {{ await run(console.log,externs,{opts}); }} finally {{ {} }}",
            if native.externs.is_empty() {
                ""
            } else {
                "wasm.dispose();"
            }
        ));
    }
    if !native.externs.is_empty() {
        entry.push_str("\nwasm.dispose();\n");
    }
    remove_chunks(dir)?;
    std::fs::write(dir.join("program.mjs"), modules.program).map_err(|e| e.to_string())?;
    for (file, text) in modules.chunks {
        std::fs::write(dir.join(file), text).map_err(|e| e.to_string())?;
    }
    std::fs::write(dir.join("main.mjs"), entry).map_err(|e| e.to_string())?;
    if let Some(types) = types {
        std::fs::write(dir.join("program.d.mts"), types).map_err(|e| e.to_string())?;
        std::fs::write(dir.join("main.d.mts"), "export {};\n").map_err(|e| e.to_string())?;
        if !native.externs.is_empty() {
            let keys = native
                .externs
                .iter()
                .map(|x| quote(&x.name))
                .collect::<Vec<_>>()
                .join(" | ");
            let wasm_types = format!(
                "import type {{ Externs }} from './program.mjs';\nexport interface WasmBindings {{\n  externs: Pick<Externs, {keys}>;\n  release(value: unknown): void;\n  dispose(): void;\n}}\nexport declare function bindWasm(bytes: ArrayBuffer | ArrayBufferView): Promise<WasmBindings>;\n"
            );
            std::fs::write(dir.join("wasm.d.mts"), wasm_types).map_err(|e| e.to_string())?;
        } else {
            remove_declaration(&dir.join("wasm.d.mts"))?;
        }
    } else {
        for name in ["program.d.mts", "main.d.mts", "wasm.d.mts"] {
            remove_declaration(&dir.join(name))?;
        }
    }
    Ok(())
}
/// The chunks of an earlier build, which the program may no longer have.
fn remove_chunks(dir: &Path) -> Result<(), String> {
    for e in std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))? {
        let path = e.map_err(|e| e.to_string())?.path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if name.starts_with("chunk-") && name.ends_with(".mjs") {
            std::fs::remove_file(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        }
    }
    Ok(())
}
fn remove_declaration(path: &Path) -> Result<(), String> {
    match std::fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!("{}: {error}", path.display())),
    }
}
fn valid_relative(path: &str) -> Result<(), String> {
    if path.is_empty()
        || Path::new(path).components().any(|c| {
            !matches!(
                c,
                std::path::Component::Normal(_) | std::path::Component::CurDir
            )
        })
    {
        return Err(crate::i18n::t!("js-source-outside", path = path));
    }
    Ok(())
}
fn copy_source(base: &Path, rel: &str, out: &Path) -> Result<(), String> {
    fn copy(base: &Path, path: &Path, out: &Path) -> Result<(), String> {
        let canonical = path
            .canonicalize()
            .map_err(|e| format!("{}: {e}", path.display()))?;
        if !canonical.starts_with(base) {
            return Err(crate::i18n::t!(
                "js-source-leaves",
                path = path.display().to_string()
            ));
        }
        if std::fs::symlink_metadata(path)
            .map_err(|e| e.to_string())?
            .file_type()
            .is_symlink()
        {
            return Err(crate::i18n::t!(
                "js-source-symlink",
                path = path.display().to_string()
            ));
        }
        if path.is_dir() {
            if out.starts_with(&canonical) {
                return Err(crate::i18n::t!(
                    "js-source-contains-output",
                    path = path.display().to_string()
                ));
            }
            std::fs::create_dir_all(out).map_err(|e| e.to_string())?;
            for e in std::fs::read_dir(path).map_err(|e| e.to_string())? {
                let e = e.map_err(|e| e.to_string())?;
                copy(base, &e.path(), &out.join(e.file_name()))?;
            }
        } else {
            if let Some(p) = out.parent() {
                std::fs::create_dir_all(p).map_err(|e| e.to_string())?;
            }
            std::fs::copy(path, out).map_err(|e| e.to_string())?;
        }
        Ok(())
    }
    let root = base.canonicalize().map_err(|e| e.to_string())?;
    let out = if out.is_absolute() {
        out.to_owned()
    } else {
        std::env::current_dir()
            .map_err(|e| e.to_string())?
            .join(out)
    };
    copy(&root, &base.join(rel), &out.join(rel))
}
