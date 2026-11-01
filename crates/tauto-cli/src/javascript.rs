//! Portable JavaScript modules and target-specific host adapters.
mod specialize;
mod wasm;
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    process::ExitCode,
};
use tauto::manifest::Manifest;
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
        if !pkg.datas.iter().any(|d| &d.name == name && d.host) {
            return Err(crate::i18n::t!("js-type-not-extern", name = name));
        }
    }
    if let Some(d) = pkg
        .datas
        .iter()
        .find(|d| d.host && !types.contains_key(&d.name))
    {
        return Err(crate::i18n::t!("js-type-unbound", name = &d.name));
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
    names: &mut BTreeSet<String>,
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
        bindings.extend(m.javascript.externs.iter());
        bindings.extend(if target == "node" {
            m.javascript.node.iter()
        } else {
            m.javascript.browser.iter()
        });
        asynchronous.extend(m.javascript.asynchronous.iter().cloned());
        sources.extend(m.javascript.sources.iter().cloned());
        for x in &pkg.externs {
            if !bindings.contains_key(&x.name)
                && (m.javascript.node.contains_key(&x.name)
                    || m.javascript.browser.contains_key(&x.name))
            {
                return Err(crate::i18n::t!(
                    "js-extern-unavailable",
                    name = &x.name,
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
        return Err(crate::i18n::t!("js-builtin-browser", name = n));
    }
    if let Some(n) = direct.intersection(&asynchronous).next() {
        return Err(crate::i18n::t!("js-async-direct", name = n));
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
                callback_error = Some(crate::i18n::t!("js-wasm-callback-abandons", name = name));
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
            .ok_or_else(|| crate::i18n::t!("js-extern-binding-form", name = &x.name))?;
        if export.is_empty() {
            return Err(crate::i18n::t!("js-extern-no-export", name = &x.name));
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
            .ok_or_else(|| crate::i18n::t!("js-type-binding-form", name = name))?;
        if export.is_empty() {
            return Err(crate::i18n::t!("js-type-no-export", name = name));
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
    native.fns.clear();
    native.exports.clear();
    native.top = None;
    std::fs::create_dir_all(dir).map_err(|e| e.to_string())?;
    if !native.externs.is_empty() {
        let m = manifest.ok_or_else(|| {
            crate::i18n::t!("js-extern-no-binding", name = &native.externs[0].name)
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
        entry.push_str(&format!("try {{ await run(console.log,externs,{opts}); }} catch(e) {{ if(e.exitCode === undefined || e.denied) console.error(e.message ?? String(e));process.exitCode=e.exitCode ?? 1; }} finally {{ closeServers(); }}"));
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

/// The node entry's `options`: the leading `--allow-*` flags of its arguments
/// are the run's permissions (`docs/design/host-effects.md`), the rest the
/// program's arguments; the standard effects are answered with node's
/// `process`, `fs` and `fetch`.
const NODE_OPTIONS: &str = r#"import { readFileSync, writeFileSync, mkdirSync, readSync, realpathSync, lstatSync, readdirSync, rmSync, mkdtempSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';
import { request as httpRequest } from 'node:http';
import { request as httpsRequest } from 'node:https';
import { isIP, createServer as createNetServer, createConnection } from 'node:net';
import { lookup } from 'node:dns/promises';
const permissions = {};
let rest = process.argv.slice(2);
while (rest.length > 0) {
  const a = rest[0];
  if (a === '--') { rest = rest.slice(1); break; }
  if (a === '--allow-all' || a === '-A') { for (const k of ['read','write','env','net','run','div']) permissions[k] = true; rest = rest.slice(1); continue; }
  if (a === '--allow-div') { permissions.div = true; rest = rest.slice(1); continue; }
  const m = /^--allow-(read|write|env|net|run)(?:=(.*))?$/.exec(a);
  if (!m) { if (a.startsWith('--allow-')) { console.error(`unknown permission \`${a}\`: the permissions are --allow-read, --allow-write, --allow-env, --allow-net, --allow-run, --allow-div and --allow-all`); process.exit(2); } break; }
  if (m[2] === undefined) permissions[m[1]] = true;
  else {
    const items = m[2].split(',').filter(s => s !== '');
    if (items.length === 0) { console.error(`\`${a}\` names nothing; write --allow-${m[1]} for all`); process.exit(2); }
    if (permissions[m[1]] !== true) permissions[m[1]] = [...(permissions[m[1]] ?? []), ...items];
  }
  rest = rest.slice(1);
}
const realPath = p => {
  // As the system resolves it: each part in turn, a link followed before a
  // `..` after it; past what exists only plain names (`docs/design/host-effects.md`).
  const whole = p.startsWith('/') ? p : process.cwd() + '/' + p;
  let at = realpathSync('/'), missing = false;
  for (const part of whole.split('/')) {
    if (part === '' || part === '.') { if (missing && part === '.') return null; continue; }
    if (part === '..') { if (missing) return null; at = dirname(at); continue; }
    const next = join(at, part);
    if (missing) { at = next; continue; }
    try { at = realpathSync(next); } catch (e) {
      try { lstatSync(next); return null; } catch (e2) { missing = true; at = next; }
    }
  }
  return at;
};
let stdinBuffer = Buffer.alloc(0), stdinDone = false;
const readLine = () => {
  for (;;) {
    const i = stdinBuffer.indexOf(10);
    if (i >= 0) { const line = stdinBuffer.subarray(0, i).toString('utf8').replace(/\r$/, ''); stdinBuffer = stdinBuffer.subarray(i + 1); return line; }
    if (stdinDone) { if (stdinBuffer.length === 0) return null; const line = stdinBuffer.toString('utf8'); stdinBuffer = Buffer.alloc(0); return line; }
    const chunk = Buffer.alloc(65536); let n = 0;
    try { n = readSync(0, chunk, 0, chunk.length, null); } catch (e) { if (e.code === 'EAGAIN') continue; if (e.code !== 'EOF') { stdinDone = true; continue; } }
    if (n === 0) stdinDone = true; else stdinBuffer = Buffer.concat([stdinBuffer, chunk.subarray(0, n)]);
  }
};
// `net_resolve`: the addresses the system resolves a host name to.
const resolveHost = host => lookup(host, { all: true, verbatim: true }).then(as => as.map(a => a.address));
// `net_addr`: a request connected to `address` without resolving the URL's host
// again; the Host header and the TLS name stay the URL's host.
const fetchAt = (url, init, address) => new Promise((resolve, reject) => {
  const u = new URL(url), ip = address.replace(/^\[|\]$/g, ''), family = isIP(ip);
  if (!family) { reject(new Error('not an IP address: ' + address)); return; }
  const send = u.protocol === 'https:' ? httpsRequest : httpRequest;
  const req = send(u, { method: init.method, headers: Object.fromEntries(init.headers), lookup: (_h, o, cb) => o && o.all ? cb(null, [{ address: ip, family }]) : cb(null, ip, family) }, res => {
    const chunks = [];
    res.on('data', c => chunks.push(c));
    res.on('end', () => {
      const items = [String(res.statusCode)];
      for (let i = 0; i + 1 < res.rawHeaders.length; i += 2) items.push(res.rawHeaders[i].toLowerCase(), res.rawHeaders[i + 1]);
      resolve([items, new Uint8Array(Buffer.concat(chunks))]);
    });
    res.on('error', reject);
  });
  req.on('error', reject);
  if (init.body !== undefined) req.write(init.body);
  req.end();
});
// Byte streams of `--allow-net` (`tcp_*`): each stream buffers what arrives
// until the program reads it. A deadline is nanoseconds of `monotonic_clock`.
const tcpListeners = new Map(), tcpStreams = new Map();
let nextTcp = 0;
const untilDeadline = d => d === null ? null : Math.max(0, Number(d) / 1e6 - performance.now());
const socketAddress = a => a.unix !== undefined ? { path: a.unix } : { host: a.host.replace(/^\[|\]$/g, ''), port: a.port };
const parseAddress = t => t.startsWith('unix:') ? { unix: t.slice(5) } : (m => m && { host: m[1], port: Number(m[2]) })(/^(.*):([0-9]+)$/.exec(t));
const shown = (socket, side) => {
  const a = side === 'local' ? socket.localAddress : socket.remoteAddress, p = side === 'local' ? socket.localPort : socket.remotePort;
  if (a === undefined) return 'unix:';
  return a.includes(':') ? `[${a}]:${p}` : `${a}:${p}`;
};
const addTcp = (socket, local, peer) => {
  const s = { socket, chunks: [], ended: false, error: null, wake: [] };
  const wake = () => { const w = s.wake; s.wake = []; for (const f of w) f(); };
  socket.on('data', c => { s.chunks.push(c); wake(); });
  socket.on('end', () => { s.ended = true; wake(); });
  socket.on('close', () => { s.ended = true; wake(); });
  socket.on('error', e => { s.error = e; wake(); });
  socket.setNoDelay(true);
  const id = nextTcp++;
  tcpStreams.set(id, s);
  return [String(id), local, peer];
};
// Waits for `ready` to hold, for a wake, or for the deadline: true when ready.
const waitFor = (wakes, ready, deadline) => new Promise(resolve => {
  if (ready()) return resolve(true);
  const ms = untilDeadline(deadline);
  if (ms === 0) return resolve(false);
  let timer = null;
  const on = () => { if (ready()) { if (timer) clearTimeout(timer); resolve(true); } else wakes.push(on); };
  wakes.push(on);
  if (ms !== null) timer = setTimeout(() => resolve(ready()), ms);
});
const tcpListen = address => new Promise((resolve, reject) => {
  const a = parseAddress(address);
  if (!a) return reject(new Error(`cannot listen on ${address}`));
  const l = { queue: [], wake: [], closed: false };
  const server = createNetServer(c => { l.queue.push(c); const w = l.wake; l.wake = []; for (const f of w) f(); });
  l.server = server;
  server.once('error', reject);
  server.listen(socketAddress(a), () => {
    const id = nextTcp++;
    tcpListeners.set(id, l);
    const b = server.address();
    resolve([String(id), typeof b === 'string' ? `unix:${b}` : b.family === 'IPv6' ? `[${b.address}]:${b.port}` : `${b.address}:${b.port}`]);
  });
});
const tcpAccept = async (id, deadline) => {
  const l = tcpListeners.get(id);
  if (!l) throw new Error(`no listener ${id}`);
  if (!await waitFor(l.wake, () => l.queue.length > 0 || l.closed, deadline)) return null;
  if (l.closed) throw new Error('the listener was closed');
  const c = l.queue.shift();
  return addTcp(c, c.localAddress === undefined ? 'unix:' : shown(c, 'local'), shown(c, 'peer'));
};
const tcpConnect = (address, deadline) => new Promise((resolve, reject) => {
  const a = parseAddress(address);
  if (!a) return reject(new Error(`cannot connect to ${address}`));
  const c = createConnection(socketAddress(a));
  const ms = untilDeadline(deadline);
  const timer = ms === null ? null : setTimeout(() => { c.destroy(); resolve(null); }, ms);
  c.once('error', e => { if (timer) clearTimeout(timer); reject(e); });
  c.once('connect', () => {
    if (timer) clearTimeout(timer);
    resolve(addTcp(c, a.unix !== undefined ? 'unix:' : shown(c, 'local'), a.unix !== undefined ? address : shown(c, 'peer')));
  });
});
const tcpStream = id => { const s = tcpStreams.get(id); if (!s) throw new Error(`no stream ${id}`); return s; };
const tcpRead = async (id, max, deadline) => {
  const s = tcpStream(id);
  if (max === 0) return new Uint8Array(0);
  if (!await waitFor(s.wake, () => s.chunks.length > 0 || s.ended || s.error, deadline)) return null;
  if (s.chunks.length === 0) { if (s.error && !s.ended) throw s.error; return new Uint8Array(0); }
  const c = s.chunks[0];
  if (c.length <= max) { s.chunks.shift(); return new Uint8Array(c); }
  s.chunks[0] = c.subarray(max);
  return new Uint8Array(c.subarray(0, max));
};
const tcpWrite = (id, bytes, deadline) => new Promise((resolve, reject) => {
  const s = tcpStream(id);
  const ms = untilDeadline(deadline);
  const timer = ms === null ? null : setTimeout(() => resolve(null), ms);
  s.socket.write(bytes, e => { if (timer) clearTimeout(timer); if (e) reject(e); else resolve(true); });
});
const tcpShutdown = (id, how) => {
  const s = tcpStream(id);
  if (how !== 1) { s.ended = true; s.chunks = []; s.socket.pause(); const w = s.wake; s.wake = []; for (const f of w) f(); }
  if (how !== 0) return new Promise(resolve => s.socket.end(resolve));
};
const tcpClose = id => {
  const s = tcpStreams.get(id);
  if (!s) return;
  tcpStreams.delete(id);
  s.ended = true; s.socket.destroy(); const w = s.wake; s.wake = []; for (const f of w) f();
};
const tcpUnlisten = id => {
  const l = tcpListeners.get(id);
  if (!l) return;
  tcpListeners.delete(id);
  l.closed = true; l.server.close(); const w = l.wake; l.wake = []; for (const f of w) f();
};
const closeServers = () => { for (const id of [...tcpStreams.keys()]) tcpClose(id); for (const id of [...tcpListeners.keys()]) tcpUnlisten(id); };
const options = {args:rest,os_resolve:resolveHost,os_fetch_at:fetchAt,os_tcp_listen:tcpListen,os_tcp_accept:tcpAccept,os_tcp_connect:tcpConnect,os_tcp_read:tcpRead,os_tcp_write:tcpWrite,os_tcp_shutdown:tcpShutdown,os_tcp_close:tcpClose,os_tcp_unlisten:tcpUnlisten,permissions,env:process.env,cwd:process.cwd(),resolvePath:realPath,os_read_line:readLine,os_print:s=>process.stdout.write(s),os_eprint:s=>process.stderr.write(s),os_read_file:p=>readFileSync(p,'utf8'),os_write_file:(p,s)=>writeFileSync(p,s),os_read_bytes:p=>new Uint8Array(readFileSync(p)),os_write_bytes:(p,b)=>writeFileSync(p,b),os_create_dir:p=>{mkdirSync(p,{recursive:true});},os_list_dir:p=>readdirSync(p),os_remove:p=>{if(!lstatSync(p))return;rmSync(p,{recursive:true});},os_temp_dir:()=>mkdtempSync(join(tmpdir(),'tauto-')),os_run:(program,args,dir,env,stdin)=>{const r=spawnSync(program,args,{cwd:dir===''?undefined:dir,env:{...process.env,...Object.fromEntries(env)},input:stdin,maxBuffer:1<<30});if(r.error)throw r.error;return {status:r.status,stdout:new Uint8Array(r.stdout),stderr:r.stderr.toString('utf8')};}};
"#;
