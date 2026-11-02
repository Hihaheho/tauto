//! The JavaScript backend: generate a module, check its syntax with Node,
//! run it, and compare.

use std::{
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant},
};
use tauto_test_suite::{RustCase, coverage::status};

/// A rejection that a case declares, or `None` when nothing declares it.
fn declared_failure(case: &RustCase, stage: &str, message: &str) -> Option<String> {
    match case.check_limitation("javascript", stage, message) {
        Ok(true) => return Some(status("todo", &format!("declared {stage}: {message}"))),
        Err(e) => return Some(status("fail", &e)),
        Ok(false) => {}
    }
    match case.check_compile_error("javascript", stage, message) {
        Ok(true) => Some(checked(case, "rejection checked")),
        Err(e) => Some(status("fail", &e)),
        Ok(false) => None,
    }
}

fn checked(case: &RustCase, what: &str) -> String {
    let gaps = case.assertion_gaps();
    if gaps.is_empty() {
        "pass".into()
    } else {
        status("partial", &format!("{what}; {}", gaps.join("; ")))
    }
}

fn run_case(case: &RustCase, i: usize, dir: &Path) -> String {
    let pkg = match case.compile("javascript") {
        Ok(p) => p,
        Err(error) => {
            let (stage, message) = match error {
                tauto_nir::CompileError::Front(m) => ("front", m),
                tauto_nir::CompileError::Build(m) => ("build", m),
                tauto_nir::CompileError::Unsupported(u) => ("unsupported", u.what),
            };
            if let Some(s) = declared_failure(case, stage, &message) {
                return s;
            }
            if stage == "unsupported" && !case.explicit_backend("javascript") {
                return status("todo", &format!("uncovered compiler capability: {message}"));
            }
            return status("fail", &format!("unexpected {stage}: {message}"));
        }
    };
    let probes = !pkg.externs.is_empty() && pkg.externs.iter().all(|e| e.name == "Probe.new");
    if !pkg.externs.is_empty() && !probes {
        if case.explicit_backend("javascript") {
            return status("fail", "unbound host externs require a host fixture");
        }
        return status("todo", "host extern bindings");
    }
    let js = match tauto_jsgen::generate(&pkg) {
        Ok(js) => js,
        Err(e) => {
            return declared_failure(case, "generate", &e)
                .unwrap_or_else(|| status("fail", &format!("generate: {e}")));
        }
    };
    let module = dir.join(format!("{i}.mjs"));
    let show_file = dir.join(format!("{i}-shows.json"));
    let show_path = serde_json::to_string(&show_file.to_string_lossy()).unwrap();
    let args = serde_json::to_string(&case.args).unwrap();
    let permissions = js_permissions(&case.permissions);
    let probe_file = dir.join(format!("{i}-probes.json"));
    let probe_path = serde_json::to_string(&probe_file.to_string_lossy()).unwrap();
    // The standard probe: a host resource that logs its name when its
    // last owner releases it.
    let host = if probes {
        "{'Probe.new'(name){name=name.get();let owners=1;return {resource:true,retain(){owners++;},release(){if(--owners===0)dropped.push(name);}};}}"
    } else {
        "{}"
    };
    std::fs::write(&module, format!("import {{writeFileSync}} from 'node:fs';\n{js}\nconst shows=[]; const dropped=[]; try {{await run(text => shows.push(text), {host}, {{args:{args}, permissions:{permissions}, env:process.env, os_print:text => process.stdout.write(text), os_eprint:text => process.stderr.write(text)}});}} catch(e) {{if(e.exitCode!==undefined){{if(e.denied)console.error(e.message);process.exitCode=e.exitCode;}}else{{console.error(e.message);process.exitCode=1;}}}} finally {{writeFileSync({show_path}, JSON.stringify(shows)); writeFileSync({probe_path}, JSON.stringify(dropped));}}\n")).unwrap();
    let syntax = Command::new("node")
        .arg("--check")
        .arg(&module)
        .output()
        .unwrap();
    if !syntax.status.success() {
        let message = String::from_utf8_lossy(&syntax.stderr);
        return declared_failure(case, "build", &message).unwrap_or_else(|| {
            status(
                "fail",
                &format!("generated JavaScript does not parse: {message}"),
            )
        });
    }
    if let Err(e) = case.check_compiled("javascript") {
        return status("fail", &e);
    }
    if !case.expects_runtime() {
        return checked(case, "compile checked");
    }
    let out_file = dir.join("out");
    let err_file = dir.join("err");
    let mut child = Command::new("node")
        .arg(&module)
        .stdout(std::fs::File::create(&out_file).unwrap())
        .stderr(std::fs::File::create(&err_file).unwrap())
        .spawn()
        .unwrap();
    let begin = Instant::now();
    let exit = loop {
        if let Some(s) = child.try_wait().unwrap() {
            break Some(s);
        }
        if begin.elapsed() > Duration::from_secs(60) {
            child.kill().unwrap();
            child.wait().unwrap();
            break None;
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let out = std::fs::read_to_string(out_file).unwrap();
    let err = std::fs::read_to_string(err_file).unwrap();
    let shows = std::fs::read_to_string(&show_file)
        .map_err(|e| format!("missing show capture: {e}"))
        .and_then(|text| {
            serde_json::from_str::<Vec<String>>(&text)
                .map_err(|e| format!("invalid show capture: {e}"))
        });
    if case.backend_known_failure.contains_key("javascript") {
        if exit.is_some_and(|s| !s.success()) {
            return match case.check_limitation("javascript", "runtime", &err) {
                Ok(true) => status("todo", &format!("declared runtime: {err}")),
                Err(e) => status("fail", &e),
                Ok(false) => unreachable!(),
            };
        }
        return status(
            "fail",
            "known failure succeeded or timed out; expected precise runtime failure",
        );
    }
    if let Some(want) = &case.probe_drops {
        let got = std::fs::read_to_string(&probe_file)
            .ok()
            .and_then(|t| serde_json::from_str::<Vec<String>>(&t).ok());
        if got.as_ref() != Some(want) {
            return status(
                "fail",
                &format!("probe_drops: expected {want:?}, got {got:?}"),
            );
        }
    }
    let result = exit
        .ok_or_else(|| "runtime safety limit exceeded".to_string())
        .and_then(|s| {
            shows.and_then(|shows| case.check_output("javascript", &shows, &out, &err, s.code()))
        });
    match result {
        Ok(()) => checked(case, "output checked"),
        Err(e) => status("fail", &e),
    }
}

/// Each worker has a directory of its own: `out` and `err` are shared by the
/// cases of one directory.
pub fn runner(worker: usize) -> impl FnMut(usize, &RustCase) -> String {
    let dir: PathBuf =
        std::env::temp_dir().join(format!("tauto-js-corpus-{}-{worker}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let scratch = Scratch(dir.clone());
    move |i, case| {
        let _keep = &scratch;
        run_case(case, i, &dir)
    }
}

struct Scratch(PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// The host's permission flags as the generated module's
/// `options.permissions`: each kind `true` (all) or the list it covers.
fn js_permissions(flags: &[String]) -> String {
    let mut kinds = serde_json::Map::new();
    for flag in flags {
        if flag == "--allow-all" || flag == "-A" {
            for k in ["read", "write", "env", "net"] {
                kinds.insert(k.into(), serde_json::Value::Bool(true));
            }
            continue;
        }
        let Some(rest) = flag.strip_prefix("--allow-") else {
            continue;
        };
        match rest.split_once('=') {
            None => {
                kinds.insert(rest.into(), serde_json::Value::Bool(true));
            }
            Some((k, list)) => {
                let entry = kinds
                    .entry(k.to_string())
                    .or_insert_with(|| serde_json::Value::Array(Vec::new()));
                if let serde_json::Value::Array(items) = entry {
                    items.extend(
                        list.split(',')
                            .filter(|s| !s.is_empty())
                            .map(|s| serde_json::Value::String(s.into())),
                    );
                }
            }
        }
    }
    serde_json::Value::Object(kinds).to_string()
}
