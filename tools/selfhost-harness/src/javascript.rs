//! The same component differential drivers on a JavaScript executable.
use super::{RunOutput, root};
use std::collections::BTreeMap;
use std::process::Command;
use std::sync::{Mutex, OnceLock};

fn module(name: &str) -> Result<String, String> {
    static MODULES: OnceLock<Mutex<BTreeMap<String, Result<String, String>>>> = OnceLock::new();
    let mut modules = MODULES.get_or_init(Default::default).lock().unwrap();
    modules
        .entry(name.to_string())
        .or_insert_with(|| {
            let loaded = tauto::program::load_tote_for_build(&root().join("totes").join(name))?;
            let package = tauto_nir::compile_loaded_with_observer(&loaded, false, true, |_| {})
                .map_err(|e| format!("selfhost JavaScript compilation: {e}"))?;
            if !package.externs.is_empty() {
                return Err("selfhost JavaScript requires explicit extern bindings".into());
            }
            tauto_jsgen::generate(&package)
                .map_err(|e| format!("selfhost JavaScript generation: {e}"))
        })
        .clone()
}

pub fn run(name: &str, args: &[String], steps: u64) -> RunOutput {
    let failure = |error| RunOutput {
        stdout: String::new(),
        stderr: String::new(),
        exit: None,
        error: Some(error),
    };
    if steps > 9_007_199_254_740_991 {
        return failure(
            "JavaScript selfhost step limit exceeds exact integer representation".into(),
        );
    }
    // Compiler traversals need the same generous stack as the evaluator route.
    let owned_name = name.to_string();
    let compiled = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || module(&owned_name))
        .map_err(|e| e.to_string())
        .and_then(|thread| {
            thread
                .join()
                .map_err(|_| "selfhost JavaScript compilation panicked".to_string())
        })
        .and_then(|result| result);
    let module = match compiled {
        Ok(module) => module,
        Err(e) => return failure(e),
    };
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = super::materialize(&format!("javascript-{name}-{id}"), &[]);
    let script = dir.dir.join("main.mjs");
    let args = serde_json::to_string(args).unwrap();
    let source = format!(
        r#"import {{readFileSync,writeFileSync,mkdirSync}} from 'node:fs';
{module}
try {{ await run(console.log, {{}}, {{
  args:{args}, steps:{steps}, permissions:{{read:true, write:true}},
  os_print:text=>process.stdout.write(text), os_eprint:text=>process.stderr.write(text),
  os_read_file:path=>readFileSync(path,'utf8'), os_write_file:(path,text)=>writeFileSync(path,text), os_read_bytes:path=>new Uint8Array(readFileSync(path)), os_write_bytes:(path,bytes)=>writeFileSync(path,bytes), os_create_dir:path=>{{mkdirSync(path,{{recursive:true}});}}
}}); }} catch(error) {{
  if(error.exitCode!==undefined) process.exitCode=error.exitCode;
  else {{console.error(error.message);process.exitCode=1;}}
}}
"#
    );
    if let Err(e) = std::fs::write(&script, source) {
        return failure(e.to_string());
    }
    let stdout = dir.dir.join("stdout");
    let stderr = dir.dir.join("stderr");
    let mut child = match Command::new("node")
        .arg(&script)
        .stdout(std::fs::File::create(&stdout).unwrap())
        .stderr(std::fs::File::create(&stderr).unwrap())
        .spawn()
    {
        Ok(child) => child,
        Err(e) => return failure(format!("cannot run JavaScript selfhost: {e}")),
    };
    let begin = std::time::Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {}
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                return failure(e.to_string());
            }
        }
        if begin.elapsed() > std::time::Duration::from_secs(120) {
            let _ = child.kill();
            let _ = child.wait();
            return failure("JavaScript selfhost exceeded the 120 second safety limit".into());
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    };
    RunOutput {
        stdout: std::fs::read_to_string(stdout).unwrap(),
        stderr: std::fs::read_to_string(stderr).unwrap(),
        exit: status.code(),
        error: None,
    }
}
