//! A tote on the machine: compiled when first called, compiled again by
//! [`Tote::reload`] after its files change.

use std::cell::RefCell;
use std::path::{Path, PathBuf};

use tauto_nir::{CompileError, Package};
use tauto_rt::permissions::Permissions;
use tauto_vm::{Program, Value};

use crate::convert::Cx;

/// The extern functions of the tote, which the facade binds: extern
/// function `index` of the package called with `args`.
pub type Externs = fn(index: u32, args: Vec<Value>, cx: &Cx) -> Result<Value, String>;

/// The tote of a facade `tauto-build` wrote. The facade keeps one for each
/// thread (the machine's values are not shared between threads), so a
/// reload is the calling thread's.
pub struct Tote {
    manifest: &'static str,
    externs: Externs,
    fingerprint: u64,
    image: Option<&'static [u8]>,
    inputs: &'static [(&'static str, u64)],
    loaded: RefCell<Option<Loaded>>,
}

struct Loaded {
    program: Program,
    exports: Vec<(String, u32)>,
    cx: Cx,
    /// The tote's files and the hashes of what they held when the running
    /// code was compiled (`tauto_nir::content_hash`, 0 for a missing file).
    inputs: Vec<(PathBuf, u64)>,
}

impl Tote {
    /// `manifest` is the path of the tote's `Tauto.eure`; `fingerprint`,
    /// [`interface_fingerprint`](tauto_nir::interface_fingerprint) of the
    /// package the facade was written from. `image` is the program the
    /// build compiled (`tauto_vm::image::Image::to_bytes`), which the first
    /// call reads instead of compiling the tote; without one, the first call
    /// compiles it. `inputs` are the tote's files with the hashes of what
    /// they held when the build read them: a reload compiles the tote again
    /// when one differs.
    pub const fn new(
        manifest: &'static str,
        externs: Externs,
        fingerprint: u64,
        image: Option<&'static [u8]>,
        inputs: &'static [(&'static str, u64)],
    ) -> Tote {
        Tote {
            manifest,
            externs,
            fingerprint,
            image,
            inputs,
            loaded: RefCell::new(None),
        }
    }

    /// Calls the exported function `name`; `args` makes its arguments and
    /// `answer` reads what it answers. An error of the run panics, as it
    /// does in the Rust backend's code.
    pub fn call<R>(
        &self,
        name: &str,
        args: impl FnOnce(&Cx) -> Vec<Value>,
        answer: impl FnOnce(Value, &Cx) -> Result<R, String>,
    ) -> R {
        if self.loaded.borrow().is_none() {
            let loaded = match self.image {
                Some(bytes) => self.read_image(bytes),
                None => self.load(),
            };
            let loaded = loaded.unwrap_or_else(|e| panic!("{e}"));
            *self.loaded.borrow_mut() = Some(loaded);
        }
        let guard = self.loaded.borrow();
        let loaded = guard.as_ref().expect("loaded");
        let inst = loaded
            .exports
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, inst)| *inst)
            .unwrap_or_else(|| panic!("tauto-embed: the tote exports no {name}"));
        let args = args(&loaded.cx);
        let mut host = Embedded {
            process: tauto_vm::Process {
                args: Vec::new(),
                permissions: Permissions::default(),
            },
            externs: self.externs,
            cx: &loaded.cx,
        };
        match tauto_vm::call(&loaded.program, &mut host, inst, args, u64::MAX) {
            Ok(v) => answer(v, &loaded.cx).unwrap_or_else(|e| {
                panic!("tauto-embed: {name} answered a value of another type: {e}")
            }),
            Err(tauto_vm::End::Exit(code)) => std::process::exit(code),
            Err(tauto_vm::End::Error(message)) => panic!("{message}"),
            Err(tauto_vm::End::Done) => unreachable!(),
        }
    }

    /// Compiles the tote again when one of its files changed since it was
    /// compiled: `Ok(true)` when the new code runs from the next call,
    /// `Ok(false)` when nothing changed or it was never called. When the new
    /// code does not compile, or its exported functions or data types are
    /// not the ones the facade was built with (which only a rebuild
    /// applies), the old code keeps running and the error says why.
    pub fn reload(&self) -> Result<bool, String> {
        let changed = match &*self.loaded.borrow() {
            None => return Ok(false),
            Some(l) => l.inputs.iter().any(|(p, h)| hash(p) != *h),
        };
        if !changed {
            return Ok(false);
        }
        let loaded = self.load()?;
        *self.loaded.borrow_mut() = Some(loaded);
        Ok(true)
    }

    fn load(&self) -> Result<Loaded, String> {
        let manifest = Path::new(self.manifest);
        let dir = manifest.parent().unwrap_or(Path::new("."));
        // Read before compiling: a file saved during the compile is new.
        let inputs = tauto::program::tote_inputs(dir)?
            .into_iter()
            .chain([manifest.to_path_buf()])
            .map(|p| {
                let h = hash(&p);
                (p, h)
            })
            .collect();
        let package = compile(dir)?;
        let fingerprint = tauto_nir::interface_fingerprint(&package);
        if fingerprint != self.fingerprint {
            return Err(format!(
                "{}: the exported functions or data types changed; rebuild to use them",
                manifest.display()
            ));
        }
        let image = tauto_vm::image::Image::of(&package)?;
        let cx = Cx::new(&image.program, &image.datas);
        Ok(Loaded {
            program: image.program,
            exports: image.exports,
            cx,
            inputs,
        })
    }

    /// The program the build compiled, with the build's view of the files.
    fn read_image(&self, bytes: &[u8]) -> Result<Loaded, String> {
        let image = tauto_vm::image::Image::from_bytes(bytes)
            .map_err(|e| format!("{}: the built program: {e}", self.manifest))?;
        let cx = Cx::new(&image.program, &image.datas);
        Ok(Loaded {
            program: image.program,
            exports: image.exports,
            cx,
            inputs: self
                .inputs
                .iter()
                .map(|(p, h)| (PathBuf::from(p), *h))
                .collect(),
        })
    }
}

/// The hash of a file's content (0 when it cannot be read): what a reload
/// compares, since a modification time can stay the same across a quick
/// save.
pub fn hash(path: &Path) -> u64 {
    std::fs::read(path).map_or(0, |b| tauto_nir::content_hash(&b))
}

/// The package as `tauto-build` compiles it, with the exports the manifest
/// selects.
fn compile(dir: &Path) -> Result<Package, String> {
    let m = tauto::manifest::load(dir)?;
    let loaded = tauto::program::load_tote_for_build(dir)?;
    let mut package = tauto_nir::compile_loaded_with_observer(&loaded, true, false, |_| {})
        .map_err(|e| match e {
            CompileError::Front(m) | CompileError::Build(m) => m,
            CompileError::Unsupported(u) => u.to_string(),
        })?;
    if let Some(selected) = &m.rust.exports {
        package.exports.retain(|e| selected.contains(&e.name));
    }
    Ok(package)
}

/// The process's host, with the facade's extern functions.
struct Embedded<'a> {
    process: tauto_vm::Process,
    externs: Externs,
    cx: &'a Cx,
}

impl tauto_vm::Host for Embedded<'_> {
    fn show(&mut self, name: &str, value: &str) {
        self.process.show(name, value)
    }
    fn stdout(&mut self, text: &str) {
        self.process.stdout(text)
    }
    fn stderr(&mut self, text: &str) {
        self.process.stderr(text)
    }
    fn args(&self) -> Vec<String> {
        self.process.args()
    }
    fn permissions(&mut self) -> &mut Permissions {
        self.process.permissions()
    }
    fn call_extern(&mut self, index: u32, args: Vec<Value>) -> Result<Value, String> {
        (self.externs)(index, args, self.cx)
    }
}
