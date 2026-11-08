//! What the machine of `totes/vm` asks of Rust: native code for some of the
//! program's functions (`totes/vm/src/native.taut`, `docs/design/jit.md`).
//!
//! The `tauto` command hands over the program it wrote for the machine
//! (`set_program`) before the tote runs; the code is generated on the
//! machine's thread at its first question. A machine with no program handed
//! over, or a bridge built without the feature `jit`, has no native code.

#[cfg(feature = "jit")]
mod native {
    use std::cell::RefCell;
    use std::sync::Mutex;

    use tauto_jit::Run;

    static PROGRAM: Mutex<Option<tauto_nir::Package>> = Mutex::new(None);

    /// Hands over the program the machine is about to run.
    pub fn set_program(pkg: tauto_nir::Package) {
        *PROGRAM.lock().unwrap_or_else(|e| e.into_inner()) = Some(pkg);
    }

    struct State {
        jit: Option<tauto_jit::Jit>,
        args: Vec<(bool, u64)>,
        last: Run,
    }

    thread_local! {
        static STATE: RefCell<Option<State>> = const { RefCell::new(None) };
    }

    fn with<R>(f: impl FnOnce(&mut State) -> R) -> R {
        STATE.with(|s| {
            let mut s = s.borrow_mut();
            let state = s.get_or_insert_with(|| {
                let pkg = PROGRAM.lock().unwrap_or_else(|e| e.into_inner()).take();
                State {
                    jit: pkg.as_ref().and_then(tauto_jit::compile),
                    args: Vec::new(),
                    last: Run::default(),
                }
            });
            f(state)
        })
    }

    pub fn vm_native_has(f: u64) -> bool {
        with(|s| s.jit.as_ref().is_some_and(|j| j.has_fn(f as u32)))
    }

    pub fn vm_native_begin() -> bool {
        with(|s| s.args.clear());
        true
    }

    pub fn vm_native_arg(neg: bool, mag: u64) -> bool {
        with(|s| s.args.push((neg, mag)));
        true
    }

    pub fn vm_native_run(f: u64, limited: bool, left: u64) -> u64 {
        with(|s| {
            let Some(j) = &s.jit else { return 4 };
            let fuel = if limited { left } else { u64::MAX };
            s.last = j.run(f as u32, &s.args, fuel);
            s.last.status
        })
    }

    pub fn vm_native_left() -> u64 {
        with(|s| s.last.left)
    }

    pub fn vm_native_mag() -> u64 {
        with(|s| s.last.mag)
    }

    pub fn vm_native_neg() -> bool {
        with(|s| s.last.neg)
    }

    pub fn vm_native_kind(f: u64) -> u64 {
        with(|s| s.jit.as_ref().map_or(2, |j| j.kind(f as u32)))
    }
}

#[cfg(feature = "jit")]
pub use native::*;

#[cfg(not(feature = "jit"))]
mod none {
    pub fn vm_native_has(_: u64) -> bool {
        false
    }
    pub fn vm_native_begin() -> bool {
        true
    }
    pub fn vm_native_arg(_: bool, _: u64) -> bool {
        true
    }
    pub fn vm_native_run(_: u64, _: bool, _: u64) -> u64 {
        4
    }
    pub fn vm_native_left() -> u64 {
        0
    }
    pub fn vm_native_mag() -> u64 {
        0
    }
    pub fn vm_native_neg() -> bool {
        false
    }
    pub fn vm_native_kind(_: u64) -> u64 {
        2
    }
}

#[cfg(not(feature = "jit"))]
pub use none::*;
