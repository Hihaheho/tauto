//! getrandom's source in WebAssembly (`--cfg getrandom_backend="custom"` in
//! `build.sh`). Only the hash maps under query-flow ask for it, to seed their
//! hashes; nothing secret is made from it, so a fixed sequence will do.

use std::cell::Cell;

thread_local! {
    static STATE: Cell<u64> = const { Cell::new(0x9E37_79B9_7F4A_7C15) };
}

/// # Safety
/// `dest` points to `len` writable bytes.
#[unsafe(no_mangle)]
unsafe extern "Rust" fn __getrandom_v03_custom(
    dest: *mut u8,
    len: usize,
) -> Result<(), getrandom::Error> {
    let out = unsafe { std::slice::from_raw_parts_mut(dest, len) };
    STATE.with(|s| {
        for b in out {
            let mut x = s.get();
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            s.set(x);
            *b = (x.wrapping_mul(0x2545_F491_4F6C_DD1D) >> 56) as u8;
        }
    });
    Ok(())
}
