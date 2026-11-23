# Running totes from Rust on the VM (`tauto-embed`)

A Rust crate calls a tote through the facade `tauto-build` writes in
`build.rs`. Both facade kinds expose the same functions and types:

- **Rust backend facade**: the tote is compiled into the crate.
- **VM facade** (`tauto-vm` via `tauto-embed`): the crate contains only the
  data types, value conversions, call stubs and the compiled program image
  (`tauto_vm::image`), so changing the tote recompiles only the small facade.

`TAUTO_BACKEND=vm|rust` chooses; by default, builds with debug assertions use
the VM facade. Totes the VM facade cannot serve (uniffi, nonresuming entries,
exported functions over unconvertible values such as functions, `Nat`, linear
types, links, and unsupported externs below) fall back to the Rust facade
with a warning.

## `reload()`

`reload() -> Result<bool, String>`: the Rust facade always returns `Ok(false)`.
The VM facade recompiles the tote if its files changed and returns `Ok(true)`;
the next call runs the new code. If compilation fails, or the interface
fingerprint (`tauto_nir::interface_fingerprint`: exported functions, data
types, constructor order, extern types) changed, the old code keeps running
and an error is returned. Each thread has its own compiled tote; `reload()`
affects the calling thread.

## How a call ends

The facade's functions end as the Rust backend's code does: a run-time error of
the guest (a division by zero, an overflow) panics, and the guest's `exit`
ends the host process. A host that must outlive the guest calls
`Tote::try_call`, which returns `Failure::Exit(code)` or `Failure::Error(message)`
instead. A missing export, an answer of another type, and a tote that does not
load are mistakes of the host's build and panic in both.

## Conversion and image

`tauto_embed::Vm` converts values; `tauto-rustgen` (`emit_vm_lib_tokens`)
writes the conversions for the tote's data types, which the VM knows only by
index. The embedded `Image` lets the first call run without compiling and
without the tote's files. Programs containing things an image cannot hold
(runtime syntax parsers, macro-host declarations, constants other than
literals and functions) are compiled from source on first call, with a
warning. An image is read only by the same VM version.

## Externs

The VM asks the host for externs by index (`Op::Extern`,
`Host::call_extern`); this layer is language-independent. The VM facade's
`tauto_externs` converts arguments, calls the same `externs` wrappers as the
Rust facade and converts the result. Extern type values are opaque
`Value::Host`s shown as `<T>`. Supported: by-value and `&T` arguments. Externs
taking `&mut T`, generic externs, externs returning borrows or taking Tauto
functions force the Rust facade. `&T` arguments of exported functions (other
than extern types) are copied into the VM.
