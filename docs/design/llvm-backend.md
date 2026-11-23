# LLVM backend (`totes/llvm`)

The LLVM backend writes a checked program as LLVM IR, which LLVM compiles to
machine code. It is the native backend: the program it gives owns its memory
itself, with no Rust compiler and no garbage collector under it.
Distributable binaries are the [Rust backend](rust-backend.md)'s job.

The backend is written in Tauto. `totes/nir` reads a package from its text
([NIR text](nir-text.md)) and `totes/llvm` writes the module. The Rust crate
`tauto-llvm` is the reference the tote is compared with: for the same
package both give the same module, and so the same binary. `tauto build --backend llvm`
uses the crate.

- The output is the text of one LLVM module. `clang` (or `llc` and a linker)
  turns it into a program. Neither the tote nor the crate links an LLVM
  library: LLVM is a tool run on the output.
- `llvm_emit` (`tauto_llvm::emit` in the crate) writes a whole program or
  refuses it, naming what in the program is outside what it writes. It never
  writes a program in part, and never writes code whose meaning it guesses.
- Observable behaviour equals the other backends': what a case shows is what
  it shows under LLVM (`crates/tauto-llvm/tests/cases.rs`).

## How the tote writes IR

IR is data, not text. `src/ir.taut` states the grammar of the IR the backend
writes with `inductive_syntax!(llvm, …)`: each kind of item, instruction,
type and value is a type of its own (`llvm::Instr::I`, `llvm::Ty::I`, …), and
a module is a value of `llvm::Module::I`. `llvm_print` (`src/print.taut`)
writes a module as text, and `llvm::parse` reads one.

The emitter builds every piece with the macro `ll!` (`src/tmpl.taut`), which
takes the piece as IR:

```
b_def(&mut b, ll!(`getelementptr i64, ptr $p, i64 $n`))
```

The macro reads its argument by the grammar when the tote is checked, so a
piece that is not IR is an error where it is written, and gives the value of
the piece's type. A hole `$x` stands for a value of the program: an IR value,
a type, a label, a function, a number, the arguments of a call or the cases
of a `switch`, by where it stands. The names the backend makes (`%t7`, `L7`,
`@f3`, `@drop.2`) are values of types only `src/names.taut` constructs, so a
hole for a label takes a label and nothing else. The runtime is one `ll!` of
whole items (`src/runtime.taut`).

The grammar is one. It names the places a hole may stand (`Value`, `Ty`, a
label, a callee, a count, the arguments, the cases) and has a second start
symbol, `Frag`, for a piece. `llvm::parse` reads a module and takes no hole;
`ll!` reads a `Frag`, and the types of a module (`llvm::…::I`) have no hole.

| file | what it holds |
| --- | --- |
| `ir.taut`, `print.taut` | the grammar of IR, and a module as text |
| `tmpl.taut`, `names.taut` | `ll!`, and the names and numbers written in IR |
| `build.taut` | one function being written: blocks, the frame's slots, fresh names |
| `layout.taut` | how a value of each type is laid out |
| `glue.taut` | the drop, dup and show functions of each type |
| `decision.taut` | the tests of a `match` as a tree |
| `walk.taut` | what is read of every expression in an expression: the locals a closure captures, whether there is a `handle` |
| `func.taut` | a function of the program |
| `runtime.taut`, `emit.taut` | the runtime, and the module of a package |
| `main.taut` | the shell: `llvm emit FILE...`, `llvm print FILE...` |

The tote and the crate make the same choices in the same order, function by
function, so their modules name every value and block alike.

## What it reads

The input is NIR (`tauto_nir::Package`) after these passes, in this order.
The passes are Rust; the tote reads their result as text.

| pass | what the backend then need not decide |
| --- | --- |
| `mono::specialize` | no function or type has a type parameter: each generic function is written once for each list of types it is used at |
| `anf::normalize` | the order of evaluation: every operand is a name or a constant |
| `ownership::insert` | where each value is released: every `drop` is a call in the tree, and every copy is a read marked `Clone` |

`decision::compile` (`d_compile` in the tote) gives the tests of each `match`
as a tree. The backend
decides only how values are laid out and which instructions say each node.
Every type in NIR is written; the backend infers none.

## Values

A value is a row of 64-bit words.

| type | words |
| --- | --- |
| a fixed-width number, a `Nat`, `Bool`, a borrow, a shown text, a `Text`, a function value, a `Vec` | 1 |
| `Unit`, `Never` | 0 |
| a product `A × B` | the words of `A`, then the words of `B` |
| a type with constructors (`data`, `struct`, `Option`, `Result`) | 1 word for the constructor, then room for the largest constructor's fields one after another |

A `Nat` is held as a `u64`. A number narrower than 64 bits is held extended to 64 bits, by its sign. A
word a constructor does not use is zero.

A field stored behind an indirection (`Indirect` in NIR) is one word: the
address of a box on the heap. The first word of a box counts the values that
share it; the other words are the field. A `Shared` box is shared by copies
of the value that holds it, and a `Unique` box has one holder. Nothing else
is on the heap. A `&rc T` is a struct of one field held in a `Shared` box
(NIR's data `&rc`): a copy shares the box, the last one drops the contents,
and a borrow of the contents is the address of the box's field. A type that
holds itself with no indirection has no size and is refused.

A `Text` is the address of a box on the heap: a word that counts the values
that share it, a word for the number of bytes, then the bytes, ended with a
zero byte. A copy of a `Text` shares the box, and the last value that shares
it frees it. A literal is a constant box of the module, whose count is 0:
a count of 0 is never changed, so every read of the literal shares the box
and it is never freed. Two
`Text`s are equal when their bytes are, and a `Text` pattern tests the bytes.
`show` writes a `Text` in quotes, with `"`, `\`, a line break, a carriage
return, a tab and a zero byte escaped by a backslash and every other control
byte, also `0x7f`, as `\u{…}`; every other byte is written as it is.

A `Vec` is the address of a header of three words on the heap: the address of
its elements, how many there are and how many there is room for. The
elements are rows of the words of one element, one after another, so
`Vec(Text)` and `Vec(u64)` differ only in the width of a row and in what the
drop does to each. A `Vec` is never shared and never copied: a borrow of it is
the address of the word that holds it, and it is released with its elements,
the runtime freeing the room and the header. The runtime (`rt_vec_*`, in the
IR of every module) does not know the type of an element; it is given the
number of words of a row, and the elements that need a drop are dropped by
code the backend writes for the element type. The builtins written are
`Vec::new`, `push`, `pop`, `len`, `get`, `get_mut`, `last_mut`, `clear`,
`truncate` and `swap_within`. A `Vec` of borrows is refused, and so are
`show` and `==` on a `Vec`.

A `Slots(S, M, A)` is the address of a header on the heap: the address of the
elements (a row of the words of an `A` for each slot), the capacity, the
address of the flags (a word for each slot, 1 when the slot holds an element),
the address of the marks (a row of the words of an `M` for each slot), the
address of the vacant mark (what `mark` returns for an index past the
capacity), then the words of the state `S`. `new` allocates the rows, clears
the flags and writes a copy of the mark it is given in every slot and as the
vacant mark (each mark is a value of its own; the template is then released);
`state` and `mark` return a copy of the owned value; `put` and `take` release
the mark and state that were there, write the new ones, and set or clear the
flag; `get` and `get_mut` give the address of a slot's row; `resize` grows the
rows and marks the new slots with copies of the mark it is given, or stores a
smaller capacity after dropping the slots that fall off (the heap room of a
smaller capacity is kept), releases the old vacant mark and state, and writes
the new ones. Allocation sizes are checked for overflow before the heap is
asked. A slot past the capacity ends the run for `get`, `get_mut`, `put` and
`take`; `mark` past the capacity is a copy of the vacant mark. An empty slot
ends the run for `get`, `get_mut` and `take`. The runtime never reads the
state; the proofs of the caller say which slots may be read. The drop
releases the state, every mark, the vacant mark and the elements of the
flagged slots, then frees the rows and the header. The builtins written are
`Slots::new`, `cap`, `state`, `mark`, `get`, `get_mut`, `put`, `take` and
`resize`. A `Slots` with a borrow among its types is refused, and so are a
copy, `show` and `==`.

The maps of `std::hashmap` and `std::indexed_map` are written in Tauto on
`Slots`, so the backend has nothing of its own for them.

A function value is the address of a box on the heap: a word that counts the
values that share it, a word for the number of its function, then the words
of what it captured. A copy shares the box, and the last value that shares it
drops what it captured and frees it. There is no call of an address: a call
of a function value of `n` words to `r` words goes to `@call.<n>.<r>`, which
tests the number and calls that function, `@c<number>(ptr %env, …)`, with the
box as its first argument. A function of the program used as a value gets
such a function that calls it. Function types that differ only in their kind
(`shared`, `copy`, …) have the same words.

A closure holds each local of its frame that its body reads, in the order
first read: a copy of the value when the closure clones it, or when the local
holds no box and the closure is not a borrowed one; a copy of the value a
borrow stands for when the closure outlives the borrow (`owned_refs`); and the
address of the local's slot otherwise, which the closure does not outlive. A
closure whose body moves what it captured, or one passed what it uses as
references, is refused.

A local is a slot of its function's frame. A function takes the words of its
parameters as arguments and gives the words of its result (`void`, `i64` or
an array of `i64`). A borrow is the address of the value it stands for.

## Ownership

The backend writes what `ownership::insert` wrote and adds nothing:

- `drop` of a value runs the *drop glue* of its type: it lowers the count of
  each box the value holds and, at zero, drops the content and frees the box.
- A read marked `Clone` runs the *dup glue*: a `Shared` box gets one more
  holder, and a `Unique` box is copied.
- Moving a field out of a `Shared` box takes the content when the box has one
  holder (the box is then freed) and copies it when it has more.
- An arm of a `match` on a local that binds no owned part of it takes
  nothing out: the arm still owns the local whole.

Glue is written once per type, as a function of the address of a value.
`show` of a value is glue too: it writes the text the other backends show.

## Runtime

The runtime is LLVM IR written in the backend (`src/runtime.taut`, `rt.rs` in
the crate) and put at the top of each module. It is in two layers.

The *system layer* is what the runtime asks of the machine, and nothing else
in the module does: `@sys_write` and `@sys_exit`, and the allocator
`@rt_alloc`, `@rt_realloc` and `@rt_free`. The code the backend writes
allocates and releases only through the allocator.

On Linux on x86_64 (`Sys::Linux`, what the tote writes and what `tauto build
--backend llvm` uses there) the layer is the kernel's: a `syscall` instruction
(inline assembly in the module) for `write`, `exit_group`, `mmap`, `munmap`
and `mremap`, an entry point `_start` that calls `main` and ends with its
result, `memcpy`, `memmove`, `memset`, `memcmp` and `bcmp` for what LLVM
itself calls, and an allocator. The program links no library:
`clang -nostdlib -static`.

The allocator gives each block a header of 16 bytes (so a block is aligned to
16) holding its size class. A block of up to 64 KiB is cut from a chunk of
1 MiB of pages and, when released, goes on the list of its class and is the
next one given for it; classes are powers of two from 32 bytes. A bigger block
has pages of its own, grown with `mremap`, and its pages are given back when
it is released. Nothing small is given back to the system, and one thread is
assumed. A request the system does not grant, or one of more than 2^62 bytes,
ends the run with `error: out of memory`.

On a Linux with a C library where there is no layer of system calls (`Sys::Libc`,
what `tauto build` uses on the machines other than Linux on x86_64) the layer
is the library's entry points to the kernel, `write`, `exit`, `mmap` and
`munmap`, and the program has the library's start-up code. The allocator is the
same, on pages from `mmap` (a block that grows moves, by a new `mmap`, a copy
and `munmap`); the library's `malloc` and `printf` are not called, and its
`mmap` constants are Linux's.

The tests that run the address sanitizer build on a third layer (`Sys::Asan`),
where every block is a block of `malloc`, `realloc` and `free`, which the
sanitizer sees. Nothing else uses it.

Everything above the layer is shared. The runtime writes numbers and `show`'s
text itself: no `printf` is called. What a program writes to the standard
output is held in 8 KiB and written when the buffer is full, at the end of the
run, at an error, and at `stdout_flush`; `show` and `stdout` write in the order
the program ran them.

Arithmetic that overflows its width, a division by zero and a `match` no arm
of which matches stop the program with a message on the standard error and
exit code 1.

## Effects

The handlers in force are a chain in the global `@rt.ev`: each entry is the
next entry, the number of an operation and the function value of its arm, and
lives in the frame of its `handle`. A `handle` of `direct` operations makes a
function value of each arm, puts an entry of each in front of the chain, runs
its body, then puts the chain back as it was. An arm reads the locals of the
frame it mentions in place. A `direct` operation finds the nearest entry of
it (`@rt_find`), calls the arm with the chain set to the entries outside that
entry, then sets it back; with no entry the run stops. A function with a
`handle` in it puts the chain back on every `return`.

The program is built for `Target::Llvm`, which does not wrap `main` in a host
handler: the standard effects `stdout`, `stdout_flush`, `stderr`, `exit`,
`argv`, `main` and `fs_read` are answered by the runtime where they are
performed (on system calls, or on the C library under the sanitizer). `show`
is answered the same way unless the program has a `handle` of it, which is
refused. The program has the authority of whoever runs it: the permission
flags of `tauto run` are not enforced in a native binary. `fs_read` does not
check that the file is UTF-8 yet.

A `handle` with an arm that does not resume or that keeps its continuation,
an arm whose pattern may not fit or that has a guard, two arms of one
operation, and an arm that returns are refused.

## What is written

Functions of tier S (no effect but `show`, answered by the host): fixed-width
numbers and their arithmetic and comparison, `Bool`, `Unit`, products, types
with constructors (also recursive and generic ones), `Option`, `Result`,
borrows, `let`, `var`, assignment, `if`, `while`, `return`, `match` with
nested patterns, calls, and `show`. Of `Text`: literals, `==`, `Text`
patterns, `concat`, `Text::of_i64`, `Text::of_u64`, `Text::of_nat`, `Text::len`,
`Text::byte`, `Text::slice`, `Text::compare` and `Text::escape_debug`. Of `Vec`: the
builtins listed under Values. Function values,
closures and their calls, and `handle`s whose arms answer `direct`
operations.

Every other program is refused: one with `Float`, another builtin on
`Text` (they take and give a `Nat`), another builtin on `Vec` or another runtime type, a
union, a `linear` type, a `handle` other than those above, a function or a
function value that may stop or resume, or a `budget`. An `extern` function
and an extern type (a type the host holds) are refused: a native binary has
no case host to answer them.

## How it is checked

`tools/selfhost-harness/tests/llvm.rs` compares the tote with the crate on
every case that shows something. For each package the tote reads the NIR
text and answers a module or what it does not write; the crate answers the
same package. The answers must be equal: the same refusal, or the same
module as `llvm_print` writes it (the crate's text is read by `llvm::parse`
and printed, which drops comments and blank lines and nothing else).

Each pair of modules is then compiled as `tauto build --backend llvm`
compiles a module, and the two programs must be the same bytes.

`tauto build --backend llvm --emit nir` writes the package the backend reads,
so the tote can be given what the CLI would compile. Its roots are the top
level and the `exports` of the tote and `--export` (`exports.md`), each an
`export` item.

`crates/tauto-llvm/tests/cases.rs` compiles the crate's module of every case
that shows something and runs it. A case passes, is refused, or is wrong;
the test fails on a wrong case. A case is wrong when LLVM does not take the
module, when the program shows something else than the case says, or when
the address sanitizer finds a value used after it is released, released
twice, or never released. Every function of the module is checked by the
sanitizer, which sees the blocks because that build takes them from `malloc`
(`Sys::Asan`). Then each case is built again on `Sys::Libc` and, on Linux on
x86_64, on `Sys::Linux` as `tauto build --backend llvm` builds it, and must
show the same. The test needs `clang` and a `cc` that links the address
sanitizer.

`tauto-niri` checks the same ownership rules on NIR itself, before any
backend: a broken rule found there is a fault of a pass, and one found only
here is a fault of this backend.

## Not decided

- How deep recursion may go: a program runs on the system stack.
- Layers of system calls for other machines than Linux on x86_64 (they use the C library's entry points), other operating systems, and an allocator that gives small blocks back to the system or is safe for threads.
- How the steps of a `budget` are counted in machine code.
- A `Nat` beyond 64 bits: a `Nat` is one word like a `u64`, stops the program when a result does not fit, and a literal beyond 64 bits is refused.
- How an arm that does not resume, and one that keeps its continuation, are
  compiled.
- The command that builds a program with this backend.
