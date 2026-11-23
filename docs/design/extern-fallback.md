# Replaceable `extern` with Tauto fallback

An `extern { … }` block is either **required** or **replaceable**. Host
bindings live in `Tauto.eure` (and bind files), never in source.

## Required blocks

Bodiless `fn`, opaque `type`, and host `instance C(T)`. Every name needs a
host binding for native builds. Opaque types have no Tauto constructor;
only extern functions make their values
([`ownership.md`](ownership.md)「`extern`」).

## Replaceable blocks

`struct` / `enum` (not `inductive`) and/or `fn` with Tauto bodies. The block
is one replacement unit:

| Host bindings for the block | Runtime |
| --- | --- |
| none | every member's Tauto body and representation |
| every member | every member's host binding |
| some but not all | build error |

Selection is fixed before code generation. A selected host implementation
that fails at run time is an ordinary failure; it does not fall back.

A required member and a replaceable member do not share a block.

## Representation boundary

The runtime representation of a replaceable type is closed to the block.
Outside it—same file included—no construction, field projection, field
update, or match on that type. Functions outside the block may still call
the block's public operations. `pub(open)` on a replaceable type is refused.

## Checking and trust

Bodies are checked as ordinary Tauto definitions whether or not a host
binding is selected. The kernel does not run host code. Host selection does
not add axioms or change definitional equality. Choosing a host binding for
a dependency tote still requires `trust.extern`; a fallback body is not an
automatic approval of host code.

## Binding resolution

Bindings are keyed by declaration name. Completeness is checked per
replaceable block (stable id: sorted member spellings). JavaScript and
Rust/Wasm bindings for one block must form one consistent host set: a
partial JavaScript map must not send the remainder of the same block
through Wasm with a different representation.
