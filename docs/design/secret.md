# Secrets and constant time

Secret values (keys, values derived from them, plaintext being decrypted) live
in `Secret(A)`. Proofs see inside it; executable code cannot, except through a
few constant-time operations and `expose`.

## Guarantee

Two inputs differing only in secret contents produce the same leakage trace:

- control flow (arms taken, functions called, iteration counts);
- memory (elements and indices touched, allocation sizes);
- operands of variable-time operations (division, `nat` arithmetic,
  early-exit comparison).

Not covered: power and EM side channels, speculative execution, erasing used
secrets.

## Two views

**Proofs** (`std/secret.taut`): `Secret(A)` is an ordinary inductive with
`Secret::Mk(v)` and `expose(s)`, and theorems may `match` on it. Each secret
operation is defined as the plain operation wrapped in `Secret::Mk` (e.g.
`ct_u64_add(a, b) = Secret::Mk(UInt::wrapping_add64(expose(a), expose(b)))`),
stated by `Refl` theorems such as `ct_u64_add_val`, so functional correctness
is proved as usual.

**Executable code** (`std/builtin/secret.taut`): extraction maps it to Nib's
`Secret(A)`, a `pub` (not `pub(open)`) struct with no visible fields, so it
cannot be built or matched outside the prelude
([`visibility.md`](visibility.md)). `secure_random` returns `Secret(Bytes)`,
and TLS keys (`TlsCert`, `TlsClientCert`) are `Secret(Bytes)`.

- A `match` on `Secret` left in executable code is an extraction error.
- `Secret` has no `PartialEq`, `Ord` or `Hash`, and types containing it have no
  structural `==`. `show` prints `Secret`.
- Generic code may move secrets but not read them.
- Lengths and shapes are public (`List(Secret(UInt(8)))`'s length, `Some`/`None`).

## Operations

For `W` in `u8`, `u32`, `u64` (and `Bool`):

| Kind | Names | Meaning |
| --- | --- | --- |
| Arithmetic | `ct_W_add`, `ct_W_sub`, `ct_W_mul` | modulo `2^w` |
| High product | `ct_u64_mul_hi` | `⌊a·b / 2^64⌋` |
| Bits | `ct_W_and`, `ct_W_or`, `ct_W_xor`, `ct_W_not` | bitwise |
| Shifts | `ct_W_shl`, `ct_W_shr`, `ct_W_rotl`, `ct_W_rotr` | public amount, modulo width |
| Comparison | `ct_W_eq`, `ct_W_lt` | result `Secret(Bool)` |
| Selection | `ct_W_select(c, a, b)`, `ct_bool_select` | `c ? a : b` |
| Width | `ct_u64_of_u8`, … | zero-extend or truncate |
| Booleans | `ct_bool_and`, `ct_bool_or`, `ct_bool_not` | |
| Bytes | `ct_bytes_len`, `ct_bytes_get(s, i)` | public length; byte at public index as `Option(Secret(UInt(8)))` |

There is no secret division, `nat` arithmetic or secret indexing. Table lookups
scan every element with `ct_W_select`; byte comparisons are built from the
operations above.

## `expose`

`expose` is the only way out: use it only for values the cryptographic
argument says are public (ciphertext, public keys, "the tag matched"). Every
executable function whose body calls `expose` is listed as unchecked in trust
reports ([`trust-bundles.md`](trust-bundles.md)).

## Backends

| Backend | Operations | Constant time |
| --- | --- | --- |
| Rust | `tauto_rt::ct` | yes |
| JavaScript | none | no: programs that only carry secrets run; using `ct_` functions is a build error |
| VM (`totes/vm`) | none | no: as JavaScript, its words and numbers take a time that depends on the value |
| niri (`tauto run --backend niri`) | interpreted | no |

Rust `Secret<T>` holds the value; comparisons use the subtraction borrow and
the top bit of `x | -x`, selection uses masks, and masks pass through
`std::hint::black_box`. This relies, outside any proof, on the compiler not
turning masks back into branches (`tauto-rt` `tests/ct_branches.rs` checks
optimized x86_64 code has no secret branches) and on the CPU running word
arithmetic, bit operations and register shifts in operand-independent time.

## Undecided

- A flag allowing `ct_` functions on JavaScript without the guarantee.
- Tests for aarch64 codegen.
- A secret version of the fast byte type.
- Erasing used secrets.
- A Lean theorem, on the Nib model, that traces do not depend on secrets.
