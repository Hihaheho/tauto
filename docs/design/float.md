# `Float`, `Float32` and `BinNat`

`Float` is an IEEE 754 binary64 value ([`nib.md`](nib.md)). In the proof
language, `std/float.taut` defines it as 64 bits with integer-computed
arithmetic; extraction maps that to Nib's `Float` and builtins.

## Literals

A decimal with a point or exponent is a `Float` literal, rounded to nearest.
Out-of-range literals are type errors; negatives use unary `-`; `.5`, `5.`,
`inf` and `NaN` are not literals; there are no `Decimal` literals or `Float`
patterns. Integer literals are never `Float`, and mixing number kinds is a type
error ([`nib.md`](nib.md)); convert with `Float::of_i64`.

## Operations

- `+ - *` and unary `-` are IEEE 754 (round half to even): overflow gives
  infinity, `0 * inf` NaN, never a runtime error.
- `/` is IEEE 754, except that dividing by `0.0` or `-0.0` is the runtime error
  `division by zero` (as in the Lean model `FOp.flt`).
- Comparisons and `==` are IEEE 754 (`0.0 == -0.0`, NaN unequal to itself).
  `Float` has `PartialEq` only, not `DecEq`, and no `Key`, so it cannot key a `HashMap`
  ([`classes.md`](classes.md)).

`show` and `Text::of_float` print the shortest decimal that reads back to the
same value, without exponent, preferring the larger of equally near
candidates; signed infinities, `NaN` and `-0` keep their sign. Cases:
[`cases/eval/float.eure`](../../cases/eval/float.eure).

## Functions (`std/prelude/num.taut`, trusted `extern`s)

| Function | Meaning |
| --- | --- |
| `Float::of_i64(n)` | nearest (half to even) |
| `I64::of_float(x)` | truncate toward 0; NaN, infinity or out of range is the runtime error `the number is too large` |
| `Float::of_text(t)` | literal syntax with optional `-`, else `None`; huge values are infinity |
| `Text::of_float(x)` | as `show` |
| `Float::bits(x)`, `Float::of_bits(b)` | `u64` bits; NaN canonicalized |
| `Float::is_nan`, `abs`, `floor`, `ceil`, `trunc` | IEEE 754 |
| `Float::round(x)` | nearest integer, halves away from 0 |
| `Float::sqrt(x)` | correctly rounded |
| `cbrt`, `exp`, `ln`, `log2`, `log10`, `pow(x, y)` | |
| `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2(y, x)`, `sinh`, `cosh`, `tanh` | |

All backends return identical bits and text. Operations IEEE 754 determines
(arithmetic, comparison, `sqrt`, `abs`, `floor`, `ceil`, `trunc`, `round`) use
the platform. The others never use platform math: Rust uses
`crates/tauto-rt/src/float_math.rs`, JavaScript the same algorithms
operation-for-operation in `crates/tauto-jsgen/src/float.js`, compared by cases
and API tests. Printing follows Rust's `Display`.

## `Float` in proofs (`import std::float`)

- `Float` is `float(bits: UInt(64))`. Operations split sign, mantissa and exponent,
  compute exactly with integers below `2^128` (which the kernel evaluates
  directly) and round to nearest even.
- After import, `1.5` in proofs reads as the corresponding bits
  (`check/sugar.rs`); operators stay `Nat`, so write `Float::add(a, b)`.
- Defined: `add`, `sub`, `mul`, `neg`, `div(a, b, h)` (`h`: `b` nonzero),
  `checked_div`, `eq`, `lt`, `le`, `is_nan`, `is_infinite`, `is_zero`, `abs`,
  `sqrt`, `trunc`, `floor`, `ceil`, `round`, `bits`, `of_bits`, `of_i64`,
  `SInt::of_float_checked64`. Closed computations close by `Refl`.
- Functions IEEE 754 leaves open (`exp`, `ln`, `pow`, trigonometry) and
  `Text::of_float`, `Float::of_text` are **axioms**, reported as such (e.g.
  `std.Float.Float.exp`); extraction admits only these axioms, mapped to
  builtins of the same name.
- NaN bits are canonicalized at runtime and every definition reads bits through
  `Float::raw`, so no program distinguishes NaNs and definition and execution
  agree.
- Trusted: the extraction map ([`self-host.md`](self-host.md)) and the axiom
  implementations (`float.rs`, `float_math.rs`, `float.js`).
  `crates/tauto-cli/tests/float.rs` compares kernel-computed definitions with
  native results.
- Nib type safety (`lean/Proto/Nib/`, [`semantics.md`](semantics.md)) covers
  `Float`, `Float32` and `+ - * /`; division by zero is a runtime error in the
  model too, and `Float::div` excludes it by proof.

## `Float32`

IEEE 754 binary32, for bulk numeric data, with the same rules.

- No literals: `Float32::of_float(0.1)` rounds (infinity if too large),
  `Float::of_float32(x)` is exact.
- Arithmetic, comparison and `==` are IEEE 754, `/ 0` is a runtime error,
  `PartialEq` only.
- `std/prelude/num.taut`: `bits`/`of_bits` (`u32`), `is_nan`, `abs`, `floor`,
  `ceil`, `trunc`, `round`, `sqrt`, and the `Float` math function names. NaN
  bits are `0x7FC00000`.
- Undetermined functions are defined as the `Float` function rounded to
  `Float32`, so they agree everywhere. `show` prints the value as a `Float`.
- Rust computes in `f32`; JavaScript in `number`, rounding
  `+ - * /` and `sqrt` with `Math.fround`. `Float` has more than twice
  `Float32`'s precision, so double rounding equals single rounding.

`std/float32.taut` defines `float32(bits: UInt(32))`, `of_float` and `of_float32`
on bits, and arithmetic via `Float` (`Float32::add(a, b)` =
`of_float(Float::add(of_float32(a), of_float32(b)))`), which matches binary32
by the double-rounding property. Math functions are axioms as for `Float`.

## `Float` as numbers (`import std::float_real`)

Proof-only definitions connecting bits to numbers; nothing here is extracted.

- `Rat` (`std/rat.taut`) is `num / (den + 1)`; `add` and `mul` return reduced
  fractions; `eq`, `le`, `lt` compare numerically (`Eq(Rat, …)` is
  representation equality).
- `Float::val(x)`: the number of a finite `x` (`±0` are 0), else `None`.
  `Float::of_rat(r)`: nearest `Float` (infinity if too large; 0 is `+0`,
  underflow keeps `r`'s sign).
- "Correctly rounded": `Float::add(a, b) = Float::of_rat(Rat::add(va, vb))`
  when finite and not exactly 0. This is checked by kernel computation in
  `crates/tauto-cli/tests/float.rs`, not proved as a general theorem.
- `Float::finite(x)`; functions excluding NaN take
  `Eq(Bool, Float::finite(x), true)`. `Float::near(y, r, eps)`;
  `Refines(g, f, eps)`: for every finite `x`, `g(x)` is within `eps` of `f`.
  Prove mathematics on `f` exactly; state the executed `g`'s error by
  `Refines`.
- `Float::total_cmp` is IEEE `totalOrder` (`-0 < +0`). It, IEEE `==`/`<` and
  `Eq(Float, …)` (bit equality) are three different things.
- `Float32::val` and `Float32::of_rat` (rounding directly; double rounding is
  wrong for general numbers).

The kernel does not evaluate closed numbers ≥ `2^128`, so `Refl` works for
denominators below `2^72`. `OrderedField(R)` in `std/real.taut` bundles
ordered-field operations and laws; theorems over `F: OrderedField(R)` add no
axioms.

## `BinNat`

Large numbers are computed with the inductives of `std/bin_nat.taut`, without
widening the kernel's built-in arithmetic. `Pos` is little-endian (`One`,
`Bit0(p)` = `2p`, `Bit1(p)` = `2p + 1`); `BinNat` is `BinZero` or `BinPos(p)`.
Operations: `add`, `mul`, `sub` (truncated), `compare`, `eq` (via `PosDiff`).
`to_nat`/`of_nat` convert, with axiom-free theorems that operations agree with
`Nat` (`to_nat(of_nat(n)) = n`, `to_nat(add(a, b)) = Nat::add(…)`, `mul`
likewise), `eq_refl`, `eq_sound`, `compare(a, a) = Equal`,
`sub(a, a) = BinZero`.
