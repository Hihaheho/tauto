# tauto-analyzer-wasm

[`tauto-analyzer`](../tauto-analyzer/README.md) compiled to WebAssembly, so an
editor in a browser checks proofs with the same checker as `tauto check`: both
kernels, the standard library, and nothing faked. The files are only in
memory; the host gives their text and nothing reads or writes a disk.

```bash
bash crates/tauto-analyzer-wasm/build.sh OUT_DIR   # writes OUT_DIR/tauto_analyzer.wasm
```

It needs the `wasm32-unknown-unknown` target. The module imports nothing.

## Calls

Each argument is UTF-8 the host writes into memory taken with `alloc(len)`.
Each call answers a pointer to a length (four bytes, little endian) followed
by that many bytes of JSON; the host gives it back with `release(ptr, 4 + len)`.

| Call | Answer |
| --- | --- |
| `set_text(path, text)` | `{"ok":true}` |
| `goals(path)` | `{"ok":{"report":…,"holes":[…],"library":[…]}}`: `tauto check --json`, `tauto goals --json` and `tauto library --json` |
| `try_fill(path, hole, expr)` | `{"ok":…}`: `tauto try --json`, the text kept as it was |
| `fill(path, hole, expr)` | the same; an accepted candidate becomes the file's text |
| `suggest(path, hole, limit)` | `{"ok":[…]}`: `tauto suggest --json` without `--verify` |

An error is `{"err":"…"}`. A path is absolute (`/game/Swap.taut`).

```js
const { instance } = await WebAssembly.instantiate(bytes, {});
const e = instance.exports, enc = new TextEncoder(), dec = new TextDecoder();
const put = (s) => { const b = enc.encode(s), p = e.alloc(b.length);
  new Uint8Array(e.memory.buffer, p, b.length).set(b); return [p, b.length]; };
const call = (f, ...args) => {
  const r = e[f](...args.flatMap((a) => (typeof a === "number" ? [a] : put(a))));
  const n = new DataView(e.memory.buffer).getUint32(r, true);
  const json = dec.decode(new Uint8Array(e.memory.buffer, r + 4, n));
  e.release(r, n + 4);
  return JSON.parse(json);
};
call("set_text", "/game/Swap.taut", "theorem swap<P: Prop, Q: Prop>(h: And(P, Q)): And(Q, P) { ?top }");
call("fill", "/game/Swap.taut", "top", "and_intro(and_right(h), and_left(h))");
```

## What differs from the native checker

- There is no clock in `wasm32-unknown-unknown`, so the reduction deadline
  (`--timeout`) is never reached: a check runs until it ends.
- `net` of the standard effects is not built in (only `check` runs here).
- The seed of the hash maps under query-flow is a fixed sequence
  (`src/rand.rs`); nothing secret is made from it.

`tests/memory.rs` makes a proof a step at a time on a file that is not on disk.
