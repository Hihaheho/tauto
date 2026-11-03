# examples/javascript: the JavaScript backend

A tote for the JavaScript backend (`docs/design/javascript-backend.md`). `src/main.taut` calls
asynchronous host functions from `host/http.mjs` (one through an `http_get` effect) and Rust
externs compiled to Wasm: the functions in `bridge/` and `i64::abs` (`absolute`). Callbacks
passed to them perform effects.

```bash
tauto run --backend javascript examples/javascript/src/main.taut
```

It runs with `node`; building the Rust externs needs the `wasm32-unknown-unknown` target.
