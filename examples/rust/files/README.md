# examples/rust/files: a hand-written bridge crate

`bridge/` is a Rust crate written by hand, and `Tauto.eure` maps the externs in `src/main.taut`
(`shout`, `count_chars`) to its functions.

```bash
tauto run --backend rust examples/rust/files
```
