# examples/rust/main-thread: running `main` on the main thread

`Tauto.eure` sets `main-thread = true`, so the Rust build runs the program on the process's main
thread instead of on a thread of its own. `src/main.taut` asks the runtime whether it is there
(`tauto_rt::main_thread::is_main`) and shows `true`.

```bash
tauto run --backend rust examples/rust/main-thread
```
