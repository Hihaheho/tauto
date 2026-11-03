# examples/rust/threads: the threads executor

`Tauto.eure` sets `executor = "threads"`, so each task gets its own thread and its waits block
that thread. `src/main.taut` runs a producer and a consumer over a bounded `Channel`, then sleeps.

```bash
tauto run --backend rust examples/rust/threads
```
