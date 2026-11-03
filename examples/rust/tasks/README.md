# examples/rust/tasks: tasks on threads

Tasks share a host counter from the hand-written bridge in `bridge/`, and the std types `Atomic` and `Mutex`.
The program starts tasks, so the Rust backend builds it for threads, and every extern type
must be `Send + Sync`.

```bash
tauto run --backend rust examples/rust/tasks
```
