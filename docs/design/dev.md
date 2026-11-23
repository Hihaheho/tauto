# `tauto dev`

`tauto dev` runs a program like `tauto run` (same arguments, on the machine
`totes/vm`) and restarts it from scratch whenever its sources change. What
its effects need is asked once, at the first start; an answer of "this time
only" covers every restart until `tauto dev` exits.
`--check-ownership` is refused: the dynamic ownership check runs only with
`tauto run --backend niri`.

```bash
tauto dev --tote .
```

## Default entry

With neither `FILE` nor `--tote`, `tauto run` and `tauto dev` run the `run.file`
of the nearest `Tauto.eure` above the working directory, relative to it. `file`
is the only key of `run`.

```eure
run { file = "app/main.taut" }
```

## Watching and restarting

The tote directory, or the file's directory, is polled every 250 ms for
changes to `.taut`, `.tauto` and `.eure` files, skipping hidden directories and
`target`. Imports outside it (dependency totes, std) are not watched.

On a change the new version is loaded and checked while the old one keeps
running. If the check fails, the error is printed and the old version keeps
serving. If it passes, the run is stopped and the new `main` starts. A version
that does not check never runs. The machine runs as a process of its own,
which is killed on a change; the program never sees an error.

No program state carries over, so each restart behaves like `tauto run`.

## Output

`show`, `print` and `eprint` are written immediately. `tauto dev`'s own
messages go to stderr prefixed `tauto dev:`. Without `--steps` there is no
step limit. Permissions are as in `tauto run`.
