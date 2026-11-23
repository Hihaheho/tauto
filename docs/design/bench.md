# `tauto bench`

`tauto bench` builds a file or package once like
`tauto build --backend rust --release` (including `TAUTO_TARGET_DIR`), then
runs the executable repeatedly and reports wall-clock time per run in
milliseconds: min, median, mean, max and population standard deviation.

- `--warmup N` (default 1, 0–100) and `--samples N` (default 10, 1–1000).
  **Every run repeats the program's side effects**; nothing is rolled back.
  Stdin is empty.
- `--timeout-ms N` (default 30000, up to 3600000) per run. On timeout the
  direct child is killed (its descendants are not) and no statistics are
  printed.
- Each run is a fresh process; the time includes startup, exit and output
  collection. It is not a profiler.
- Every run, warmups included, must exit successfully with stdout and stderr
  byte-identical to the first run; each stream is capped at 1 MiB. Otherwise the
  command fails. Program output is not shown.
- `--json` prints the samples, statistics, method, warmup count, output sizes
  and consistency in one object.

Exit status: 0 success, 1 build/run/consistency failure, 2 bad arguments.
