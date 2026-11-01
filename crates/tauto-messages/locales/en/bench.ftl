# `tauto bench`.

bench-help =
    usage: { $usage }

    Build once in release mode, then measure whole-process wall time.
    Defaults: 1 warmup, 10 samples, 30000 ms timeout per run.
    Warmups: 0..100; samples: 1..1000; timeout-ms: 1..3600000.
    Output limit: 1 MiB per stream per run; stdin is empty.
    Every run repeats the program's effects. Compilation is not timed.
    Startup, output collection, supervisor threads and 1 ms polling are timed.
    Do not interpret sub-millisecond differences. This is not a profiler.
bench-duplicate-option = duplicate option: { $option }
bench-backend-rust-only = bench supports --backend rust
bench-needs-integer = { $option } requires a nonnegative integer
bench-out-of-range = { $option } is outside its allowed range
bench-timeout-range = --timeout-ms requires an integer from 1 to 3600000
bench-unknown-option = unknown option: { $option }
bench-one-path = bench accepts one source file or package directory
bench-needs-path = bench requires a source file or package directory
bench-program-failed = program failed ({ $status })
bench-output-changed = program stdout/stderr changed between runs; no timing summary produced
bench-cannot-read-output = cannot read program output: { $error }
bench-output-limit = program output exceeds 1 MiB per stream
bench-cannot-start = cannot start benchmark: { $error }
bench-cannot-wait = cannot wait for benchmark: { $error }
bench-timeout = program exceeded timeout ({ $ms } ms)
bench-reader-failed = { $stream } reader failed
bench-running = bench: running { $warmup } warmup(s) and { $samples } sample(s); program effects repeat on every run
bench-run-error = run { $run }: { $error }
bench-overhead-note = includes supervisor threads and 1 ms polling; sub-millisecond differences are not meaningful
bench-heading = rust release: whole-process wall time (ms), { $samples } samples, { $warmup } warmup(s)
bench-consistent = exit 0; consistent stdout ({ $stdout } bytes) and stderr ({ $stderr } bytes)
bench-error = bench: { $error }
