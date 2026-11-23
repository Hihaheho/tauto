# `check` settings in `Tauto.eure`

## Time limit

`tauto check` gives each source file a time budget (default 10 s). A file that
exceeds it is an error, never a warning or a skip.

The budget counts time spent checking the file's own declarations, including
the kernel checks run by step expansion
([`macro-steps.md`](macro-steps.md)), but not loading or syntax expansion;
imported files count against themselves. It is enforced by the same deadline
as `--timeout` (a per-declaration limit; whichever comes first wins): the
declaration being checked is rejected, and the rest of that file and later
files are not checked. The error names the file and the limit and points to
`check.slow`.

```eure
check {
  time-limit = 10
  slow { "std/float_pack.taut" = 120 }
}
```

- The nearest `Tauto.eure` above a file decides; with none, 10 s.
- `time-limit` (seconds, positive, may be fractional) applies to files not in
  `slow`. `slow` keys are paths relative to the manifest; each must exist and
  exceed `time-limit`, so the list holds only genuinely slow files.
- `TAUTO_TIME_SCALE=k` multiplies every limit (for loaded machines); the
  `slow` validation uses the written values.
- Unknown keys under `check` are errors.
- The bundled standard library carries its own `check` settings, applied to its
  virtual paths independently of the user's manifest.

## Allowed axioms

```eure
check { axioms { "std/quot.taut" = ["Quot::sound"] } }
```

When `axioms` is present, a declaration under the manifest that depends on an
axiom not listed for its file fails (declaring the axiom itself does not).
Keys must name existing files. Without `axioms`, dependencies are only
reported.
