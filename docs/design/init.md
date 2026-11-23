# `tauto init`

`tauto init [DIR]` (default: the current directory) writes `Tauto.eure`
(version `0.1.0`, no dependencies) and a runnable `src/main.taut`. Nothing
else is touched: no dependency resolution, no VCS metadata.

- The package name is the directory name and must be lowercase ASCII letters,
  digits and hyphens, starting with a letter. It is never normalized.
- A missing destination is created only if its parent exists. `..`,
  symlinked directories and existing output files (even dangling symlinks) are
  errors; files are created exclusively. The symlink checks are preflight only;
  concurrent changes to the tree are not guarded against.
- On I/O failure, the files and empty directories this run created are removed
  best-effort.

Exit status: 0 success, 1 filesystem or name error, 2 bad arguments.
