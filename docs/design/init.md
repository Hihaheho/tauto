# Tote initialization

`tauto init [DIR]` writes `Tauto.eure` and `src/main.taut`. The path defaults to
the current directory. A missing destination directory is created only when its
parent exists. Existing unrelated files and directories are preserved.

The package name is the destination directory's name: lowercase ASCII letters,
digits and hyphens, starting with a letter. This matches the manifest and the
runtime tote loader. A non-ASCII parent path is allowed; a non-ASCII package name
is rejected before writing. Names are not silently normalized.

The manifest declares version `0.1.0` and no
dependencies. The source is a finite program that needs no external resources.
From the destination, `tauto check src/main.taut` checks it and
`tauto run --tote .` runs it. Initialization itself does not execute programs,
resolve dependencies, invoke tools, create version-control metadata, or change
configuration outside the two generated files.

Existing output files, including dangling symlinks, are errors. Destination and
source directories must not be symlinks; explicit path components are checked
before writing. Parent components (`..`) are rejected. File creation is exclusive
rather than overwriting. On an I/O failure, best-effort cleanup targets the files and empty
directories created by that invocation and reports any cleanup failure. Symlink
checks are preflight checks, not protection against concurrent replacement of
parent directories or output files. Initialization and cleanup assume exclusive
access to the destination directory tree; they are not a race-safe transaction.

Exit status is 0 for success or help, 1 for filesystem or package-name errors,
and 2 for invalid arguments. `tauto init --help` describes the interface.
