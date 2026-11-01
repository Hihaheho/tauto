# The messages of `tauto init`.

init-help =
    usage: tauto init [PATH]
    Creates Tauto.eure and src/main.taut without overwriting files.
    PATH defaults to the current directory; its parent must exist.
    The directory name uses lowercase ASCII letters, digits and -, starting with a letter.
    No dependencies, version control, or tools are invoked.
init-created = Created { $path }
init-run-hint = Run from that directory with: tauto run --tote .
init-failed = tauto init: { $error }
init-not-plain-directory = { $path } is not a plain directory
init-bad-path = PATH must be nonempty and cannot contain ..
init-parent-missing = parent directory { $path } does not exist
init-no-name = cannot derive a package name from the directory
init-bad-name = directory name must start with a lowercase ASCII letter and contain only lowercase ASCII letters, digits and -
init-refuse-overwrite = refusing to overwrite { $path }
init-cleanup-failed = { $error }; could not clean up created paths: { $paths }
