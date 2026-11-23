# The messages of `trust.run` (`permission_file`).

permissions-too-large = a permissions file is at most 1 MiB
permissions-expected-keys = expected keys such as `read = ["data"]`
permissions-unknown-key = unknown key { $key }: the keys are read, write, env, net, run, clipboard, div and all
permissions-key-error = { $kind }: { $error }
permissions-true-names-nothing = { $kind } is `true`; it names nothing
permissions-false-default = `false` is the default; leave the key out
permissions-expected-texts = expected a list of texts
permissions-bad-name = { $name } is not a name a flag can hold
permissions-empty-list = an empty list grants nothing; leave the key out
permissions-expected-value = expected `true` or a list of texts

# What a run may do, asked at its start (`run_prompt`).

run-prompt-title = { $path } needs these permissions to run (+ marks one not allowed before):
run-prompt-question = Allow? [a] from now on / [y] this time only / [N] do not run:
run-prompt-no-terminal = not run: there is no terminal to ask at; review the above and pass --yes to allow it for this run
run-prompt-not-allowed = not allowed; nothing was run
run-prompt-no-home = no home folder to keep the answer in; set HOME or TAUTO_HOME
run-prompt-kind-read = read files
run-prompt-kind-write = write files
run-prompt-kind-env = read environment variables
run-prompt-kind-net = reach the network
run-prompt-kind-run = start other programs
run-prompt-kind-clipboard = read the clipboard
run-prompt-kind-div = run without the step limit
run-flag-removed = { $flag } is gone: a run asks at its start for what its effects need; pass --yes to allow it without asking
run-grant-needs-list = { $kind } is allowed only for the names that `trust.run` of the project's Tauto.eure lists: write `{ $kind } = [...]` there
permissions-needs-list = { $kind } is allowed only for what it lists: write `{ $kind } = [...]`
