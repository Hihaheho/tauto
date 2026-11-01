# The messages of `--permissions FILE`.

permissions-needs-file = --permissions needs a file
permissions-file-error = { $file }: { $error }
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
