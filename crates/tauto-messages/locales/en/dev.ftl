# `tauto dev`.

dev-watching = tauto dev: watching { $path }
dev-waiting = tauto dev: waiting for a change
dev-changed = tauto dev: { $files } changed; checking
dev-keeps-running = tauto dev: the running version keeps running
dev-running-again = tauto dev: running again
dev-exited = tauto dev: the program exited with { $code }
dev-ended = tauto dev: the program ended
dev-interrupted = after { $steps } steps; `--steps N` raises it
dev-vm-in-process = tauto dev: TAUTO_VM=rust is for `tauto run`; `tauto dev` runs the machine as a process
dev-error = tauto: { $error }
