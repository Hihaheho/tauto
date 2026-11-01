# `tauto proof-status`.

proof-status-usage = usage: { $usage }
proof-status-counts = { $files ->
        [one] 1 file
       *[other] { $files } files
    }: { $ok } ok, { $incomplete } incomplete ({ $holes ->
        [one] 1 hole
       *[other] { $holes } holes
    }), { $failed } failed, { $skipped } skipped
proof-status-none = none
proof-status-axioms = axioms used: { $axioms }
proof-status-externs = extern functions: { $externs }
proof-status-unread = did not read: { $file }
