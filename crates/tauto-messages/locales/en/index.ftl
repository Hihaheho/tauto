# The messages of `tauto index`, and of the gate `add`, `update` and `lock` pass through.

index-help =
    usage: tauto index sync [--tote DIR]
    { "       " }tauto index status [--tote DIR]
    { "       " }tauto index check [NAME…] [--tote DIR]
    { "       " }tauto index new DIR [--name NAME]
    { "       " }tauto index observe (NAME [--locked] | --project ID --git URL [--branch NAME | --tag NAME]) [--index ALIAS] [--tote DIR]
    { "       " }tauto index decide (NAME | --project ID) (accept | reject) --reason TEXT [--rev REV] [--index ALIAS] [--tote DIR]
    { "       " }tauto index withdraw (NAME | --project ID) --reason TEXT [--rev REV] [--index ALIAS] [--tote DIR]
    { "       " }tauto index publish [--valid-for SECONDS] [--index ALIAS] [--tote DIR]

    { "  " }sync     fetch every index Trust.eure names, check its history, and take in
    { "           " }what is new. A batch an index should not have published, or a
    { "           " }history rewritten under what was taken in, stops that index here
    { "           " }for good.
    { "  " }status   what adopting requires, with the user policy, and what this
    { "           " }machine holds of each index: how far it was taken in, the pin, the
    { "           " }last check of its origin, and whether it stopped.
    { "  " }check    whether the locked commit of each Git dependency (or of NAME) may
    { "           " }be adopted now under Trust.eure, and if not, why. Run `sync` first.

    { "  " }Keeping one's own index (a local-owned index in Trust.eure):
    { "  " }new       start an index in the empty directory DIR, and print its entry
    { "            " }for Trust.eure.
    { "  " }observe   record the newest commit of the Git dependency NAME (its locked
    { "            " }commit with --locked), or of the branch or tag of a project not
    { "            " }yet a dependency, and its source tree, in the batch being written.
    { "  " }decide    accept or reject a revision: REV, or the one observed last.
    { "  " }withdraw  take back a revision for good.
    { "  " }publish   commit the batch being written (or an empty one, which keeps the
    { "            " }index valid) for --valid-for seconds, a day unless given.

    Trust.eure sits beside the project's Tauto.eure. When it is there, add,
    update and lock adopt a new commit of a Git dependency only when the indexes
    it names allow it, and every Git dependency names its `project`. What was
    taken in is kept in $TAUTO_INDEX_STATE (else ~/.local/state/tauto/index).

    The user policy, $TAUTO_USER_TRUST (else ~/.config/tauto/trust.eure), adds
    to every project's Trust.eure: more observers and age witnesses, a longer
    wait, shorter limits. Without one, the safe default applies: a revision is
    adopted only 14 days after it was observed, however long Trust.eure waits.
    `min_age_seconds = 0` in the user policy waits only as Trust.eure says.
index-takes-no-argument = { $command } takes no argument
index-unknown-command = unknown command index { $command }
index-command-error = tauto index { $command }: { $error }
index-usage-error = tauto index: { $error }
index-tote-needs-dir = --tote needs a directory
index-user-default = the safe default
index-user-default-no-file = the safe default, as there is no { $path }
index-file-error = { $path }: { $error }
index-strengthen-error = { $path } with { $user }: { $error }
index-trusts-no-index = { $dir } has no { $file }; it trusts no index
index-no-policy = { $dir } has no { $file }
index-syncing = Syncing index { $alias }
index-syncing-from = Syncing index { $alias } ({ $url } { $reference })
index-sync-nothing-new = nothing new
index-sync-new-batches =
    { $n ->
        [one] 1 new batch
       *[other] { $n } new batches
    }
index-stopped = STOPPED: { $why }
index-sync-failed = index { $alias }: { $line }
index-requires = observed by { $observers }; aged by { $witnesses }; waits { $wait }; checkpoints valid { $lifetime }; origin checked within { $check }
index-status-user = user policy: { $policy }
index-status-every = every project: { $requires }
index-status-project = project sha256:{ $project }…: { $requires }
index-status-not-taken = not taken in; run `tauto index sync`
index-status-taken = taken in through { $rev }
index-status-pinned = pinned at        { $rev }
index-status-checked-ago = origin checked   { $ago } ago, at { $rev }
index-status-checked-future = origin checked   at { $time }, after now
index-status-checked-never = origin checked   never
index-may-adopt = may be adopted
index-may-not-adopt = may not be adopted:
index-not-locked = { $name } is not a locked Git dependency
index-needs-project = { $name }: under { $file } every Git dependency names its project (`project = "sha256:…"`)
index-not-allowed = the indexes do not allow it
index-wait-from = (the wait of { $wait } is from { $user }; { $file } waits { $own })
