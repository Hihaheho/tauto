# `tauto macro`.

macros-usage = usage: { $usage }
macros-not-writing = not writing: the expansion has errors
macros-warning = warning: { $message }
macros-inside = (inside #{ $parent })
macros-steps = { $steps ->
        [one] 1 step
       *[other] { $steps } steps
    }
macros-no-call = no macro call at { $at }
macros-input = input
macros-output = output
