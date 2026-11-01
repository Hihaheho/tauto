# `tauto test`.

test-usage = usage: { $usage }
test-case-todo = case is unimplemented or asks for an unsupported assertion
test-case-backend-only = case has no evaluator assertion; backend runners check it
test-case-unexpected-pass = case passes; remove its unimplemented mark
test-summary = { $passed } passed; { $failed } failed
test-none-selected = no tests selected
test-discovery-symlink = { $path }: test discovery does not follow symlinks
test-program-exited = program exited with { $code }
