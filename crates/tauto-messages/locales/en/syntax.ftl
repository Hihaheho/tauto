# `tauto syntax`.

syntax-usage = usage: { $usage }
syntax-tables-missing = { $file }: the tables of syntax { $name } are missing; run `tauto syntax gen`
syntax-wrote = wrote { $path }
syntax-tables-unused = { $path }: no syntax uses these tables; run `tauto syntax gen`
syntax-removed = removed { $path }
syntax-cannot-build-generator = cannot build the generator: { $error }
syntax-temp-not-utf8 = the temporary path is not UTF-8
syntax-cannot-run-generator = cannot run the generator: { $error }
syntax-not-found = no syntax { $name } in { $dir }
syntax-ambiguous = more than one syntax { $name } in { $dir }
syntax-error-in = syntax { $name }: { $error }
