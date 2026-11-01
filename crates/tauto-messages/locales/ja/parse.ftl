# The syntax errors of the parser (tauto-parol).

parse-too-deep = ソースの入れ子が深すぎる
parse-syntax-error = 構文エラー
parse-unexpected-input = 予期しない入力
parse-keyword-as-name = `{ $word }` はキーワードであり、名前には使えない。`r#{ $word }` と書くこと
parse-unexpected = 予期しない { $found }
parse-input-after-end = 終わりの後に予期しない入力がある
parse-let-type-eq = この `let` には `=` はあるが `:=` がない。型の中の `=` は命題の等号なので、束縛は `let x: T := v` と書くこと
