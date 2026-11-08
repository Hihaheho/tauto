# The syntax errors of the parser (tauto-parol).

parse-too-deep = ソースの入れ子が深すぎる
parse-syntax-error = 構文エラー
parse-unexpected-input = 予期しない入力
parse-keyword-as-name = `{ $word }` はキーワードであり、名前には使えない。`r#{ $word }` と書くこと
parse-unexpected = 予期しない `{ $found }`
parse-unexpected-line-break = 予期しない改行
parse-input-after-end = 終わりの後に予期しない入力がある
parse-let-type-eq = この `let` には `=` はあるが `:=` がない。型の中の `=` は命題の等号なので、束縛は `let x: T := v` と書くこと
parse-let-pattern = `let` は名前を一つだけ束縛し、パターンは取らない。`let x := v` と書いてフィールドアクセス（`x.field`）で取り出すか、`match` で値を分解すること
