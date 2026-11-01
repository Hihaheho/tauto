# アナライザ (`tauto-analyzer`) のメッセージ: 穴を展開できない理由と、
# 名前を変えられない理由。名前・項・パスは変数で、そのまま書く。

analyzer-not-an-expansion = `{ $text }` は穴の展開の仕方ではない: `intro`、`match(x)`、`induction(x)` またはタクティク `name!(arg)` を使うこと
analyzer-intro-not-function = ゴール `{ $goal }` は関数型ではない: 導入するものがない
analyzer-match-not-in-scope = `{ $var }` は `?{ $hole }` でスコープにある変数ではない
analyzer-match-not-inductive-var = `{ $var }` : `{ $ty }` は帰納型ではない
analyzer-match-not-inductive = `{ $family }` は帰納型ではない
analyzer-tactic-needs-step = `{ $name }!(…)` はタクティクだ: そのステップのアームは、ファイルをそれで検査して初めて分かる (expand_step)
analyzer-step-arm-reads = ステップのアーム { $k } が `{ $line }` となっている
analyzer-file-not-read = ファイルは読んだファイルの中にない
analyzer-candidate-not-in-scope = 候補 `{ $name }` は読み込んだスコープにない
analyzer-query-waits-not-file = クエリがファイルでないものを待っている
analyzer-fill-no-longer-reads = `?{ $name }` に `{ $expr }` を入れるとファイルが読めない: { $error }
analyzer-not-loaded = プログラムが読み込まれていない
analyzer-no-such-statement = そのような文はない
analyzer-pinned-field = フィールドは読み出す対象の型から見つかる
analyzer-pinned-syntax = syntax が作る名前 (`name_Rule`) はそこから導かれる
analyzer-pinned-field-pun = その名前はフィールドの名前でもあり、一度だけ書かれている
analyzer-rename-no-name = ここには宣言を見つけられる名前がない
analyzer-rename-prelude = `{ $name }` はプレリュードのものだ
analyzer-rename-pinned = `{ $name }` は名前を変えない: { $why }
analyzer-rename-no-name-here = ここに名前がない
analyzer-rename-file-without-path = パスのないファイル
analyzer-rename-broken-file = { $path } は全体として読めない。先に構文エラーを直すこと
analyzer-rename-opaque = `{ $old }` は { $path } の構文リテラルまたは `quote` の中にも書かれており、そこでは使用箇所が見つからない
analyzer-rename-unresolved = `{ $old }` は { $path }:{ $line } に書かれているが宣言に解決されないので、この宣言の使用かもしれない
analyzer-rename-approximate = `{ $old }` は { $path } で使われているが、どの宣言かは名前でしか分からない
analyzer-rename-tote-mate = `{ $old }` は { $path } にも現れる。そのファイルは { $file } をインポートせずに見るトートにある
analyzer-rename-text-changed = 名前の変更中にテキストが変わった
analyzer-rename-no-path = パスがない
analyzer-rename-edited-not-load = 編集したファイルが読み込めない
analyzer-rename-an-edited-not-load = 編集したファイルの一つが読み込めない
analyzer-rename-leaves-syntax-error = 名前を変えると { $path } に構文エラーが残る
analyzer-rename-captures = `{ $new_name }` にすると { $path } のある名前の指す先が変わる (そこで既にスコープにある)
analyzer-rename-not-a-name = `{ $name }` は名前ではない
analyzer-rename-keyword = `{ $name }` はキーワードだ
