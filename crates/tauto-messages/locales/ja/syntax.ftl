# `tauto syntax`.

syntax-usage = 使い方: { $usage }
syntax-tables-missing = { $file }: syntax { $name } の表がない。`tauto syntax gen` を実行すること
syntax-wrote = { $path } を書いた
syntax-tables-unused = { $path }: この表を使う syntax はない。`tauto syntax gen` を実行すること
syntax-removed = { $path } を消した
syntax-cannot-build-generator = 生成器をビルドできない: { $error }
syntax-temp-not-utf8 = 一時ファイルのパスが UTF-8 ではない
syntax-cannot-run-generator = 生成器を実行できない: { $error }
syntax-not-found = { $dir } に syntax { $name } はない
syntax-ambiguous = { $dir } に syntax { $name } が二つ以上ある
syntax-error-in = syntax { $name } のエラー: { $error }
