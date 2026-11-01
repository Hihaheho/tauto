# `--permissions FILE` のメッセージ。

permissions-needs-file = --permissions にはファイルが必要である
permissions-file-error = { $file }: { $error }
permissions-too-large = 権限ファイルは 1 MiB までである
permissions-expected-keys = `read = ["data"]` のようなキーが必要である
permissions-unknown-key = 未知のキー { $key }: キーは read、write、env、net、run、clipboard、div、all である
permissions-key-error = { $kind }: { $error }
permissions-true-names-nothing = { $kind } が `true` である。これは何も指さない
permissions-false-default = `false` は既定値である。キーごと省くこと
permissions-expected-texts = テキストのリストが必要である
permissions-bad-name = { $name } はフラグに書ける名前ではない
permissions-empty-list = 空のリストは何も許さない。キーごと省くこと
permissions-expected-value = `true` かテキストのリストが必要である
