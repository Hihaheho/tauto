# 証明付きのミニ言語検査器

小さなスタック言語の型付け規則から、`mode!` で検査器を生成する例です。
成功時には出力スタック型、その型付けの導出、出力の一意性が得られます。
拒否時には、どの出力型でも型付けできないことの反証が得られます。
`check_and_run` は検査に成功したときだけ実行器を呼びます。

人間が読む仕様は `src/typing.taut` の `OpTyping` と `Typing` です。
検査器とその証明をマクロが生成し、生成物を通常のカーネルが検査します。
入力プログラムの型付けを手で証明して渡す必要はありません。

## 言語と実行例

スタックの値は自然数と真偽値です。`PushNum` と `PushBool` で値を積み、
`Add` で上の二つの自然数を足し、`Dup` で一番上の値を複製します。
`Seq` は二つのプログラムを順に実行します。`Branch` は一番上の真偽値を取り除き、
その値で選んだ枝を実行します。`Halt` はスタックをそのまま返します。
スタックの先頭は `Number` / `Boolean` と `NumOn` / `BoolOn` の外側です。

`src/programs.taut` のプログラムを `src/main.taut` が実行します。

| プログラム | 検査と実行 |
|---|---|
| 2 と 3 を積んで足す | 数値が一つ残り、値は 5 |
| 真の枝で 7 を複製して足し、分岐後にもう一度二倍する | 値は 28 |
| 偽の枝で 20 と 1 を足し、同じ続きで二倍する | 値は 42 |
| 真偽値の上で 2 と 3 を足す | 下にある真偽値を保つ |
| 真偽値を複製する | 同じ真偽値が二つ残る |
| 値を一つだけ積んで足す | スタック不足で拒否 |
| 数値と真偽値を足す | オペランドの型が違うため拒否 |
| 二つの枝が数値と真偽値を返す | 合流後の型が揃わないため拒否 |
| 実際には選ばれない枝に不正な `Add` がある | その枝も検査するため拒否 |

最後の例は、検査を通さず実行すれば 7 を返します。それでも検査器は拒否します。
反証が意味するのは **この型付け規則の導出がないこと** です。
すべての実行が失敗するという主張ではありません。

## `mode!` が使うもの

- `OpTyping` の入れ子パターンが、`Add` に数値が二つ必要であることを表します。
- `Typing` の `via OpTyping: check_op` が、命令単位の判定器を接続します。
- `Seq` の二つ目の前提は、一つ目が求めた出力型を入力に使います。
- `Branch` の二つの前提は同じ出力変数を使います。`eq Shape: shape_dec` が
  両方の出力を比較し、等しい証明か、等しくない証明を返します。
- 再帰は `Code` の部分項だけを検査します。探索順序や暗黙の実行回数上限はありません。

## 実行器との証明

`proof/safety.taut` はマクロの保証を実行器の振る舞いにつなぎます。

- `run_safe`：任意の型付けされたプログラムと、その入力型に合うスタックについて、
  **実際の `run` が成功し、出力型に合うスタックを返す**。
- `run_never_stuck`：その実行がスタック不足や型違いを表す `None` にはならない。
- `checked_run_safe`：検査を経由した `check_and_run` についても同じ性質が成り立つ。
- `output_unique` と `checker_contract`：元の `Typing` に対して、生成した一意性と判定の契約を取り出す。
- `rejected_refutes`：拒否結果から任意の出力型の導出を反証する。

これらの定理は公理を使いません。`proof/examples.taut` は具体的な計算結果を
`Refl` で検査し、不正なプログラムの型付けが存在しないことも証明します。

## 実行と検査

リポジトリのルートで実行します。

```sh
cargo run --locked -p tauto-cli --bin tauto -- check --tote examples/stack-check --fresh
cargo run --locked -p tauto-cli --bin tauto -- run --backend eval --tote examples/stack-check
cargo run --locked -p tauto-cli --bin tauto -- test cases/check/stack-check.eure
cargo test --locked -p tauto-test-suite --test backends -- rust check/stack-check
cargo test --locked -p tauto-test-suite --test backends -- javascript check/stack-check
```

`cases/check/stack-check.eure` が証明と実行結果、偽の導出の拒否を検査します。
前提間の出力の受け渡しは `cases/check/mode-composition.eure` でも検査します。

## 保証の範囲

対象は有限の構文木です。ループ、任意のジャンプ、副作用、入力テキストの解析は含みません。
拒否は反証を持ちますが、失敗位置を説明する診断データは返しません。

証明の対象は、カーネルが読む自然数と純粋な実行器です。抽出による証明の消去と
各実行バックエンドは信頼境界にあり、同じ例の実行結果をケースで比較します。
実行時の自然数には数値表現の上限があり、資源不足や数値のオーバーフローまで
この型安全性の定理が保証するわけではありません。実行例は小さな値だけを使います。
