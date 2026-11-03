# エフェクトを使う処理の証明

## 例：古い結果が新しい結果を上書きしない

A の読み取り開始 → B の読み取り開始 → B が `20` を返す → A が `10` を返す。
最後の表示値は `20` のまま、という小さな例です。

- `src/policy.taut`：実際に実行する純粋な状態遷移と、その証明。
- `src/main.taut`：`start_read` / `read_completed` という代数的 effect と handler。
  handler は別実装を書かず、証明した **同じ `complete`** を呼びます。

## 証明していること

`Resource` は「現在の世代」と「表示値」を持ちます。
`begin` は世代を進め、`complete` は応答の token が現在の世代に一致したときだけ値を更新します。

1. **`stale_ignored`**：任意の状態・token・値について、token が現在の世代と異なるなら、
   `complete` は**状態全体を変えない**。
2. **`current_accepted`**：現在の token なら、指定された値に更新する。
   「全部無視すれば安全」という空疎な実装ではありません。
3. **`late_cannot_replace_current`**：新しい結果を反映した後に古い結果が届いても、
   新しい結果が残る。最初の二つの定理を合成した一般的な命題です。

`stale` 引数は `token ≠ generation(state)` の証拠です。
証明では token 比較を場合分けし、不一致なら反射律、一致なら仮定と矛盾することを示します。
特定の `1` と `2` についてだけのテストではなく、任意の自然数について検査されます。

## 実行

インストール済みの CLI を使うか、`TAUTO` に手元の CLI のパスを指定してください。
checkout のルートで：

```sh
TAUTO=./target/debug/tauto
TAUTO_CACHE=off "$TAUTO" check examples/effect-proofs/src/policy.taut --fresh
TAUTO_CACHE=off "$TAUTO" run --tote examples/effect-proofs
TAUTO_CACHE=off "$TAUTO" build --backend javascript --target node -o target/effect-proofs-js examples/effect-proofs
node target/effect-proofs-js/main.mjs
```

JavaScript 版を実行する場合だけ Node が必要です。
証明と実行結果の回帰ケースは `cases/check/effect-proofs.eure` にあります。
`tauto test cases/check/effect-proofs.eure` で両方を検査できます。

拒否テストを試すなら、コピーした `policy.taut` の `complete` の `false => state` を
`false => Resource::Mk(generation(state), value)` に変えて `check --fresh` してください。
古い応答も採用するこの変更は `stale_ignored` に拒否されます。
逆に `true` の腕を `true => state` にすると `current_accepted` が拒否します。
どちらも `tauto extract FILE` で拒否されます。

## 保証の境界

**証明の対象は純粋な `complete` とその合成です。`perform` / handler 自体の実行意味論を
定理にしているわけではありません。** handler の代入・継続再開・抽出・各 backend は信頼境界です。
handler の代入を無条件上書きに変えると、純粋な証明は通ったまま最終値が `10` になります。

これは非同期完了通知の順番を再現する小さな driver で、実際の通信や並行 scheduler は実装しません。
到着保証、失敗処理、キャンセル、任意の multi-shot handler の安全性も証明していません。
本番との接続では、すべての更新がこの遷移を通り、応答 token が対応する開始時のものだと保証する必要があります。

証明中の `Nat` は非有界ですが、実行時には `u64` になります。
実行時にこの解釈を保つには、各開始前の世代が `2^64−1` 未満で、token を再利用しないことが必要です。
この例は二回だけ世代を進めるので範囲内です。一般のカウンター周回への対処は含みません。
