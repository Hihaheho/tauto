# JavaScript host 境界の寿命

## 実行境界

`javascript-backend.md`「Host bindings」の extern は、値と Promise を返せる。
直接渡した Nib callback は host から呼べるが、値渡しでも登録元の extern 呼出しの
寿命に制限される。`javascript.retain` に挙げた extern の callback だけは、所有者の
host 値が解放されるまで呼べる（`javascript-host-types.md`「Kept callbacks」）。借用 callback と借用参照を呼出しの外で使うことはできない。
Promise が未完了の呼出しで callback を使う構成と、呼出しを終えてから callback を
保持する構成は別である。前者と、host のイベントを待って Nib 側で処理する構成は、
呼出しを越える callback 所有権を必要としない。

Rust/Wasm 境界の owned callback は、`javascript-backend.md`「Rust externs
through Wasm」の規則に従う。JavaScript extern の callback を後から呼べるという
保証ではない。どの境界でも、借用の寿命や native frame の再開回数を緩めない。

host の例外と Promise の rejection は `run` の失敗になる。回復する失敗は、host
binding が `Result` を返し Nib で扱える。通常の式の列は、途中の失敗後に残りの式を
実行しない。所有値の解放は任意の Nib 後処理の実行とは異なり、Nib のデータ型には
ユーザー定義の Drop がない。host 資源の後処理は host 型の release binding が担い、
通常の終了、中断する効果、`run` の失敗、instance の終了のどれでも一度だけ走る。

Nib の値の後処理は、後処理の関数を呼ぶことである。後処理が欠かせない値は
`linear` にする。linear の値はすべての経路でちょうど一度使われ、中断しうる効果
（`0`、`<=1`、`ω`）を跨いで持てないので、後処理を通らない経路は型検査で拒否される。
後処理自身の効果、失敗、停止は通常の関数呼出しと同じ規則に従う。値を作る式と
後処理を対にする専用の構文はない。

待機の取消は host 型の値（取消の印）と、`Result` を返す async extern で表す。
取消は、その印を受け取った extern 呼出しの待機だけを終わらせ、その呼出しは
取消を表す `Err` で完了する。結果と取消が競合しても、Promise は一度だけ決着し、
Nib は先に決着した一方だけを受け取る。取消しても終わらない待機は host の責務で、
Nib は完了の値を待ち続ける。

`program.mjs` の公開入口は `run` と `instantiate` である。`instantiate` は
`javascript.exports` に挙げた関数だけを instance の method として公開する
（`javascript-host-types.md`「Exports」）。実行時コードの変換は、トップレベルの文と
`javascript.exports`・`javascript.chunks` の入口から到達する関数を対象にする。
マクロの展開でだけ使う関数は、この到達範囲に含まれない。各呼出しの局所変数、handler、ステップ予算は
独立している。method の host 型の引数と結果は instance の handle に属し、関数の
引数は借用で method の呼出しの間だけ、関数の結果は instance の終了まで呼べる。
`javascript-backend.md`「Type declarations」の宣言生成は、この入口と extern
境界を記述する。内部の継続形式の関数を通常の host callable として扱わない。

`javascript.types` に挙げた型の値は host object を handle に保つ
（`javascript-host-types.md`「Host types」）。それ以外の型について、任意の host
object を Tauto のデータ constructor と同じ表現だと仮定することはできない。
