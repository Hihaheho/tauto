# whale

インクリメンタル計算のための依存の追跡。ノード（キー `K` で呼ぶ計算。中身 `T` は使う側が決める）が何をいつ読んだかを記録し、そのノードがまだ有効かを答える。計算そのものや結果の置き場所は持たない。依存は std だけ。

グラフは値で、操作はどれも新しいグラフを返す。古いグラフを持っていれば、それはそのまま一貫したスナップショットになる。

```
let w = Whale::new(3)                                     // 耐久性の段は 3 つ
let w = put(w, a, 0, Nil)                                // a は入力
let w = put(w, b, 0, Cons(a, Nil))                       // b は a を読む
Whale::valid(w, b)                                        // yes
let w = put(w, a, 0, Nil)                                // a を書き直すと
Whale::valid(w, b)                                        // no
Whale::confirm_unchanged(w, b, Cons(a, Nil))              // b を計算し直して同じなら、また有効
```

（`put` は `Whale::register` の結果からグラフを取り出す補助。`examples/basic.taut` にある。）

## 考え方

- **耐久性**（durability）: 段 0 が最も変わりやすく、上の段ほど変わりにくい。リビジョンは段ごとのカウンタの列で、段 0 のカウンタはどの変更でも一つ進む時計、段 `d` のカウンタは `d` 以上の段で最後に変わったときの時計。段 `d` の変更は時計を進め、0〜`d` のカウンタをその時計にする。`verified_at` も `changed_at` も同じ時計で測るので、ノードの段が書き直しで変わっても、前に読んだノードとの比べ方は変わらない。ノードの耐久性は、頼んだ段と読んだノードの耐久性の最小になる（変わりやすいものを読むノードは安定を名乗れない）。
- **有効性**: ノードは、自分の段のカウンタが `verified_at` 以下なら有効（その段以下で何も変わっていない）。そうでなくても、直接読んだノードの `changed_at` が読んだときから増えていなければ有効。検査は浅いので、読む側を問う前に読まれる側を最新にしておく。
- **早期打ち切り**（early cutoff）: 計算し直して値が同じなら `Whale::confirm_unchanged` を呼ぶ。`verified_at` だけを上げ `changed_at` は残すので、それを読むノードは有効なまま。値が変わったなら `Whale::confirm_changed`。どちらかを比較関数で決めるのが `Whale::update`。
- **逆辺**: 各ノードは自分を読むノードの一覧を持ち、書き込みのたびに付け替える。`Whale::remove_if_unused` は誰にも読まれていないノードだけを外す（GC 用）。`Whale::has_cycle` は読みの連鎖が自分に戻るかを調べる。

## API（`src/Graph.taut`）

| 関数 | 内容 |
| --- | --- |
| `Whale::new(levels)` | 空のグラフ（段は 1 以上） |
| `Whale::register(w, k, x, dur, ids)` | `k` を `ids` を読むノードとして置く。変更として数え、`verified_at = changed_at` = 新しいカウンタ |
| `Whale::confirm_unchanged(w, k, ids)` / `Whale::confirm_changed(w, k, ids)` | 計算し直した結果を記録（読んだものも取り直す） |
| `Whale::update(w, k, x, differs, dur, ids)` | `differs(old, new)` で変更かどうかを決めて書く |
| `Whale::get_or_insert(w, k, x, dur, ids)` | あればそれを、なければ登録して返す |
| `Whale::valid(w, k)` / `Whale::valid_at(w, k, r)` / `Whale::verified_at(w, k, r)` / `Whale::mark_verified(w, k, r)` | 有効性の判定と、検証済みの印（`verified_at` は下がらない） |
| `Whale::remove` / `Whale::remove_if_unused` / `Whale::has_cycle` | 削除、GC、循環の検出 |
| `Whale::get` / `Whale::get_data` / `Whale::keys` / `Whale::dependency_ids` / `Whale::revision` / `Whale::bump` | 読み出しとリビジョン |

書き込みは、読むと言われたキーにノードがなければ何もせず `absent(keys)` を返す。成功は `done(…)`。

## 証明

- `src/Revision.taut`: カウンタは下がらない（`Revision::bump_mono`）、段 `d` の変更は `d` より上の段に触れない（`Revision::bump_above`）、段 `d` があればそのカウンタは前の時計を越える（`Revision::bump_at`）。だから変更で書いたノードの `changed_at` は、段がどれでも、それより前に読んだ側が覚えている値より大きい。
- `src/Laws.taut`: どのキーの順序（`Ord`）でも置いた値がそのキーで読め、他のキーは変わらない。API の各操作について、書いたノードは有効（`register_valid`・`changed_valid`・`update_valid` など）、データと `changed_at` の値、他のノードは不変（`*_other`）、変更なしの確認は `changed_at` を保ち依存側を有効のまま残す（早期打ち切り、`unchanged_readers`・`update_unchanged_readers`）、存在しない依存があれば何も変えず拒否する（`*_refused`）、削除・未使用時の GC、検証済みの印の単調性。
- `src/Cycle.taut`: `Whale::has_cycle` は依存グラフに循環があるとき、かつそのときに限り yes を返す（`has_cycle_sound`・`has_cycle_complete`、鳩の巣原理による）。
- `src/Reads.taut`: 記録される読み取りはすべて新鮮で、要求した依存の id と一致する。耐久性は要求値と読んだノードのどれ以下、段は読んだノードのどれより上。
- `src/Edges.taut`: 逆辺。登録したノードは、読む各ノード（存在するもの）の dependents に入る（`register_links`・`store_links`）。もう読まないノードの dependents からは外れ（`store_unlinks`）、削除したノードは読んでいた各ノードの dependents から外れる（`remove_unlinks`）。
- `examples/basic.taut`: 具体的なグラフでの早期打ち切りの連鎖、耐久性（段を変えて書き直した入力を読む側が無効になることも）、拒否、逆辺、GC、循環をカーネルの計算で確かめる。

公理は使っていない（`tauto check --json` で確認）。

## 検査

```sh
tauto check --tote .
tauto lint src/*.taut examples/*.taut tests/*.taut
tauto fmt --check src/*.taut examples/*.taut tests/*.taut
tauto test .
```

`examples` と `tests` は追加のソース（`package.additional-sources`）で、`tauto check --tote` が一緒に検査する。
