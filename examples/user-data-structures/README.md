# ユーザー定義の Vec とハッシュ表のモデル

`VecModel` は、先頭から連続して埋まるスロットの上に可変長配列を定義します。
`HT` は、ハッシュ値と要素の組をリストで保持するハッシュ表のモデルです。
スロットの占有条件、配列への追加・取り出し、ハッシュ表の検索・挿入・削除に関する
性質を Tauto の定理として記述しています。

```sh
cd examples/user-data-structures
tauto check
```

| ファイル | 内容 |
|---|---|
| [`src/uhost.taut`](src/uhost.taut) | `UHost` の整数モデルと、32 ビット幅・64 ビット幅の算術ハンドラ |
| [`src/occupancy.taut`](src/occupancy.taut) | スロットの占有状態と付加情報を表す `Occupancy(S, M)` とその法則 |
| [`src/prefix.taut`](src/prefix.taut) | 先頭から連続して埋まる配列の占有条件 |
| [`src/table.taut`](src/table.taut) | 制御バイトを付加情報に持つ表の占有条件 |
| [`src/slots_model.taut`](src/slots_model.taut) | 要素の有無が占有条件と一致する `SlotsModel` と、取得・格納・取り出し・容量変更の操作 |
| [`src/vec_model.taut`](src/vec_model.taut) | `VecModel` の操作と、末尾への追加後にその要素を取得・取り出しできることの証明 |
| [`src/key_class.taut`](src/key_class.taut) | キーの比較とハッシュへの入力を定義するクラスと、等しいキーについての法則 |
| [`src/hash_table_model.taut`](src/hash_table_model.taut) | `HT` の検索・挿入・再構築と、挿入した要素が見つかることの証明 |
| [`src/delete_rule.taut`](src/delete_rule.taut) | 削除の規則と、残る要素の探索を保つことの証明 |
