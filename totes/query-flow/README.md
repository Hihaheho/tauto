# query-flow

Tauto で書く増分計算のライブラリ。クエリの結果をキャッシュし、読んだクエリと asset が変わったときだけ計算し直す。
依存の追跡は [`whale`](../whale) が受け持ち、状態は保存先（ディレクトリかメモリ）に保存して別のプロセスで使い回せる。
設計と、ディスクの形式は `docs/design/query-flow.md` にある。

```
@query!(Add) => fn Add
fn add(db: Db, a: i64, b: i64): i64 ! {halt, Div} { a + b }

let rt := new_runtime()
run(rt, Add(1, 2))                 // Value(3)
```

## ファイル

- `src/codec.taut`：値をテキストに書き出し、読み戻す `Codec` と、長さつきのフィールド
- `src/flow.taut`：ランタイム（クエリの実行、asset、無効化、トレーサー）
- `src/api.taut`：型つきの面（`Query(T)`、`AssetKind(K, T)`、`Db::query`・`Db::asset`・`run`・`resolve_asset` など）
- `src/macros.taut`：`@query!` と `@asset_key!`
- `src/store.taut`：`save` と `load`
- `src/storage.taut`：保存先の effect（`store_read`・`store_replace`）と、メモリに置くハンドラ `with_memory_store`
- `src/storage_fs.taut`：ディレクトリに置くハンドラ `with_dir_store`
- `tests/`：`perform test` の試験

## 検査

```sh
tauto check --tote .
tauto lint src/*.taut tests/*.taut
tauto fmt --check src/*.taut tests/*.taut
tauto test .
```
