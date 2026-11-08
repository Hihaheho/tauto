# 増分計算：whale と query-flow

`totes/whale` と `totes/query-flow` は、計算をクエリとして書き、読んだものを実行時に記録して、読んだものが
変わらない結果を使い回す仕組みである。どちらも Tauto で書く。

- **whale**（`totes/whale`）は依存の追跡だけを受け持つ。ノード（キー `K` と中身 `T`）が何をいつ読んだかを持ち、
  ノードがまだ有効かを答える。グラフは値で、操作は新しいグラフを返す。有効性、早期打ち切り、逆辺、循環の
  検出を証明し、公理を使わない（`totes/whale/README.md`「証明」）。
- **query-flow**（`totes/query-flow`）は whale の上で、クエリを走らせ、結果をキャッシュし、asset（外からの入力）を
  扱い、状態を保存先（ディレクトリかメモリ）に保存する。

## クエリと asset

- **クエリ**は、データベース `Db` を受け取って値を返す関数である。走っているあいだに読んだクエリと asset を
  ランタイムが記録する。読んだものが前回から変わっていなければ、キャッシュした結果を返す。
- **asset** は外からの入力（ファイルのテキスト、設定など）で、グラフの葉である。ホストが `resolve_asset` で与えるか、
  ホストが登録した locator が、最初に読まれたときに与える。読み込み中の asset を読んだクエリは止まり、
  `run` は `Suspended` を返す。`pending_assets` が読み込むべきものを返し、ホストが与えてから聞き直す。
- **早期打ち切り**：計算し直した結果が前と同じなら、`changed_at` を進めない。それを読むクエリは計算し直さない。
  同じかどうかは、既定では符号化したテキストの一致で、`output_eq` で関数を与えられる。asset は `asset_eq` で比べる。
  エラーはランタイムの比較関数（既定では常に異なる）で比べる。
- **耐久性**（`Volatile` < `Transient` < `Stable` < `Static`）：クエリの耐久性は読んだもののうち最も低いもの。
  ある段の変更は、その段以下のクエリだけに確かめ直しを求める。
- **エラー**：`Db::fail(db, e)` で終えたクエリのエラーは、値と同じくキャッシュされる。読んだクエリのエラーは
  `Db::query` で伝わり、`Db::try` で受け取れる。`Db::cancel(db)` で終えたクエリと、循環（`Cycle`）、読み込み中（`Suspended`）、
  走っているあいだに読んだものが消えた場合（`DependenciesRemoved`）は、キャッシュしない。

### 書き方

```
@query!(Add) => fn Add
fn add(db: Db, a: i64, b: i64): i64 ! {halt, Div} { a + b }

@query!(Tagged { keys: [a] }) => fn Tagged
fn tagged(db: Db, a: i64, note: Text): i64 ! {halt, Div} { a }

@asset_key!(Source { asset: Text }) => fn SourceFile::codec, fn Source
pub struct SourceFile { path: Text }

@asset_key!(Labeled { asset: Text, keys: [path] }) => fn LabeledFile::codec, fn Labeled
pub struct LabeledFile { path: Text, label: Text }
```

- `@query!(Add)` は、関数の最初の引数をデータベース、残りをキーとして、`fn Add(a: i64, b: i64): Query(i64)` を作る。
  `@query!(Add { output_eq: f })` は出力を `f` で比べる。
- `keys: [a, …]` は、挙げた引数だけをキーにする。ほかの引数は関数に渡るが、クエリを区別しない（`Tagged(1, "x")` と
  `Tagged(1, "y")` は同じクエリで、先に計算した結果を使う）。
- `@asset_key!(Source { asset: Text })` は asset のキーの型にする `struct` に付け、`fn Source(): AssetKind(SourceFile, Text)` と
  `fn SourceFile::codec(): Codec(SourceFile)` を作る。値は `asset` の型である。フィールドには名前を付け、struct は
  パラメータを取らない。`asset_eq: f` で値を `f` で比べる。`keys: [path, …]` は、挙げたフィールドだけで asset を区別する。
  同じ asset を別のキーで名指すと、asset は最後に名指したキーの全体を覚え、`Db::list_asset_keys`・`pending_assets`・
  `pending_assets_of`・locator にはそのキーを渡す。キーの全体はそのプロセスでだけ覚え、保存しない。
- locator は `(Db, K) -> LocateResult(T)` の関数で、`register_asset_locator(rt, Source(), f)` で登録する。`LocateResult::Ready(v, d)` で
  値を与え、`LocateResult::Pending` でホストに任せる。
- キー、出力、asset の値は `Codec` で書き出す。`i64`・`u64`・`Nat`・`Text`・`Bool`・`Unit` と、それらの `List`・`Option` は
  `Codec` に用意があり、それ以外の型 `T` は、その型のファイルが書く `T::codec()` を使う。
- クエリの中では、module `Db` の関数を `Db::query(db, q)` の形で呼ぶ：`query`（値。エラーは伝わる）、`try`（値かエラー）、
  `asset`（読み込み中なら止まる）、`asset_state`（読み込み中なら `None`）、`list_asset_keys`（種類のキーの一覧。増減で計算し直す）、`fail`、`cancel`。
- 外からは `run`・`poll`（答えと、結果が最後に変わったリビジョン）・`changed_at`・`invalidate`・`remove_query`・
  `remove_query_if_unused`・`clear_cache`・`resolve_asset`・`resolve_asset_error`・`invalidate_asset`・`remove_asset`・
  `pending_assets`・`pending_assets_of`・`has_pending_assets` を使う。`build_runtime` はエラーの比較関数とトレーサーを受け取る。
  トレーサーは `Event`（クエリの開始、キャッシュの使用、実行、停止、循環、asset の解決・無効化、locator の実行）を受け取る。

### キーとグラフ

グラフのキーはテキストで、先頭の一文字が種類を表す。クエリは `q`、asset は `a`、asset の種類のキーの集合は `s` で、
続けて名前（クエリの名前、asset の種類の名前）と符号化した引数（`keys` を書いたときは挙げたものだけ）を、長さつきのフィールド（下の「フィールド」）で書く。
whale のノードの中身は `Slot` で、asset の状態（読み込み中、値、エラー）、クエリの結果（出力かエラー、どちらも符号化した
テキスト）、無効化したクエリのどれかである。

計算し直すときは、読んだものを読んだ順に最新にし、どれかが読んだときより後に変わっていれば計算し直す（whale の
有効性）。クエリの計算の仕方（runner）は、そのプロセスで一度走らせたときに覚える。

## 保存先

`save(rt)` と `load(rt)` は、query-flow の effect（`src/storage.taut`）だけを使い、ファイルシステムの effect を直接は使わない。

- `store_read(name): Option(Bytes)` は、名前 `name` の項目の全体を返す。なければ `None`。
- `store_replace(name, b): Result(Unit, Text)` は、項目 `name` を `b` に一度に置き換える。後の `store_read` は古い項目か
  新しい項目の全体を見て、書きかけのものは見ない。エラーはハンドラのメッセージである。

`save` は項目 `state.qflow` を状態（下の「ディスクの形式」）で置き換え、`load` はそれを読む。項目がどこにあるかは
ハンドラが決める。tote は二つのハンドラを持つ。

- `with_dir_store(dir, body)`（`src/storage_fs.taut`）：項目 `name` はファイル `dir/name` である。置き換えは、`dir` を作り
  （`fs_create_dir`）、`dir/name.tmp` に書き（`fs_write_bytes`）、`fs_rename` で `dir/name` に置き換える。読み込みは
  `fs_read_bytes` で、読めないファイルは項目なしとして読む。
- `with_memory_store(m, body)`（`src/storage.taut`）：項目は `MemoryStore` `m` が持つ。ファイルシステムのない環境
  （ブラウザなど）と試験で使う。`MemoryStore::get`・`set`・`remove` で中身を読み書きできる。

## ディスクの形式

項目 `state.qflow` の中身の形式である。

### フィールド

ファイルは UTF-8 のテキストで、フィールドの並びである。フィールドは、中身のバイト数を十進で書き、`:`、中身の順に
書く（`5:hello`）。中身に何が含まれても、並びは一通りに読める。

### 並び

```
"query-flow" "1" 検査和 本体…
```

- 最初の三つのフィールドは、形式の名前 `query-flow`、版 `1`、本体の検査和（十進）である。検査和は、本体の
  フィールドを並べたテキストのバイト列の FNV-1a（32 ビット）である。
- 本体は、リビジョンの段の数（4）とその数だけの段のカウンタ、続いてノードの数とその数だけのノードである。
- ノードは次のフィールドの並びである。
  1. キー
  2. 中身の種類と値：`L`（読み込み中の asset）、`R` と値（asset の値）、`F` とエラー（asset のエラー）、`O` と出力
     （クエリの出力）、`E` とエラー（クエリのエラー）、`C`（無効化したクエリ）
  3. 耐久性、`verified_at`、`changed_at`、段（level）の四つの数
  4. 読んだものの数と、その数だけの（キー、読んだときの `changed_at`）
  5. 読む側（dependents）の数と、その数だけのキー

### 読み込みの規則

- 項目がなければ `NoState` で、ランタイムは変えない。
- 名前・版・検査和が合わない、フィールドとして読めない、余りがある、段の数が 4 でない、同じキーが二度ある、
  ノードがないキーを読んでいる、のどれかなら `Discarded(理由)` で、ランタイムは変えない。版を変えた形式の
  項目は捨てて計算し直す。
- 読めたら、グラフを置き換え、すべての段のカウンタを一つ進める（読んだ結果は、このプロセスではまだ確かめて
  いない）。値かエラーを持つ asset は、ホストが確かめるまで未確認とする。
  - ホストが `resolve_asset` で同じ値（`asset_eq` による）を同じ耐久性で与えると、asset の `changed_at` は変わらず、
    それを読んだ結果は有効のまま使える。違う値なら変更で、whale の規則で読んだものが計算し直される。
  - locator のある種類は、読まれたときに locator が与え直し、同じ規則で比べる。
  - 未確認の asset を読むクエリ（と、それを確かめようとするクエリ）は止まり、asset は `pending_assets` に入る。
- 読み込んだ直後は、クエリの計算の仕方（runner）をまだ知らない。runner のないクエリは、読んだものが変わって
  いなければそのまま有効で、変わっていればそれを読むクエリが計算し直す（そのとき runner を覚える）。

## 未決定

- 実行時の状態は一つのスレッドから使う。複数のスレッドから同時にクエリを走らせる形は持たない。そのため、実行中に
  asset が解決されたことを検出する仕組み（`InconsistentAssetResolution`）はない。
- `keys` で一部のフィールドをキーにした asset の、キーの全体は保存しない。読み込んだ直後は、そのプロセスで名指されて
  いない asset のキーを `Db::list_asset_keys` などが返さず、locator は呼ばれない（asset は読み込み中のまま、ホストが与える）。
- エラーは `Text` で、型ごとに取り出す形（`downcast_err`）は持たない。
- 保存は全体を一つの項目に書く。変わったノードだけを書く形は持たない。
