# tauto の self-host（Rust バックエンドに関係しない部分）

tauto のコンパイラの大部分を tauto で書き直す方針と、その構成。部品は tote（`totes/`）にまとめ、
kernel が検査する全域な層（`inductive` と total な `fn`）で書き、要所に正しさの定理を付ける。
各 tote の README が振る舞いを、`crates/tauto-selfhost` の試験が Rust の実装との一致を示す。

## 方針

| 項目 | 方針 |
| --- | --- |
| 何を書くか | Rust バックエンドを使わずに進められる部分だけ（「構成」）。実行は `eval.rs`（インタプリタ）で、遅くても正しければよい |
| どこまで証明するか | 全域性と型（kernel が検査し、止まり、網羅的）に加え、要所の正しさの定理。全関数の仕様は書かない。ただし `totes/nibcheck` は検査器全体の健全性まで示す（「nibcheck の健全性（`totes/nibcheck/src/`）」） |
| kernel | **変えない**（`check.rs`、`check/core.rs`）。精密化の糖衣（「精密化の糖衣」）は kernel の外にあり、kernel と `check/core.rs` が受け取る項の形は糖衣なしで書いたときと同じ |
| 実行 | **Nib への extraction**（「extraction（`crates/tauto/src/extract.rs`）」）。生成した Nib が `eval.rs` で動き、[`rust-backend.md`](rust-backend.md) でネイティブにもなる |
| OS IO | **薄い Nib の殻**として残す（「殻」） |
| 確かめ方 | 同じ入力を Rust の実装と tauto の実装に与えて出力を比べる差分試験（「差分試験」）。比べる相手の Rust の実装は変えない |
| builtin | 最小にする。Nib で書けないものだけ（バイトを読む、文字列を作る、数の幅を変える、OS）。どの builtin も `tauto-rt` が実装する |

## 構成

| Rust の部品 | tote |
|---|---|
| —（基本の道具） | `totes/text`、`totes/unicode`、`std/Map.taut`（ordmap） |
| `crates/tauto/src/fmt.rs` | `totes/fmt` |
| `crates/tauto-parol`（字句・構文解析、`cst.rs`） | `totes/scan`、`totes/llk`、`totes/syntax`（「構文」） |
| 文法の表の生成（`tools/tauto-parol-gen`） | `totes/llkgen`（[`macro-implementation.md`](macro-implementation.md)「`totes/llkgen` と表のファイル」） |
| `crates/tauto-surface/src/surface.rs`、`surface/program.rs` | `totes/surface` |
| `crates/tauto-surface/src/macros/scope.rs` | `totes/macros` |
| `crates/tauto-nibcheck/src/types.rs`、`rows.rs`、`lin.rs` | `totes/nibcheck` |
| `tauto-rt`、`tools/tauto-parol-gen` | Rust のまま（後者は Rust の表の生成器を動かす道具なので。`totes/llkgen` が同じ表を作る） |

依存は一方向で、循環は tote の読み込みが拒否する。

```text
text ─┬─ fmt
      ├─ scan ── llk ── syntax ── surface
      │                              └────── nibcheck
      └─ （すべての tote が text を使ってよい）
```

```sh
tauto run --steps 1000000000 --tote totes/fmt -- ARGS…    # tote を eval で走らせる
cargo test --locked -p tauto-selfhost                      # 差分試験と証明
```

## 全体の形

```text
totes/<name>/src/*.taut   型・関数・定理・実行コード
totes/<name>/src/main.taut 実行の入口
std/*.taut                標準ライブラリ
```

`totes/` のソースは `.taut` に統一する。定理も同じソースに置き、独立した
`proof/` ディレクトリは使わない。定理と実装を同じファイルに書いても、別の
モジュールに分けて import してもよい。

`tauto run --tote DIR` と build は同じ読み込みを使う。依存 tote が先、各 tote
のソースはパスの辞書順、`main.taut` は最後。依存 tote の main は読み込まない。
import 先は先に読み、同じファイルは一度だけ読む。

検査と実行の境界は宣言ごとに決まる。実行用の型・関数・効果を使う関数と
トップレベルの実行文は実行側の検査に渡し、証明の仮定にはしない。
それ以外の関数・帰納型・定理は二つのカーネルで検査する。検査失敗を
実行コードとして再試行しない。証明に穴・公理・失敗があれば tote を拒否する。

検査した関数は実行用の表現に変換し、実行コードと合わせる。tote 自身の関数で
入出力が実行用の型で表せるものは、外部からも呼べるように残す。定理と、実行から
使われない証明専用の補助関数は出力しない。生成物はソースとして保存しない。

## コードを書くときの規則

1. 関数・型・効果の名前の先頭に tote の名前を付ける（`scan_next`、`LlkStack`、`text_split`）。名前は略さない。
   Rust の実装に同じ役の名前があれば合わせる。
2. 移植は Rust の関数一つに tauto の関数一つを対応させ、名前も合わせる。差分試験が落ちたときに読み比べられる。
   `HashMap` の反復順に Rust の側が頼っていないかを確かめる。
3. 証明側の名前は Nib std の関数名（`map`、`fold`、`concat` など）と重ならないようにする（extraction の出力で衝突するため）。
4. 関数を struct のフィールドに入れて呼ばない（`rows.rs` が拒否する）。比べる関数などは借用閉包の引数で渡す。
5. `Text` の大小は `text_compare` で比べる。失敗しうる関数は `Result(T, E)` か `Option(T)` を返す。
6. `match` に `_ =>` の既定の腕を書かない（コンストラクタを足したとき黙って吸収されるため）。
7. 殻（Nib）の文字列リテラルにバックスラッシュと `"` を書かない。改行・タブ・引用符は `text_of_code_point(10)` のように作り、
   名前の付いた関数にする。

## 精密化の糖衣

糖衣は、カーネルが糖衣なしで書いたときと同じ項を受け取るものに限る（カーネルに規則を足さない）。どれも
`check/matching.rs`（精密化）か `check/sugar.rs` にあり、結果は kernel と `check/core.rs` が検査し直す。
ケースは `cases/check/programs.eure`。

1. **fn のジェネリクス。** `fn len<A>(l: List(A)) -> Nat` の `A` は `theorem` の `<A>` と同じく
   型 `Type` の暗黙引数。
2. **項の中の `match`。** 引数や関数の本体の中に `match` を書ける。
3. **式への `match`。** `match nat_lt(a, b) -> Nat { … }` は、新しい変数 `x` についての `match` を
   作り、`x` に式を代入したもの。場合分けだけで、式の欄への呼び出しは再帰にならない。
   定義中の関数への呼び出しを式に書ける（`match even(k) -> Yn { … }`）。それは腕の外で帰納法の仮定になる。
4. **テキストのリテラル。** `std/Text.taut` が `inductive Text { text(bytes: List(Nat)) }` を宣言した後は、
   `"ab"` を `text(Cons(Nat, 97, Cons(Nat, 98, Nil(Nat))))`（UTF-8 のバイト列）と読む。
5. **演算子。** `std/Base.taut` が `nat_add` と `Yn` を宣言した後は、
   `-` を `nat_sub`、`a < b`・`a <= b` を `nat_lt(a, b)`・`nat_le(a, b)`、
   `a > b`・`a >= b` を引数を入れ替えた `nat_lt`・`nat_le`、`&&`・`||`・`!` を `yn_and`・`yn_or`・`yn_not` と読む。
   `+`・`*` は読み替えず、どこでも kernel 組み込みのまま（`nat_add(a, b)`・`nat_mul(a, b)` はその別名で、
   `a + b`・`a * b` と定義上等しい）。`+` は第1・第2引数のどちらでも、`*` は第1引数で簡約する。
6. **レコード。** コンストラクタが一つの族 `T` について、`T { f: e, … }` はそのコンストラクタを
   フィールドの順に適用したもの。パターン `T { f: p, g }` も同じ（書かないフィールドは `_`、
   名前だけのフィールドはその名前を束縛する）。extraction もこの書き換えだけは読む。
7. **フィールド、等号、`let`。** コンストラクタが一つの族の値 `x` について `x.f` はそのフィールドを取り出す
   `match`。`a == b` は `a` の型で `nat_eq`・`yn_eq`・`text_eq` のどれかになり、`a != b` はその `yn_not`。
   型注釈なしの `let x = e` は、`x` を `e` で置き換えたもの。extraction は `x.f` を `match`
   （`Pair` は Nib の `.fst`・`.snd`）、`==`・`!=` を Nib の同じ演算子にする。
8. **ラムダの引数の型。** 関数型の引数に書いたラムダは、その型の定義域（閉じていれば）を引数の型として持つ。
   それでラムダの本体の `match` がその引数について書ける。
9. **入れ子の `match` の一般化。** 腕の中の入れ子の `match` は、外の `match` で型が変わった仮定
   （`h: P(Cons(e, rest))`）を一般化する。
10. **暗黙引数の再精密化。** 暗黙引数を持つ呼び出しの引数がそれ自体暗黙引数を持つとき、後で分かった型で
    もう一度精密化する。
11. **`mutual` の fuel。** 「停止性の書き方」。
12. **`&mut` と `var`。** 「`&mut` と `var`」。

### `&mut` と `var`（`crates/tauto-kernel/src/check/mutable.rs`）

状態を持ち回るコードを、Nib の形のまま証明言語に書くための糖衣。書き換えは構文だけで、結果は
kernel と `check/core.rs` が検査する。extraction は書かれたままを読み、元の `&mut` の Nib を出す。

* `fn f(&mut c: C, x: A) -> R` は、`fn f(c: C, x: A) -> Mut1(R, C)` と読む。`MutK(R, S1, …, SK)` は
  コンストラクタ `mutK(value': R, s'1: S1, …)`（プログラムが書けない名前のフィールド）を一つ持つ族で、使われたときに宣言される。`&mut` 引数が
  複数あれば、書いた順に並ぶ。定理では `f(counter(0, 0)) = mut1(v, c')` のように、値と最後の状態を語る。
* 本体では、状態（`&mut` 引数と見えている `var`）を名前で持ち回る。呼び出し `g(&mut x, &mut y.f, e)` は
  `match g(x, y.f, e) { mut2(v, x, t) => … }` で、`y` はフィールド `f` を `t` にして作り直す。
  `x := e` と `var x = e` は `match mut0(e) { mut0(x) => … }`（`let` と違い、項を複製しない）。
* 状態を変える `match`（と `if`。`yes`・`no` への `match`）は、関数の最後なら各腕がそのまま関数を終える。
  途中なら状態全部を `mutK(v, …)` で返し、続きがそれを取り出す。このとき値の型が要る: 文としての
  `match` は `()`、`let x: T = match …` か `match e -> T` で書く。`var` も型を書く。
* 引数は書いた順に評価する。後の引数が状態を変えるなら、先に読んだ値を束縛しておく。`&x` は `x`、
  `()` は `star()`（型は `Unit`）。
* `while` や `return` を含む関数は実行用（証明言語の宣言ではない）。ラムダの中では状態を変えられない。
* 除去子の値の型（動機の適用 `(t => Nat)(c)`）を含意引数として推論したとき、頭のラムダを簡約してから
  精密化する。これで `match g(c.n) { … }` のように、フィールドを総称関数へ渡す式に `match` できる。

## extraction（`crates/tauto/src/extract.rs`）

kernel の型から、各宣言の引数が **型・証明・値** のどれかを読む（`check/roles.rs`）。値だけを残す。

| 証明側 | Nib |
| --- | --- |
| `inductive`（`Type` の族、添字なし） | `shared enum`。パラメータはジェネリクス、証明の欄は落とす |
| 構築子が一つの族 | `shared struct`。構築子の呼び出しは `Name { f: v }`、パターンも同じ形。Nib からは `x.f` で読む |
| `Prop` の族、`theorem`、`axiom`、`def` | 落とす |
| `fn` | 型の引数はジェネリクス、証明の引数は落とし、呼び出しの対応する引数も落とす |
| `match x -> T` | `match x`。証明への `match` は腕一つの値。`Nat`・`Yn` への `match` は `if` の鎖 |
| 証明の `let` | 落とす |

**写像の表**（信頼する部分）。`std/` の次の宣言は書き出さず、Nib の型と関数に写す。どれも
`std/` に定義があり、証明はその定義について行う。

| 証明側 | Nib |
| --- | --- |
| `Nat`、`zero`、`succ(n)` | `u64`、`0`、`n + 1` |
| `Yn`、`yes`、`no` | `Bool`、`true`、`false` |
| `List`、`Option`、`Pair`、`Unit` | Nib std の `List`、`Option`、`Pair`（証明が族として読む prelude の宣言そのもの）、`()` |
| `Text` | `Text`（「`std/Text.taut`」の関数） |
| `Array`、`array_of_list`、`array_get`、`array_len`、`array_to_list` | Nib std の `Array` と同名の builtin（「配列」） |
| `Stack` と `stack_*` | Nib std の `Vec` と `vec_*`（「スタック」） |
| `nat_lt`、`nat_le`、`nat_eq`、`nat_sub`、`nat_div`、`nat_mod` | `<`、`<=`、`==`、飽和減算、0 除算は 0 |
| `yn_and`、`yn_or`、`yn_not` | `&&`、`\|\|`、`!` |

**信頼の範囲。** kernel と `check/core.rs`、写像の表、Nib の実行系（`eval.rs`、Rust バックエンド）、殻。
写像のずれは差分試験で見る。**既知の差**：`u64` は 2^64 で溢れて実行時エラーになる
（`Nat` は溢れない）。証明側の値は入力の位置・長さ・数え上げ（入力のバイト数以下で、入力はメモリに載るので 2^64 に届かない）と、
数のリテラルを読んだ値（`totes/text` の `text_parse_u64` は 2^63 以上を `None` にする）なので、この差は出力に現れない。

## 証明側の標準ライブラリ

### `std/Base.taut`

`Yn`、`nat_*`、`list_*`、それらと命題をつなぐ補題。項についての場合分け `ordering_cases(P, e, …)` もここにある：
`P` は場合の値についての `match` を含む関数で、プログラムの本体が `e` についての `match` に
展開されたものが `P(e)` になる。各場合は `e` がその値に等しいという仮定を受け取る。

### `std/Text.taut`

`Text` は UTF-8 のバイト列のモデル。長さ、`i` 番目のバイト、切り出し、連結、比較、数の十進表記を
定義し、表で Nib の builtin に写す。コードポイントの復号は証明側で書く（バイトの算術）。

### 停止性の書き方

構造的再帰で書けないもの（スキャナと構文解析器の駆動ループ、単一化、不動点）は **fuel** で書く。
`fuel: Nat` を最初の引数にして `match fuel` で減らし、尽きたら失敗を表す値を返す。呼び出し側は
入力の長さから十分な fuel を渡し、定理は「fuel が足りれば失敗しない」形で述べる。

互いに呼び合う関数が同じ fuel を分け合うときは、`mutual { fn … }` にまとめ、どれも `fuel: Nat` を
最初の引数にして `match fuel { zero => … succ(j) => … }` と書き、呼び合いには `j` を渡す。フロント
エンド（`crates/tauto-kernel/src/check/steps.rs`）がこの組を、要求の帰納型と答えの帰納型、要求に答える
一つの関数 `F'read`（`fuel` についての構造的再帰）と、それを呼ぶ元の名前の関数に書き換える。
各関数の `zero` 腕は `F'zero'f(a⃗)` という関数になり、呼び出しごとに同じ引数で渡される（答えの型が
違うときの既定値。実際には使われない）。だから `zero` 腕は引数を使ってよい（`&mut` の関数の `zero` 腕は
状態を返すので、これが要る）。カーネルの規則は変えない。例は `cases/check/induction.eure` の
`mutual-functions-can-share-a-step-count`。

### 配列

表（scan の文字分類、llk の遷移表など）は添字で引く。`std/Array.taut` の `Array(A)` は証明側では
リストを包んだもので、`array_get(a, i)` は `list_nth` と定義される。証明はこの定義について行う。
extraction は `Array` を Nib std の `Array`（`std/prelude/Shared.taut`、shared で読むだけの配列）に、
四つの関数を同名の builtin に写す。evaluator では `Value::Array`、
Rust では `Rc<[A]>` で、`array_get` は O(1)。信頼するのは「この builtin がリスト版の定義どおりに
振る舞う」ことで、`Nat` と `u64` の写像と同じ種類の前提である。差分は
`cases/rust/programs.eure` の `arrays-are-shared-and-read-by-index` で見る。

### スタック

解析のスタックやフレームのスタックは、リストの先頭に積むと 1 回ごとにセルを確保する。`std/Stack.taut` の
`Stack(A)` は証明側ではリストを包んだもの（トップが先頭）で、`stack_new`・`stack_push(&mut s, x)`・
`stack_pop(&mut s)`・`stack_len(&s)`・`stack_is_empty(&s)` の定義がその意味を言う。extraction は `Stack` を
Nib の `Vec`（affine）に、五つの関数を `vec_new`・`vec_push`・`vec_pop`・`vec_len` の呼び出しにその場で
展開する（関数としては書き出さない）。実行ではトップが `Vec` の末尾で、積むのも取るのも O(1)、要素ごとの
セルはない。信頼するのは写像だけで、`Array` と同じ種類の前提である。

`Vec` は affine なので、`shared` な構造体のフィールドには入れられない。`&s`・`&mut s` で貸すか、
`var s: Stack(A) = stack_new()` の局所にする。名前の `stack` はコンストラクタ（`stack_of`）と衝突しない。
使い方は `totes/llk`（パーサのスタックとイベント）と `totes/syntax`（CST のフレーム）にある。イベントは
積んだ順の逆に取り出すので、CST は最後のイベントから組む。

## 殻

殻（`src/main.taut`）は `os_args` で引数を、`os_read_file` で入力を受け、証明側の純粋な関数を一度
呼び、結果を `os_print`・`os_eprint` で書くだけにする。殻の行数は tote ごとに数十行に収め、
人間が目で確かめる。OS の builtin は `std/prelude/Os.taut`、テキストと数の builtin は `std/prelude/Text.taut`、`std/prelude/Num.taut`。

## 差分試験

`crates/tauto-selfhost` が共通の道具を持つ。

- `run_tote(name, args, steps)` は tote を eval で走らせる（`load_tote` と `run_program_with` を直接呼ぶ）。
- コーパスのすべての入力を一時ディレクトリに書き、パスの列を `args` で一度に渡す。tote は結果を `== <名前>` の行で区切って一つの標準出力に出す。Rust の側も同じ形の文字列を作り、`assert_same_dump` で比べる。
- 違えば、最初に違う行の前後を並べて失敗する。

## 構文（`totes/scan`、`totes/llk`、`totes/syntax`）

構文は手書きしない。`tools/tauto-parol-gen` が `tauto.par` から作った表を、tauto のデータとして書き出し、それを読む駆動部を tauto で書く。

1. 表の書き出し：`tauto_parol::syntax_tables()` が `generated/parser.rs` の定数を読んで表を作り、`scripts/generate-syntax-tables.sh` が表ごとのデータ `totes/syntax/src/tables/<name>.txt` と、それを `include_text!` で返す関数の `totes/syntax/src/tables.taut` に書く（`--check` で確かめるだけ）。書き出すもの：終端記号と非終端記号の名前、宣言された非終端記号、先読みの最大 k、読み飛ばすトークン、先読み DFA、生成規則（逆順で入っている）、字句のモードと DFA、文字クラス（全 Unicode スカラー値を区間にまとめる）、開始の非終端記号。
2. 静的なデータのリテラルがないので、数を空白で区切った長い文字列（データのファイルの中身）にして tote の中で読む。
3. `totes/scan` は字句の DFA の実行部分（最長一致、優先度、先読み、モードの切り替え）、`totes/llk` は LL(k) の駆動部、`totes/syntax` は表と CST の組み立て。それぞれの README に振る舞いを書く。
4. 差分試験：同じソースから `tauto_parol::parse` と `totes/syntax` が同じ CST を作ることを確かめる。

## 証明（`totes/*/src/`、`std/`）

tote の定理は `totes/<tote>/src/*.taut` に置く。プログラム（`src/`）からは読まれず、
`crates/tauto-selfhost/tests/proofs.rs` が、どの宣言も穴も公理もなく検査を通ることを見る。

### ordmap（`std/Map.taut`、`std/MapLaws.taut`、`std/MapRemoveFloor.taut`）

`std/Map.taut` は順序付きの写像（AVL 木、永続）。木を、その中順のエントリの列
（`ordmap_tree_entries`）で読む。比較関数には全順序であること（`OrdmapLaw`：`cmp(a, a)` が
`equal`、`equal` なら等しい、`less` と `greater` が入れ替わる、`less` が推移的）を仮定する。

* 回転と `ordmap_balance` はエントリの列を変えない（`ordmap_balance_entries`）。
* 列が整列していれば、`ordmap_tree_get` は列の先頭からの探索（`ordmap_list_get`）、
  `ordmap_tree_insert` は整列した列への挿入（`ordmap_list_insert`）に等しい。
* よって `ordmap_insert` は整列を保ち（`ordmap_insert_ordered`）、挿入したキーは挿入した値を持ち
  （`ordmap_get_insert_same`）、他のキーは値を変えない（`ordmap_get_insert_other`）。

`ordmap_compare_nat`（`std/MapLaws.taut`）と `ordmap_compare_text`（`std/MapText.taut`。`text_compare`、
バイト列の辞書式順序）は `OrdmapLaw` を満たす。よって数とテキストをキーにした写像では、上の定理は仮定なしに成り立つ。
同じ写像に違う `cmp` を渡すのは利用者の誤りで、検査しない（クラスを使う写像では
[`classes.md`](classes.md) のインスタンスの一意性がこれを不要にする）。

`std/MapRemoveFloor.taut` は同じやり方で `ordmap_remove` と `ordmap_floor` を示す。

* `ordmap_tree_remove` は列からそのキーのエントリを除くこと（`ordmap_list_remove`）に等しい
  （`ordmap_tree_remove_entries`）。`ordmap_join` は二つの列を繋ぐ（`ordmap_join_entries`）。
* よって `ordmap_remove` は整列を保ち（`ordmap_remove_ordered`）、除いたキーは値を持たず
  （`ordmap_get_remove_same`）、他のキーは値を変えない（`ordmap_get_remove_other`）。
* `ordmap_floor` は、列のうちキーが `k` より後でない最後のエントリ（`ordmap_list_floor`）に等しい
  （`ordmap_floor_entries`）。

### text と unicode（`totes/text`、`totes/unicode`）

文字 `c`（0x110000 未満でサロゲートでない、`text_is_char`）について、
`text_decode(text_of_code_point(c), 0)` は `c` と符号化の全長を返す（`text_decode_of_code_point`、`totes/text/src/utf8.taut`）。
符号化の長さ 1〜4 ごとに示し（`utf8_round_1`〜`utf8_round_4`）、`text_of_code_point` の各段
（`text_utf8_from_128` ほか、証明側に置く。計算だけで本体に一致する）をそれに繋ぐ。
算術は `src/nat.taut`：`nat_add`・`nat_mul` の法則、商と余りの一意性、商の商は積での商（`nat_div_div`）。
`totes/unicode` は Rust の `char::is_alphanumeric`・`char::is_whitespace` と同じ分類を、ASCII は証明側で決め、残りは表（`tables.taut` が `include_text!` で読む `tables/*.txt`）の区間で引く。

* 復号（`text_decode_with`）は積を `nat_mul(64, x)` と書く。`nat_mul` は第二引数で再帰するので、
  未知の `x` に対して展開されない（`nat_mul(x, 64)` だと入れ子の深さに対して 64 の冪で項が膨らむ）。
* カーネルは止まった `match` の腕の下まで正規化するので、大きなリテラルとの比較（`nat_le(55296, c)`）は
  その数だけ深く再帰する。`tauto check` と `proofs.rs` は深いスタック（256MB）のスレッドで検査する。

### scan（`totes/scan/src/longest.taut`）

オートマトンの走りを `scan_walk`（状態から `m` 文字、表の行 `scan_next` で一つずつ遷移）で書き、
走りが一文字以上で着いた状態で受理項目が成り立つ（`scan_accept`、先読みを含む）ところをその走りのトークンとする。

* `scan_find` が返すトークンは走りのトークンである（`scan_find_sound`）。
* 走りのトークンはどれも `scan_find` が返すものより長くない（`scan_find_longest`）。よって
  走りのトークンがあれば `scan_find` は何かを返す。
* 燃料（残りのバイト数）が足りることは、`m + 1` 文字の走りが `pos + m < n` を満たすことから示す
  （`scan_walk_bound`）。

### llk（`totes/llk/src/derives.taut`）

パーサのスタック（上が先頭）を、まだ導出するものとして読む関係 `LlkDerives(t, stack, tokens)` を置く。
非終端記号は表の生成規則のうちその記号を左辺に持つものの右辺（展開する順）と生成規則の終わりに置き換わり、
終端記号は次のトークンの型であり、生成規則の終わりは何も導出せず、空のスタック（か終端 0 だけ）は
次のトークンが入力の終わりであることを求める。

* `llk_run_in` が成功を返せば、そのときのスタックはトークンを導出する（`llk_run_sound`）。
  `llk_parse` が成功を返せば、開始記号がトークンを導出する（`llk_parse_sound`）。
* 先読みがどの生成規則を選ぶかは関係しない。パーサが展開する非終端記号の生成規則しか取らないことは
  関係するので、`llk_run_in` は予測された生成規則の左辺を確かめ、違えば失敗する（生成した表では起きない）。

**`&mut` の関数についての証明の書き方。** 本体の途中で止まる式（`nat_eq(ty, a)`、`llk_predict(…)` など）
ごとに、その続きを最後の引数で受ける関数（`llk_term_at` ほか、同じ書き方の `&mut` の関数）を置き、
仮定を `Eq_subst` で運ぶ。再帰呼び出しは `match` で包み直される（`llk_rewrap`）ので、その恒等を補題にする。
nibcheck の証明も同じ書き方をする。

### surface、syntax、fmt

`totes/surface`（`crates/tauto-surface/src/surface.rs` の移植）、`totes/syntax`、`totes/fmt` は全域性と型までで、
正しさは差分試験で見る。

## nibcheck の健全性（`totes/nibcheck/src/`）

**目標。** nibcheck がエラーを報告しないプログラムは、宣言的に書いた Nib の規則（型、種、クラス、
効果、線形性）のすべてで型が付く。検査器全体の健全性で、要所だけではない。

**規則は検査器と別に書く。** [`nib.md`](nib.md)、[`semantics.md`](semantics.md)、[`ownership.md`](ownership.md)、
[`classes.md`](classes.md) から、検査器を参照しない帰納的な関係として
`totes/nibcheck/src/rules_*.taut` に置く。規則そのものが仕様なので、人間が読んで確かめる対象になる。
検査器が文書より緩いところが見つかれば、規則に合わせて検査器を直すか、文書と規則に書き足す。

**層。** 下の層の定理を上の層が使う。

| 層 | 対象 | 定理 |
| --- | --- | --- |
| 1 型 | `ty.taut` | `ty_compare` が等しいと言えば同じ型（`ty_eq_sound`）。合併とタグの正規化は集合として正しい。置換 `ty_substitute` |
| 2 単一化 | `checker.taut` | 宣言的な型の等しさ `TyEq(σ, a, b)`（変数は σ の束縛と等しい、構造、合併の正規形、`TyApp` の読み）。`ck_unify` が成功すれば σ' は σ を延長し `TyEq(σ', a, b)`。`ck_fits` は宣言的な部分型、`ck_join` はその上界 |
| 3 宣言 | `datas.taut`、`types_decl.taut` | 種の規則、データと関数の宣言がよく形成されている |
| 4 式 | `types_infer.taut`、`types_match.taut` | 宣言的な型付け `Γ ⊢ e : T`（Nib の式すべて）。エラーがなければ導出がある |
| 5 クラス | `types_classes.taut` | インスタンスの解決と `where` の健全性 |
| 6 効果 | `rows.taut`、`direct.taut` | 宣言的な効果の判断。推論した行は規則の上界 |
| 7 線形性 | `lin_*.taut`、`freevars.taut` | [`ownership.md`](ownership.md) の規則。値は高々一度（線形なら正確に一度）使われる |
| 8 全体 | `modules.taut`、`types_run.taut` | `nibcheck` がエラーなし ⇒ プログラムが 1〜7 の規則すべてで型付く |

**燃料。** 検査器の再帰の多くは `steps` の燃料で書かれ、尽きると失敗（エラー）を返す。健全性は
「成功したなら」の形なので、燃料が尽きる場合は自明に成り立つ。燃料が足りることは健全性に要らない。

**`&mut Checker`。** 状態は `Checker` 一つにまとまっている。定理は `mut1(v, c')` の形で値と最後の状態を
語り、本体の途中で止まる式ごとに続きを最後の引数で受ける関数を置く（llk の証明と同じ）。

### 層 1：合併とタグ（`src/union_sound.taut`）

集合として読む（`std/Row.taut` の `Mem`）。順序と重複のなさは示していない。

* 葉（`Leaves`）は合併でも `never` でもない型で、合併の中の葉も数える。`union_mem`・`union_has`：
  `ty_union(ts)` の要素（`ty_members`）はちょうど `ts` の葉で、どれも葉。
* `tags_union_mem`・`tags_union_left`・`tags_union_right`：`tags_union(a, b)` のタグはちょうど `a` と `b` のタグ。
  `tagged_shape`：`ty_tagged` は新しいタグと型自身のタグを合わせて、その下の型に付ける。
* 挿入の内側の `match`（比較の結果で分ける）は、比較の結果を最後の引数に取る関数（`ins_k`）に出して
  `refl()` で等しいことを示す。前の引数にすると `match` がそれらを抽象し、形が合わない。
* 置換 `ty_substitute` について一般の性質は示さない。層 2 の総称の規則は置換した型をそのまま述べ、
  層 3 は `fk_sound` の形（代入した型の種を抑える）で使う。

### 層 2：`ck_unify`（`src/unify_sound.taut`）

`TyEq` の `ok`（`tyeq_poly` の rigid な型が二つの型に出ないこと）は、検査器が `kept` に記録した使い方とする（`KeptOk`）。
記録は終わりの置換でもう一度確かめられる（`ck_check_kept`）。

* `ck_unify_ok`：置換が整列していれば、後の状態は前の状態を延長し（`Grows`：整列、置換の延長、記録の延長）、
  `yes` なら `a` と `b` はその状態で同じ型。
* 燃料 `k` についての帰納（`unify_at`）で、相互再帰の四つ（`ck_unify_in`、`ck_unify_rest_in`、
  `ck_unify_pairs_in`、`ck_unify_app_in`）を同時に示す。`ck_unify_pairs_in` は長さが違うと `yes` を返すので、
  定理は長さが等しいときの `TyEqList`（`TyEqLenAt`）。呼ぶ側はどこも長さを先に比べている。
* 二つの段の続き（`if m { k } else { no }`）は `ck_and(k, m)` と `post_and` で書く。
* ワイルドカードの腕は、どの構成子の代わりかを本体で名指せないので、`a`・`b` に等しい `a1`・`b1` についての
  定理にし（`rest_step_eqs`）、等式の仮定の型が腕ごとに精密化されるのを使う。

### 層 2：`ck_fits`（`src/fits_sound.taut`、規則は `src/rules_ty.taut` の `TySub`）

`TySub` は等しさ、`never`、総称の右（rigid に置いた形が合い、`kept` に記録がある）と左（`bounds` の
新しい変数で具体化した形が合う）、借用（`&mut` は `&` として、借用は値として）、複製できる値を借用として、
合併の左右、タグを忘れること、関数（引数は反変）を規則とする。

* `ck_fits_ok`・`ck_attempt_fits_ok`：状態は延長され（`Grows`。data と kind の bound は変わらないか
  増えるだけ）、`yes` なら `TySub` がその状態で成り立つ。
* 燃料についての帰納（`fits_all`）で、fits の相互再帰の 15 段を同時に示す。各段は、展開の等式を
  一度 `refl()` で示して `Eq_subst` する（`post_unf`）。ワイルドカードの腕は等式の仮定と `post_cases` で書く。
* 入れ子の `match`（一つの型で分けた腕の中で、もう一つの型で分ける）は、ワイルドカードの腕の数が掛け算に
  なり検査が終わらないので、内側を段に分けた（`ck_fits_inst_in`・`ck_fits_lend_in`・`ck_fits_untag_in`・
  `ck_fits_fn_in`）。答えは同じで、燃料を一段多く使う。

### 層 2：`ck_join`（`src/join_sound.taut`）

`ck_join` は二つの枝の型から一つの型を作る（同じ型、`never` でない方、`&A` と `A` なら `A`、それ以外は合併）。

* `ck_join_ok`：状態は延長され、二つの型はどちらも結果の型に `TySub` で合う。
* 合併の場合は `tysub_union_r` と、`ty_union` が合併の正規形であること（`tyeq_union_norm`）で示す。
* `&mut` の脱糖が作る形（`ck_join_my`・`ck_join_k`・`ck_jb2` など）を書き、`refl()` で元の関数と等しいことを
  一度示して、その形について示す。開いた型で `match` が止まる腕は、`opt_cases` で構成子ごとに展開する。

### 層 3：種（`src/kind_sound.taut`）

`kind(T)` の式（[`ownership.md`](ownership.md)）を不等式として示す。最小解はこの不等式を満たすものの中で
最も小さいので、`datas_kind` の答えは文書の種以上、つまり安全側になる。

* `KLe(a, b)` は `kind_join(a, b) = b`。
* `SummaryOk(d)`：どの宣言の要約（`base`・`holds`）も解である。フィールドを足しても増えず、最小の要約
  （宣言した種、再帰なら `shared`、どのフィールドも言及しない総称）から始まっている。
* `kind_field_le`：`SummaryOk(d)` で、`D` の総称すべてに引数があれば、`D` の各フィールドに引数を
  代入した型の種は `kind(D(args))` 以下。`kind_declared_le`・`kind_recursive_le`・
  `kind_unmentioned_le` も同じ形。
* 中心は `fk_sound`。`map` が総称のちょうどそれぞれに型を与えるとき（`MapKeys`・`MapCover`）、
  `field_kind` がフィールドについて言う種と、保持する総称の引数が `k` 以下なら、`ty_substitute` で
  代入した型の種も `k` 以下。`ty_substitute` について使うのはこの形だけである。合併は `union_sound.taut`
  の葉の性質、タグは `tagged_shape` を使う。
* `field_kind` は Rust と nibcheck で同じに読む。`F(X)` は `F` と `X` の両方を見る。
  総称の名前で書かれた引数なしの `TyNamed` は、`ty_substitute` と同じく総称として読む。nibcheck の
  不動点の反復は、要約が増えたかを長さでなく包含で調べる。

### 層 3：要約の構築（`src/summary_sound.taut`、`src/summary_state.taut`）

* `datas_summarize_summary_ok`：宣言マップが整列していれば、`datas_summarize` の結果は `SummaryOk`。
  入力の要約の正しさや、燃料が十分であることは仮定しない。
* `summary_field`・`summary_ctors`：保持する総称は、入力の `holds` が総称の中にあれば、計算後も
  総称の中にある。これと種の上限から、燃料切れの `data_top` は `DataOk` を満たす。
* `summary_least`・`summary_update_floor`：宣言した種、再帰の下界、言及しない総称の条件は、
  `data_least` が満たし、一周の更新で保たれる。
* `summary_round_unchanged`・`summary_round_quiet`：`grew = no` で終わる一周は状態を変えず、
  訪問した各宣言が固定点条件を満たす。`summary_map_key` は、検索できるキーが `ordmap_entries` に
  含まれることを示す。したがって全宣言について固定点条件が得られる。
* `ck_finish_datas_summary_ok`：宣言マップが整列していれば、`ck_finish_datas` の後の状態は
  `CkSummaryOk`（`SummaryOk(c.datas)`）を満たす。再帰フラグの設定は整列性を保ち、宣言の診断は
  `datas` を変更しない。
* `ck_summary_fixed`・`ck_summary_grows`：宣言環境を保つ状態遷移は `CkSummaryOk` を保つ。
  `ck_unify_summary_ok`・`ck_fits_summary_ok`・`ck_join_summary_ok` は、既存の保存定理を介して
  単一化・適合判定・join についてこれを示す。

### 層 3：宣言登録から要約の不変条件へ

* `src/datas_frame.taut` の `CkReadFrame(c, m)` は、処理の前後で `datas` と `subst` が
  等しいこと。`frame_bind_ok` で逐次処理をつなぎ、`frame_summary` で `CkSummaryOk` の保存に移す。
  `ck_written_in_frame` などは、書かれた型を読む相互再帰全体についてこれを示す。
* `src/datas_registration.taut`：フィールドとコンストラクタを読んでも宣言環境は変わらず、
  コンストラクタ索引の登録は宣言マップを変えない。`ck_declare_data_ordered` は宣言の挿入が
  マップの整列性を保つことを示す。prelude とプログラムの一覧について帰納し、
  `ck_prepare_datas_summary_ok` で要約の構築につなぐ。`ck_prepare_new_summary_ok` は初期状態からの
  定理で、整列性を外から仮定しない。効果の宣言も `CkReadFrame` を保つ。
* `src/signature_frame.taut`：引数、戻り値、借用、`where` を読む処理、関数の登録、prelude と
  プログラムの署名一覧の登録は `CkReadFrame` を保つ。
* `src/classes_frame.taut`・`src/instances_frame.taut`：クラスの種注釈・メソッド・法則の診断、
  インスタンスの頭・制約・法則・署名比較・登録について同じ保存を示し、
  `ck_declare_classes_frame` でクラスとインスタンスの登録全体につなぐ。
* `src/prepare_sound.taut` の `ck_prepare_fns_summary_ok`：クラス、インスタンス、prelude の関数、
  プログラムの関数を登録しても要約は正しい。`registration_new_summary_ok` は初期状態から
  データと呼出可能な宣言の準備を続けて行った後の `CkSummaryOk` を、追加の前提なしに示す。
* `types_run.taut` の `ck_prepare_datas` と `ck_prepare_fns` は、`ck_run` が検査の前に行う宣言の準備で、
  `ck_run` はこの順に呼ぶ。証明は各処理の展開との等式をカーネルで確かめている。

上の保存定理は宣言環境を変えないことを示すもので、クラス解決や式の型付けの健全性の代わりにはならない。

## 証明のキャッシュ（`crates/tauto-kernel/src/check/cache.rs`）

一度検査を通った定理の証明は、それが依るものが変わらない限り検査し直さない（項目ごと、内容アドレス）。

* **鍵**は SHA-256 で、検査器自身のソース、定理（文と証明、位置は除く）、定理が名指す大域のそれぞれの
  **インターフェース**のハッシュから作る。インターフェースは型、展開されるなら値（関数・定義。定理の証明は
  展開されないので入らない）、族の宣言で、それらが名指すものへ推移的に及ぶ。検査器の作った名前（`x'42`）は
  現れた順に番号を振り直す。
* よって証明を書き換えても、その定理を使う側は無効にならない。関数の本体を変えると、それを使う定理だけが
  検査し直される。宣言をファイル内で動かしても変わらない。
* キャッシュに当たっても、文はキャッシュがないときと同じく精密化され、二つの検査器（`check.rs` と `check/core.rs`）が
  検査する。証明だけを検査済みとして扱う。失敗・未完の宣言を名指す定理はキャッシュしない。
* 関数（`mutual` の組、no-confusion を含む）は値が展開されるので、検査済みとしては扱わない。同じ作りの鍵で
  精密化した項を保存し、当たったときは精密化と `check.rs` の検査を省いて、その項を `check/core.rs` が
  毎回検査する。no-confusion は作り直し、やはりコアだけが検査する。保存された項がコアを通らなければ
  （壊れたキャッシュなど）、精密化からやり直して書き直す。
* 置き場所は `$TAUTO_CACHE`、なければ `$XDG_CACHE_HOME/tauto/proofs`、`~/.cache/tauto/proofs`。
  `TAUTO_CACHE=off` か `tauto check --fresh` で全部検査する。`tests/proofs.rs` はキャッシュを使わない。

## 範囲外

| 部品 | 理由 |
|---|---|
| `lint.rs` の移植 | 方針として行わない |
| カーネル（`check.rs`、`check/`）とエラボレータ | カーネルのリテラルの算術が `u128` を使う。Nib に `u128` がない。信頼の境界の設計も要る |
| `eval.rs` | 多重の継続を Nib で書く設計が要る。インタプリタの上のインタプリタは遅すぎるので、バックエンドの上で書く |
| `report.rs`、CLI | OS の層の上で書けるが、CLI が呼ぶカーネルと `eval.rs` が Rust のまま（上の二行）なので、CLI も Rust のまま置く |
| NIR・rustgen・`tauto-bind`・`tauto-build` | [`rust-backend.md`](rust-backend.md) の領域 |

## 未決定

| # | 問い |
|---|---|
| 1 | tote の名前を最上位の `module` にするか、名前の先頭の tote 名をどう外すか |
| 2 | tote の git の依存、版、ロックファイル（`Tauto.lock`） |
| 3 | `u128` か多倍長の整数（カーネルのリテラルの算術のため） |
| 4 | 静的なデータのリテラル（`const` の表、バイト列の埋め込み） |
| 5 | 証明側の遅さが問題になったとき、kernel の primitive（`Text`、機械整数）を足すか |
| 6 | nibcheck の健全性の残り：関数本体・トップレベルの式・最終診断を含む検査全体が `datas` を保つこと、データと関数の宣言が宣言的な規則でよく形成されていること、層 4〜8（式、クラス、効果、線形性、全体） |
