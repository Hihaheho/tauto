# tauto の self-host

tauto のコンパイラの大部分を tauto で書き直す方針と、その構成。部品は tote（`totes/`）にまとめ、
kernel が検査する全域な層（`inductive` と total な `fn`）で書き、要所に正しさの定理を付ける。
各 tote の README が振る舞いを、`tools/selfhost-harness` の試験が Rust の実装との一致を示す。

## 方針

| 項目 | 方針 |
| --- | --- |
| 何を書くか | 主要な層は「構成」の tote。限定的な Rust 出力は `totes/rustgen` が担当する。実行は `eval.rs`（インタプリタ）または既存の Rust バックエンドによるビルドで行う |
| どこまで証明するか | 全域性と型（kernel が検査し、止まり、網羅的）に加え、要所の正しさの定理。全関数の仕様は書かない。ただし `totes/nibcheck` は検査器全体の健全性まで示す（「nibcheck の健全性（`totes/nibcheck/src/`）」） |
| kernel | 通常の検査には Rust の `check.rs` と `check/core.rs` を使う。独立カーネルの Tauto 実装 `totes/kernel` は、書き出した精密化済みの宣言を再検査する。精密化の糖衣（「精密化の糖衣」）は kernel の外にあり、kernel と `check/core.rs` が受け取る項の形は糖衣なしで書いたときと同じ |
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
| `crates/tauto-kernel/src/check/core.rs` の閉じた宣言の検査 | `totes/kernel`（[`totes/kernel/README.md`](../../totes/kernel/README.md)） |
| `tauto-rt`、`tools/tauto-parol-gen` | Rust のまま（後者は Rust の表の生成器を動かす道具なので。`totes/llkgen` が同じ表を作る） |

限定的な Rust 出力は [`totes/rustgen`](../../totes/rustgen/README.md) が担当する。
Tauto の surface parser から関数を読み、明示的な `i64`/`Bool` の部分言語を検査して Rust を出力する。
未対応の構文は拒否し、Rust の精密化器やコード生成器に入力を転送しない。
この tote 自体のビルドは既存の Rust コンパイラを使い、精密化器全体・完全な Rust バックエンド・
コンパイラの bootstrap は含まない。

依存は一方向で、循環は tote の読み込みが拒否する。

```text
text ─┬─ fmt
      ├─ scan ── llk ── syntax ── surface
      │                              └────── nibcheck
      └─ （すべての tote が text を使ってよい）
```

```sh
tauto run --steps 1000000000 --tote totes/fmt -- ARGS…    # tote を eval で走らせる
cargo test --locked --manifest-path tools/selfhost-harness/Cargo.toml                      # 差分試験と証明
```

## 全体の形

```text
totes/<name>/src/*.taut   型・関数・定理・実行コード
totes/<name>/src/main.taut 実行の入口
std/*.taut                標準ライブラリ
```

`totes/` のソースは `.taut` に統一する。定理も同じソースに置き、独立した
`src/` ディレクトリは使わない。定理と実装を同じファイルに書いても、別の
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
5. `Text` の大小は `Text::compare` で比べる。失敗しうる関数は `Result(T, E)` か `Option(T)` を返す。
6. `match` に `_ =>` の既定の腕を書かない（コンストラクタを足したとき黙って吸収されるため）。
7. 殻（Nib）の文字列リテラルにバックスラッシュと `"` を書かない。改行・タブ・引用符は `Text::of_code_point(10)` のように作り、
   名前の付いた関数にする。

## 精密化の糖衣

糖衣は、カーネルが糖衣なしで書いたときと同じ項を受け取るものに限る（カーネルに規則を足さない）。どれも
`check/matching.rs`（精密化）か `check/sugar.rs` にあり、結果は kernel と `check/core.rs` が検査し直す。
ケースは `cases/check/programs.eure`。

1. **fn のジェネリクス。** `fn len<A>(l: List(A)): Nat` の `A` は `theorem` の `<A>` と同じく
   型 `Type` の暗黙引数。
2. **項の中の `match`。** 引数や関数の本体の中に `match` を書ける。
3. **式への `match`。** `match Nat::lt(a, b): Nat { … }` は、新しい変数 `x` についての `match` を
   作り、`x` に式を代入したもの。場合分けだけで、式の欄への呼び出しは再帰にならない。
   定義中の関数への呼び出しを式に書ける（`match even(k): Bool { … }`）。それは腕の外で帰納法の仮定になる。
4. **テキストのリテラル。** `std/Text.taut` が `inductive Text { Mk(bytes: List(Nat)) }` を宣言した後は、
   `"ab"` を `Text::Mk(Cons(Nat, 97, Cons(Nat, 98, Nil(Nat))))`（UTF-8 のバイト列）と読む。
5. **演算子。** `std/Base.taut` が `Nat::add` を宣言した後は（`Bool` は kernel の prelude にある）、
   `-` を `Nat::sub`、`a < b`・`a <= b` を `Nat::lt(a, b)`・`Nat::le(a, b)`、
   `a > b`・`a >= b` を引数を入れ替えた `Nat::lt`・`Nat::le`、`&&`・`||` を `Bool::and`・`Bool::or` と読む（`not(a)` は関数 `not` の呼び出し）。
   `+`・`*` は読み替えず、どこでも kernel 組み込みのまま（`Nat::add(a, b)`・`Nat::mul(a, b)` はその別名で、
   `a + b`・`a * b` と定義上等しい）。`+`・`*`・`-` は第2引数についての再帰で定義した関数（ペアノ）で、
   `a + Succ(k)` は `Succ(a + k)`、`a * Succ(k)` は `a * k + a`、`a - Succ(k)` は `pred(a - k)` に簡約する。
   kernel が特別に計算するのは、両方の引数がリテラルのときだけ（その定義を展開した結果と同じ値）。
   prelude の `Nat::eq`・`Nat::lt`・`Nat::sub`・`Nat::div_nz`・`Nat::rem_nz`（`prelude_nat.taut`）も同じで、両方の引数がリテラルなら
   一度に計算する（`div_nz`・`rem_nz` の三つ目の引数、0 でないことの証明は見ない）。prelude の名前は宣言し直せないので、この計算は常にこれらの定義と一致する。
6. **レコード。** コンストラクタが一つの族 `T` について、`T { f: e, … }` はそのコンストラクタを
   フィールドの順に適用したもの。パターン `T { f: p, g }` も同じ（書かないフィールドは `_`、
   名前だけのフィールドはその名前を束縛する）。extraction もこの書き換えだけは読む。
7. **フィールド、等号、`let`。** コンストラクタが一つの族の値 `x` について `x.f` はそのフィールドを取り出す
   `match`。`a == b` は `a` の型で `Nat::eq`・`Bool::eq`・`Text::eq` のどれかになり、`a != b` はその `not`。
   型注釈なしの `let x := e` は、`x` を `e` で置き換えたもの。extraction は `x.f` を `match`
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

* `fn f(&mut c: C, x: A): R` は、`fn f(c: C, x: A): Mut1(R, C)` と読む。`MutK(R, S1, …, SK)` は
  コンストラクタ `mutK(value': R, s'1: S1, …)`（プログラムが書けない名前のフィールド）を一つ持つ族で、使われたときに宣言される。`&mut` 引数が
  複数あれば、書いた順に並ぶ。定理では `f(counter(0, 0)) = mut1(v, c')` のように、値と最後の状態を語る。
* 本体では、状態（`&mut` 引数と見えている `var`）を名前で持ち回る。呼び出し `g(&mut x, &mut y.f, e)` は
  `match g(x, y.f, e) { mut2(v, x, t) => … }` で、`y` はフィールド `f` を `t` にして作り直す。
  `x := e` と `var x := e` は `match mut0(e) { mut0(x) => … }`（`let` と違い、項を複製しない）。
* 状態を変える `match`（と `if`。`true`・`false` への `match`）は、関数の最後なら各腕がそのまま関数を終える。
  途中なら状態全部を `mutK(v, …)` で返し、続きがそれを取り出す。このとき値の型が要る: 文としての
  `match` は `()`、`let x: T := match …` か `match e: T` で書く。`var` も型を書く。
* 引数は書いた順に評価する。後の引数が状態を変えるなら、先に読んだ値を束縛しておく。`&x` は `x`、
  `()` は `#()`（要素のない積。型も `#()`）。
* `while` や `return` を含む関数は実行用（証明言語の宣言ではない）。ラムダの中では状態を変えられない。
* 除去子の値の型（動機の適用 `(t => Nat)(c)`）を含意引数として推論したとき、頭のラムダを簡約してから
  精密化する。これで `match g(c.n) { … }` のように、フィールドを総称関数へ渡す式に `match` できる。

## extraction（`crates/tauto/src/extract.rs`）

kernel の型から、各宣言の引数が **型・証明・値** のどれかを読む（`check/roles.rs`）。値だけを残す。
宣言の引数数も検査済みメタデータに保持し、結果が関数型の場合に、その関数の引数と区別する。

抽出は kernel が検査した展開済みの宣言とソースのスナップショットを使い、検査後にファイルを
読み直さない。tote のローダは、抽出した全域関数の情報を実行プログラム全体に結び付けて保持する。
効果の検査では、そのプログラムが変わっていないときだけ、該当する関数の再帰を `Div` としない。
通常の Nib の再帰、別名や関数を返す呼び出しを通る循環にはこの扱いをしない。
書き出された Nib のコメントやファイル名は全域性の根拠にならず、テキストとして読み直したものには
この情報はない。引数の関数値の効果と歩数を数える呼び出しは、同じ検査済みの効果の行から決まる。

| 証明側 | Nib |
| --- | --- |
| `inductive`（`Type` の族、添字なし、パラメータは型のみ） | `shared enum`。型のパラメータはジェネリクス、証明の欄は落とす |
| 上記のうち構築子が一つの族 | `shared struct`。構築子の呼び出しは `Name { f: v }`、パターンも同じ形。公開された欄は Nib から `x.f` で読む |
| 添字・型以外のパラメータ・型を格納する欄を持つ族、それらを含む族 | 非公開の共通値表現。閉じた依存型の境界は nominal な抽象型 |
| `Prop` の族、`theorem`、`axiom`、`def` | 落とす |
| `fn` | 型の引数はジェネリクス、証明の引数は落とし、呼び出しの対応する引数も落とす |
| `match x: T` | `match x`。証明への `match` は腕一つの値。`Nat`・`Bool` への `match` は `if` の鎖 |
| 証明の `let` | 落とす |

**証明を渡せないコード。** kernel が検査しないコード（Nib のコード、kernel が読まない効果つきの `fn`、
トップレベルの文）は証明を書けない。抽出が証明の引数と欄を落とすので、そのまま呼べば証明の要求が消える。
だから、そのコードから次のものを使うと抽出の段階でエラーにする（`proofs_given`）：呼び出しで書く引数に
証明を含む `fn`、証明の欄を持つ構築子、その族のレコード `T { f: v }`。`where` が足す法則は呼び出しで
書かないので数えない。通常の抽出で作ったレコードの値は受け取り、公開されている欄を読める。
依存するデータの境界は次の規則に従う。

**依存するデータ。** 添字付き帰納族、型以外のパラメータを持つ族、その値を含む族を
操作する検査済みの計算は、非公開のタグ付き共通値表現に写す。型と証明の内容は
消去し、計算に使える値の引数・欄を保持する。関数値も同じ表現で保持するため、
実行時に決まる添字や、再帰で変化する型引数の列挙を必要としない。
型による枝の絞り込みは検査時に行い、実行時には保存したタグと値で分岐する。
不可能な枝と内部のタグの不一致は `extract_unreachable` に写す。これは未定義動作ではなく
発散する内部関数で、到達しないことは検査済みの入力と抽出の正しさに依存する。

Nib への境界では、閉じた依存型ごとに nominal な抽象型を使う。同じ型かどうかは
カーネルの変換で判断する。異なる添字・述語は、実行時の欄が同じでも別の型になる。
構築子・欄・パターン・内部の変換関数は公開しない。検査済みの関数で値を作り、
同じ契約を要求する関数へ渡せる。`Option` と `List` の要素にもこの型の区別を保持する。
通常の帰納型は元の Nib の表現を保ち、欄ごとの内部変換を通して共通値表現と受け渡す。
型引数に抽象型を含む場合も、その要素の型の区別を保つ。再帰で変わる型は添字として表し、
閉じた族の型全体を抽象型として公開する。構築子の再帰的な展開や有限個の特殊化は行わない。
値の引数に依存する契約や総称的な依存関数は、そのまま Nib の関数として公開せず、
検査済みの関数内で使う。境界で公開するには閉じた型の引数と結果を持つ関数で包む。
効果を持つ計算は、操作の識別子・引数・継続を持つ非公開の要求として表す。
引数とブロックの文は左から右へ評価し、未処理の要求には後続の計算を継続として結合する。
証明の結果を消去する場合も、その結果を得るための操作は実行する。
継続の本体は非公開の関数に分離し、自由な局所値だけを捕捉する。
ハンドラは自分の操作を処理し、他の操作を外へ転送する。再開した計算には同じハンドラを適用し、
その最終値には return 腕を適用する。操作の腕が返した値に return 腕を重ねて適用しない。
再開回数の制約は、元のハンドラを検査するカーネルの規則で保証する。
閉じた引数・結果を持つ操作は、通常の値と同じ境界変換を通して Nib の効果へ接続する。
内部の動的な適用と不可能な分岐を含む境界の行には、保守的に `Div` も含める。
局所的な可変値は検査済みの型のセルに保持し、継続から同じセルを参照する。
関数値は元の引数位置の個数を保持する。消去した型・証明の位置には内容を持たない
一つの値を渡し、型引数に命題を渡しても位置を削らない。部分適用は渡された値を捕捉し、
余る引数は結果の関数値に渡す。直接の呼び出しでは宣言の役割が既知の位置を省略する。
暗黙に補う位置とその値は精密化が選んだ適用から記録し、キャッシュにも保持する。
型・証明の内容は消去し、実行時に必要な補完値は明示引数と同じ規約で渡す。
抽出はこのメタデータと元の構文を使い、カーネルへ展開された項には依存しない。
閉じた関数型も nominal な抽象型になり、同じ関数型を受け渡す宣言は同じ境界を使う。
検査済みの関数が作った関数値を保存・受け渡しできるが、未検査の関数をその値として
構築する操作と、Nib から直接呼び出す操作は公開しない。

`I64` の範囲の証明は消去するが、値はその範囲と一致する Nib の `i64` に写す。
検査済みの構築・分解と、実行時の範囲検査を行う関数は、その写像を通して実行する。

`inductive struct` と `inductive enum` はこの逆向きで、プログラムは書いたとおりに実行し、カーネルには
同じ形の族を渡す。欄の型は下の写像の表を逆に引く（`u64` は `U64`、`Bool` は `Bool`）
（[`program-data.md`](program-data.md)）。

**写像の表**（信頼する部分）。`std/` の次の宣言は書き出さず、Nib の型と関数に写す。どれも
`std/` に定義があり、証明はその定義について行う。

| 証明側 | Nib |
| --- | --- |
| `Nat`、`Zero`、`Succ(n)` | `nat`（上限のない自然数）、`0`、`n + 1` |
| `U8`・`U32`・`U64`、`I32`・`I64` | `u8`・`u32`・`u64`、`i32`・`i64`（`std/UInt.taut`、`std/SInt.taut`） |
| `Bool`、`true`、`false` | `Bool`、`true`、`false` |
| `List`、`Option`、`Pair`、`Unit` | Nib std の `List`、`Option`、`Pair`（証明が族として読む prelude の宣言そのもの）、`()` |
| `Text` | `Text`（「`std/Text.taut`」の関数） |
| `Array`、`Array::of_list`、`Array::get`、`Array::len`、`Array::to_list` | Nib std の `Array` と同名の builtin（「配列」） |
| `Bytes`、`bytes(l)` と `bytes_*`、`Text::of_bytes` | Nib std の `Bytes` と同名の builtin（「バイト列」） |
| `Float` と `float_*`、`I64::of_float_checked`、`Text::of_float`、`Float::of_text` | Nib の `Float` と演算子・同名の builtin（[`float.md`](float.md)。値を定義しない関数は公理） |
| `Stack` と `stack_*` | Nib std の `Vec` と `vec_*`（「スタック」） |
| `Nat::lt`、`Nat::le`、`Nat::eq`、`Nat::sub`、`Nat::div_nz`、`Nat::rem_nz` | `<`、`<=`、`==`、飽和減算、割り算と剰余（0 でないことの証明は消える） |
| `Quot(A, r)`、`Quot::mk(A, r, a)`、`Quot::lift(A, r, B, f, h, q)` | `A`、`a`、`f(q)`（「商」） |
| `Bool::and`、`Bool::or`、`not` | `&&`、`\|\|`、`not(a)` |

**信頼の範囲。** kernel と `check/core.rs`、写像の表、Nib の実行系（`eval.rs`、Rust バックエンド）、殻。
写像のずれは差分試験で見る。**既知の差**：`u64` は 2^64 で溢れて実行時エラーになる
（`Nat` は溢れない）。証明側の値は入力の位置・長さ・数え上げ（入力のバイト数以下で、入力はメモリに載るので 2^64 に届かない）と、
数のリテラルを読んだ値（`totes/text` の `text_parse_u64` は 2^63 以上を `None` にする）なので、この差は出力に現れない。

## 証明側の標準ライブラリ

### `std/Base.taut`

`Bool`、`nat_*`、`list_*`、それらと命題をつなぐ補題。項についての場合分け `Ordering::cases(P, e, …)` もここにある：
`P` は場合の値についての `match` を含む関数で、プログラムの本体が `e` についての `match` に
展開されたものが `P(e)` になる。各場合は `e` がその値に等しいという仮定を受け取る。

### 整数の割り算

丸め方の違う整数の割り算は名前つきの関数で書き、中置の `/` は分数としての割り算（`Rat` など）だけに使う。
割る関数は型ごとに二つの形を持つ。

- effect のない形は、割る数が 0 でないことの証明 `h: ¬(b = 0)` を受け取る：`Nat::div_nz(a, b, h)`・
  `Nat::rem_nz(a, b, h)`（`prelude_nat.taut`）、`Int::tdiv_nz`・`Int::tmod_nz`・`Int::fdiv_nz`・`Int::fmod_nz`
  （`std/Int.taut`）、`U8::div_nz`・`U8::rem_nz` と `U32`・`U64` の同名の関数（`std/UInt.taut`。証明は `¬(val(b) = 0)`）、
  `I32::tdiv_nz` などと `I64` の同名の関数（`std/SInt.taut`。結果が幅に収まらなければ `None`）。
- effect つきの形は、0 で割ると effect `DivZero`（`std/UInt.taut`）を起こす：`Nat::div(a, b): Nat ! {DivZero}`、
  `Nat::rem`、`Int::tdiv`・`Int::tmod`・`Int::fdiv`・`Int::fmod`、`U8::div`・`U8::rem` など、`I32::tdiv` など
  （`! {DivZero, overflow}`）。どれも `b` が 0 かを判定し、0 なら `DivZero` を起こし、そうでなければ
  判定の結果から作った証明で `_nz` の形を呼ぶ。意味は一つで、二つの形は前提を証明で渡すか effect で扱うかの違いである。

0 を返して全域にすることも、`Option` で返すこともしない。呼び出し側は `DivZero` を handler で扱うか、row に載せて外へ伝える。
証明の中の等式は `_nz` の形で書く。0 でないことの証明は、数のリテラルなら `Nat::ne_zero(64, Refl)`・`Int::ne_zero(2, Refl)`
（`Nat::eq` の計算で確かめる）、`Succ(k)` なら `Nat::succ_ne_zero(k)`、`Nat::pow2(k)` なら `Nat::pow2_ne_zero(k)`、
`Nat::lt(0, b) = true` からは `Nat::ne_zero_of_pos(b, h)` で作る。核の証明は無関係なので、同じ割り算に別の証明を
渡した項は変換で等しい。

### `std/Refined.taut`

`Refined(A, P)` は `A` の値 `val` と、それが `P` を満たす証明 `ok` の組。証明は `Prop` なので抽出で消え、
検査済みの計算では値の欄だけを保持する。Nib との境界では述語ごとに区別される抽象型になる。
`Refined::ext` は `val` が等しい二つが等しいこと
（カーネルの証明の無関係性による）。`refine_by(p, x)` は `Bool` の述語 `p` で `x` を実行時に検査し、`true` なら
証明つきの値を返す。述語を `Eq(Bool, p(x), true)` の形にすると、プログラムに書いた値の証明は `Refl` で済む。
kernel が検査しないコードは `Refined` を直接構築・分解できない。検査済みの関数から受け取り、
同じ述語の型を要求する関数へ渡す。値を読む操作も検査済みの関数として公開する
（「extraction（`crates/tauto/src/extract.rs`）」）。

### `std/Text.taut`

`Text` は UTF-8 のバイト列のモデル。長さ、`i` 番目のバイト、切り出し、連結、比較、数の十進表記を
定義し、表で Nib の builtin に写す。コードポイントの復号は証明側で書く（バイトの算術）。

### 停止性の書き方

構造的再帰で書けないもの（スキャナと構文解析器の駆動ループ、単一化、不動点）は **fuel** で書く。
`fuel: Nat` を最初の引数にして `match fuel` で減らし、尽きたら失敗を表す値を返す。呼び出し側は
入力の長さから十分な fuel を渡し、定理は「fuel が足りれば失敗しない」形で述べる。

互いに呼び合う関数が同じ fuel を分け合うときは、`mutual { fn … }` にまとめ、どれも `fuel: Nat` を
最初の引数にして `match fuel { Zero => … Succ(j) => … }` と書き、呼び合いには `j` を渡す。フロント
エンド（`crates/tauto-kernel/src/check/steps.rs`）がこの組を、要求の帰納型と答えの帰納型、要求に答える
一つの関数 `F'read`（`fuel` についての構造的再帰）と、それを呼ぶ元の名前の関数に書き換える。
各関数の `Zero` 腕は `F'Zero'f(a⃗)` という関数になり、呼び出しごとに同じ引数で渡される（答えの型が
違うときの既定値。実際には使われない）。だから `Zero` 腕は引数を使ってよい（`&mut` の関数の `Zero` 腕は
状態を返すので、これが要る）。カーネルの規則は変えない。例は `cases/check/induction.eure` の
`mutual-functions-can-share-a-step-count`。

### 配列

表（scan の文字分類、llk の遷移表など）は添字で引く。`std/Array.taut` の `Array(A)` は証明側では
リストを包んだもので、`Array::get(a, i)` は `List::nth` と定義される。証明はこの定義について行う。
extraction は `Array` を Nib std の `Array`（`std/prelude/Shared.taut`、shared で読むだけの配列）に、
四つの関数を同名の builtin に写す。evaluator では `Value::Array`、
Rust では `Rc<[A]>` で、`Array::get` は O(1)。信頼するのは「この builtin がリスト版の定義どおりに
振る舞う」ことで、`Nat` と `nat` の写像と同じ種類の前提である。差分は
`cases/rust/programs.eure` の `arrays-are-shared-and-read-by-index` で見る。

### バイト列

ネットワークやファイルのバイナリは `std/Bytes.taut` の `Bytes` で扱う。証明側では `List(U8)` を包んだもので、
長さ・`i` 番目・切り出し（`start <= end <= 長さ` のときだけ `Some`）・連結・等しさ、`Text` との行き来を定義する。
`Text::of_bytes` は `Text::of_utf8` と同じ UTF-8 の検査を通ったときだけ `Some` で、`Bytes::of_text` はテキストの
バイトをそのまま並べる（テキストのバイトは 256 未満なので、各バイトを 256 で割った余りにする定義は値を変えない）。
extraction は `Bytes` を Nib std の `Bytes`（`std/prelude/Shared.taut`、shared で読むだけ）に、各関数を同名の
builtin に写す。実行では切り出しが元の記憶域を共有する窓になり（evaluator と Rust は `tauto_rt::stdlib::Bytes`、
JavaScript は `Uint8Array` の `subarray`）、`Bytes::slice` は O(1) でコピーしない。信頼するのは `Array` と同じく
「この builtin がリスト版の定義どおりに振る舞う」ことで、差分は `cases/eval/bytes.eure` を三つの実行系で見る。

### スタック

解析のスタックやフレームのスタックは、リストの先頭に積むと 1 回ごとにセルを確保する。`std/Stack.taut` の
`Stack(A)` は証明側ではリストを包んだもの（トップが先頭）で、`Stack::new`・`Stack::push(&mut s, x)`・
`Stack::pop(&mut s)`・`Stack::len(&s)`・`Stack::is_empty(&s)` の定義がその意味を言う。extraction は `Stack` を
Nib の `Vec`（affine）に、五つの関数を `Vec::new`・`Vec::push`・`Vec::pop`・`Vec::len` の呼び出しにその場で
展開する（関数としては書き出さない）。実行ではトップが `Vec` の末尾で、積むのも取るのも O(1)、要素ごとの
セルはない。信頼するのは写像だけで、`Array` と同じ種類の前提である。

`Vec` は affine なので、`shared` な構造体のフィールドには入れられない。`&s`・`&mut s` で貸すか、
`var s: Stack(A) := Stack::new()` の局所にする。名前の `stack` はコンストラクタ（`Stack::Mk`）と衝突しない。
使い方は `totes/llk`（パーサのスタックとイベント）と `totes/syntax`（CST のフレーム）にある。イベントは
積んだ順の逆に取り出すので、CST は最後のイベントから組む。

### 商

`Quot(A, r)` は kernel の定数（prelude と `check/core.rs`）で、補題は `std/Quot.taut` にある。
プログラムは類を `Quot::lift(A, r, B, f, h, q)` でしか読まない。`h` は、`r` で関係する二つの値に
`f` が同じ結果を返すという証明である。extraction は `Quot(A, r)` を `A` に、`Quot::mk(A, r, a)` を `a` に、
`Quot::lift` を `f(q)` に写し、関係と証明は落とす。どの代表を持っていても `f` の結果は同じなので、
実行時に代表の違いは見えない。builtin を足さず、信頼する写像も増えない。公理 `Quot::sound` は証明として
落ちるので、それを使う宣言を含むプログラムも抽出する。差分は `cases/check/quotient.eure` の
`a-program-reads-a-class-through-a-lift-on-every-backend` を三つの実行系で見る。

## 殻

殻（`src/main.taut`）は `argv` で引数を、`read_file` で入力を受け、証明側の純粋な関数を一度
呼び、結果を `print`・`eprint` で書くだけにする（標準エフェクト、`host-effects.md`）。殻の行数は tote ごとに数十行に収め、
人間が目で確かめる。OS の builtin は `std/prelude/Os.taut`、テキストと数の builtin は `std/prelude/Text.taut`、`std/prelude/Num.taut`。

## 差分試験

`tools/selfhost-harness` が共通の道具を持つ。

- `run_tote(name, args, steps)` は tote を eval で走らせる（`load_tote` と `run_program_with` を直接呼ぶ）。
- コーパスのすべての入力を一時ディレクトリに書き、パスの列を `args` で一度に渡す。tote は結果を `== <名前>` の行で区切って一つの標準出力に出す。Rust の側も同じ形の文字列を作り、`assert_same_dump` で比べる。
- 違えば、最初に違う行の前後を並べて失敗する。

## 構文（`totes/scan`、`totes/llk`、`totes/lr`、`totes/syntax`）

構文の正本は `totes/grammar/src/grammar.taut` の `syntax tauto` 宣言。生成された `tauto::parse` は型付き AST を返し、同 tote の入口で実際にソースを解析する。`tauto syntax source totes/grammar tauto` が文法のリテラルをそのまま取り出し、`scripts/generate-tauto-grammar.sh` が bootstrap 用の `tauto.par` と試験用の文法へ書く（`--check` は差分の検出だけ）。

`tools/tauto-parol-gen` がその `tauto.par` から作った表を、tauto のデータとして書き出し、それを読む駆動部を tauto で書く。最初に宣言を読む Rust の bootstrap parser と `tauto::parse` の `syn_parse` runtime は残る。型付き AST の parser をコンパイラの CST・エラー回復の駆動部に置き換えたという意味ではない。

1. 表の書き出し：`tauto_parol::syntax_tables()` が `generated/parser.rs` の定数を読んで表を作り、`scripts/generate-syntax-tables.sh` が表ごとのデータ `totes/syntax/src/tables/<name>.txt` と、それを `include_text!` で返す関数の `totes/syntax/src/tables.taut` に書く（`--check` で確かめるだけ）。書き出すもの：終端記号と非終端記号の名前、宣言された非終端記号、先読みの最大 k、読み飛ばすトークン、先読み DFA、生成規則（逆順で入っている）、字句のモードと DFA、文字クラス（全 Unicode スカラー値を区間にまとめる）、開始の非終端記号。
2. 静的なデータのリテラルがないので、数を空白で区切った長い文字列（データのファイルの中身）にして tote の中で読む。
3. `totes/scan` は字句の DFA の実行部分（最長一致、優先度、先読み、モードの切り替え）、`totes/llk` は LL(k) の駆動部、`totes/lr` は LALR(1) の駆動部（`totes/lalrgen` の表を `Tables::lr_texts` の形で読む）、`totes/syntax` は表と CST の組み立て。それぞれの README に振る舞いを書く。
4. 差分試験：同じソースから `tauto_parol::parse` と `totes/syntax` が同じ CST を作ることを確かめる。

## 証明（`totes/*/src/`、`std/`）

tote の定理は `totes/<tote>/src/*.taut` に置く。プログラム（`src/`）からは読まれず、
`tools/selfhost-harness/tests/proofs.rs` が、どの宣言も穴も公理もなく検査を通ることを見る。

### ordmap（`std/Map.taut`、`std/MapLaws.taut`、`std/MapRemoveFloor.taut`）

`std/Map.taut` は順序付きの写像（AVL 木、永続）。木を、その中順のエントリの列
（`Ordmap::tree_entries`）で読む。比較関数には全順序であること（`OrdmapLaw`：`cmp(a, a)` が
`equal`、`equal` なら等しい、`less` と `greater` が入れ替わる、`less` が推移的）を仮定する。

* 回転と `Ordmap::balance` はエントリの列を変えない（`Ordmap::balance_entries`）。
* 列が整列していれば、`Ordmap::tree_get` は列の先頭からの探索（`Ordmap::list_get`）、
  `Ordmap::tree_insert` は整列した列への挿入（`Ordmap::list_insert`）に等しい。
* よって `Ordmap::insert` は整列を保ち（`Ordmap::insert_ordered`）、挿入したキーは挿入した値を持ち
  （`Ordmap::get_insert_same`）、他のキーは値を変えない（`Ordmap::get_insert_other`）。

`Ordmap::compare_nat`（`std/MapLaws.taut`）と `Ordmap::compare_text`（`std/MapText.taut`。`Text::compare`、
バイト列の辞書式順序）は `OrdmapLaw` を満たす。よって数とテキストをキーにした写像では、上の定理は仮定なしに成り立つ。
同じ写像に違う `cmp` を渡すのは利用者の誤りで、検査しない（クラスを使う写像では
[`classes.md`](classes.md) のインスタンスの一意性がこれを不要にする）。

`std/MapRemoveFloor.taut` は同じやり方で `Ordmap::remove` と `Ordmap::floor` を示す。

* `Ordmap::tree_remove` は列からそのキーのエントリを除くこと（`Ordmap::list_remove`）に等しい
  （`Ordmap::tree_remove_entries`）。`Ordmap::join` は二つの列を繋ぐ（`Ordmap::join_entries`）。
* よって `Ordmap::remove` は整列を保ち（`Ordmap::remove_ordered`）、除いたキーは値を持たず
  （`Ordmap::get_remove_same`）、他のキーは値を変えない（`Ordmap::get_remove_other`）。
* `Ordmap::floor` は、列のうちキーが `k` より後でない最後のエントリ（`Ordmap::list_floor`）に等しい
  （`Ordmap::floor_entries`）。

### text と unicode（`totes/text`、`totes/unicode`）

文字 `c`（0x110000 未満でサロゲートでない、`text_is_char`）について、
`text_decode(Text::of_code_point(c), 0)` は `c` と符号化の全長を返す（`text_decode_of_code_point`、`totes/text/src/utf8.taut`）。
符号化の長さ 1〜4 ごとに示し（`utf8_round_1`〜`utf8_round_4`）、`Text::of_code_point` の各段
（`text_utf8_from_128` ほか、証明側に置く。計算だけで本体に一致する）をそれに繋ぐ。
算術は `src/nat.taut`：`Nat::add`・`Nat::mul` の法則、商と余りの一意性、商の商は積での商（`nat_div_div`）。
`totes/unicode` は Rust の `char::is_alphanumeric`・`char::is_whitespace` と同じ分類を、ASCII は証明側で決め、残りは表（`tables.taut` が `include_text!` で読む `tables/*.txt`）の区間で引く。

* 復号（`text_decode_with`）は積を `Nat::mul(64, x)` と書く。`Nat::mul` は第二引数で再帰するので、
  未知の `x` に対して展開されない（`Nat::mul(x, 64)` だと入れ子の深さに対して 64 の冪で項が膨らむ）。
* カーネルは止まった `match` の腕の下まで正規化するので、大きなリテラルとの比較（`Nat::le(55296, c)`）は
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

**`&mut` の関数についての証明の書き方。** 本体の途中で止まる式（`Nat::eq(ty, a)`、`llk_predict(…)` など）
ごとに、その続きを最後の引数で受ける関数（`llk_term_at` ほか、同じ書き方の `&mut` の関数）を置き、
仮定を `Eq::subst` で運ぶ。再帰呼び出しは `match` で包み直される（`llk_rewrap`）ので、その恒等を補題にする。
nibcheck の証明も同じ書き方をする。

### lr（`totes/lr/src/derives.taut`）

パーサのスタックの記号（上が先頭）と、読んだトークン（後のものが先頭）の関係 `LrForest(t, syms, done)` を置く。
空のスタックは何も導出せず、上の終端記号は最後に読んだトークンの型であり、上の非終端記号はその生成規則の
右辺に置き換えても同じトークンを導出する。

* `lr_run` が木を作れば、開始記号だけが入力の終わりの前のトークンを導出する（`lr_run_sound`）。
  `lr_parse` が成功を返しても同じ（`lr_parse_sound`）。
* 表の動作（shift、reduce、goto）がどうであるかは関係しない。reduce が生成規則の右辺を本当にスタックから
  降ろすこと、受理が開始記号の生成規則でスタック全体を降ろし、入力の終わりで起きることは関係するので、
  パーサはそれを確かめ、違えば失敗する（生成した表では起きない）。
* パーサは一歩を返す関数（`lr_step`）と、それを燃料の分だけ繰り返す `lr_run` に分けてある。`&mut` を使わない
  ので、証明は一歩ごとの場合分けで済む。

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
  `Refl` で等しいことを示す。前の引数にすると `match` がそれらを抽象し、形が合わない。
* 置換 `ty_substitute` について一般の性質は示さない。層 2 の総称の規則は置換した型をそのまま述べ、
  層 3 は `fk_sound` の形（代入した型の種を抑える）で使う。

### 層 2：`ck_unify`（`src/unify_sound.taut`）

`TyEq` の `ok`（`tyeq_poly` の rigid な型が二つの型に出ないこと）は、検査器が `kept` に記録した使い方とする（`KeptOk`）。
記録は終わりの置換でもう一度確かめられる（`ck_check_kept`）。

* `ck_unify_ok`：置換が整列していれば、後の状態は前の状態を延長し（`Grows`：整列、置換の延長、診断・リテラル・クラス・型構成子の記録と関数表の保持）、
  `true` なら `a` と `b` はその状態で同じ型。
* 燃料 `k` についての帰納（`unify_at`）で、相互再帰の四つ（`ck_unify_in`、`ck_unify_rest_in`、
  `ck_unify_pairs_in`、`ck_unify_app_in`）を同時に示す。`ck_unify_pairs_in` は長さが違うと `true` を返すので、
  定理は長さが等しいときの `TyEqList`（`TyEqLenAt`）。呼ぶ側はどこも長さを先に比べている。
* 二つの段の続き（`if m { k } else { false }`）は `ck_and(k, m)` と `post_and` で書く。
* ワイルドカードの腕は、どの構成子の代わりかを本体で名指せないので、`a`・`b` に等しい `a1`・`b1` についての
  定理にし（`rest_step_eqs`）、等式の仮定の型が腕ごとに精密化されるのを使う。

### 層 2：`ck_fits`（`src/fits_sound.taut`、規則は `src/rules_ty.taut` の `TySub`）

`TySub` は等しさ、`never`、総称の右（rigid に置いた形が合い、`kept` に記録がある）と左（`bounds` の
新しい変数で具体化した形が合う）、借用（`&mut` は `&` として、借用は値として）、複製できる値を借用として、
合併の左右、タグを忘れること、関数（引数は反変）、直積の射影と並べ替え（`A × B <: A`、`A × B <: B × A`）を
規則とする。直積の規則は、期待される型の各メンバー（`ty_wanted_members`）が直積のメンバーのどれかと同じ型
であることで、`ck_expect` が呼ぶ `ck_fits_wide` でだけ使う（合併と関数の型の中では位置で合わせる）。

* `ck_fits_ok`・`ck_attempt_fits_ok`：状態は延長され（`Grows`。data と kind の bound は変わらないか
  増えるだけ）、`true` なら `TySub` がその状態で成り立つ。
* 燃料についての帰納（`fits_all`）で、fits の相互再帰の 15 段を同時に示す。各段は、展開の等式を
  一度 `Refl` で示して `Eq::subst` する（`post_unf`）。ワイルドカードの腕は等式の仮定と `post_cases` で書く。
* 入れ子の `match`（一つの型で分けた腕の中で、もう一つの型で分ける）は、ワイルドカードの腕の数が掛け算に
  なり検査が終わらないので、内側を段に分けた（`ck_fits_inst_in`・`ck_fits_lend_in`・`ck_fits_untag_in`・
  `ck_fits_fn_in`）。答えは同じで、燃料を一段多く使う。

### 層 2：`ck_join`（`src/join_sound.taut`）

`ck_join` は二つの枝の型から一つの型を作る（同じ型、`never` でない方、`&A` と `A` なら `A`、それ以外は合併）。

* `ck_join_ok`：状態は延長され、二つの型はどちらも結果の型に `TySub` で合う。
* 合併の場合は `tysub_union_r` と、`ty_union` が合併の正規形であること（`tyeq_union_norm`）で示す。
* `&mut` の脱糖が作る形（`ck_join_my`・`ck_join_k`・`ck_jb2` など）を書き、`Refl` で元の関数と等しいことを
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
* `summary_round_unchanged`・`summary_round_quiet`：`grew = false` で終わる一周は状態を変えず、
  訪問した各宣言が固定点条件を満たす。`summary_map_key` は、検索できるキーが `Ordmap::entries` に
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

* `src/checker_frame.taut` の `CkRunFrame` は、宣言環境の不変性と置換の整列性を表す。
  単一化・適合判定・join と、それらに診断を続ける処理について保存を示す。
* `src/finish_frame.taut` の `ck_finish_report_summary_ok` は、入力の置換が整列し、宣言要約が
  正しければ、整数の既定幅と最終診断を反映したレポートの宣言要約も正しいことを示す。
* `src/rules_decls.taut` は、宣言一覧の関数名の一意性を帰納的に定義する。
  `src/decl_names_sound.taut` の `ck_check_fn_names_sound` は、関数名の検査後にエラーが
  なければこの関係が成り立つことを示す。extern の関数も同じ一覧で検査する。
* `src/fuel_sound.taut` は、本体・パターンの各検査が燃料 0 でエラーを記録することを
  計算で確かめる。空の一覧を含め、燃料が尽きたときは検査済みとして扱わない。

* `src/inference_frame.taut` は、式・文・関数本体の 26 個の相互再帰について、一つの燃料の
  帰納法で `CkRunFrame`（局所スコープを更新する処理では `CkScopeFrame`）を示す。
  `src/inference_*.taut` の各ステップは、実装の展開との等式と、そのステップの保存証明を持つ。
* `src/registration_ordered.taut` は、データ登録と要約の最終化が置換の整列性を保つことを示す。
  `src/body_frame.taut` は関数本体一覧とトップレベルを接続し、`src/run_summary.taut` の
  `types_check_summary_ok` は初期状態から返却レポートまで `SummaryOk` を示す。
* 呼び出し対象の推論結果は、状態の更新を終えてから `ck_poly_instance` に渡す。
  同じ状態への更新を引数に入れると更新前の状態を渡すため、別の `let` で順序を明示する。
  `src/call_failure_sound.taut` は、単一化の失敗を拒否することと、呼び出し対象・引数の両方の
  診断を残すことを計算で確かめる。

* `src/finish_acceptance.taut` の `ck_finish_obligations` は、最終レポートにエラーがなければ、
  整数リテラル・閉包・総称・種の制約・型構成子の制約・保留されたクラスの診断条件が
  最終状態ですべて成り立つことを示す。診断だけの処理は成功時には状態を変えないことを使う。
  ここで取り出すのは各診断の条件である。

* `src/mentions_sound.taut` は、型の解決・合併とタグの正規化・型適用が総称への言及を
  消さないことを示す。`src/ck_mentions_sound.taut` と `src/rigid_sound.taut` は、漏出の
  検査が成功すれば宣言的な `RigidFor` が成り立つことを示す。
  `src/final_rigid_sound.taut` の `ck_finish_type_equality` は、最終レポートにエラーがなければ、
  最終状態の記録を前提とした `TyEqAt` を `TyEqIn` に移す。
* `src/rules_kind_inst.taut` の `InstanceKinds` は、総称の各代入型が、宣言した種の制約を
  満たす型と等しいことを表す。`src/final_kind_sound.taut` は記録された代入に対してこれを示す。
  これは代入の種に関する条件で、借用を型引数に渡せないことなどの条件は別に示す。

* `src/rules_data_kind.taut` は、通常の型の引数の個数、明記した種によるフィールドの上限、
  再帰する宣言に許される種を、検査器から独立した関係で定義する。
  `src/declaration_arity_sound.taut` は通常の型位置で引数の個数が宣言と一致することを示す。
  `src/declaration_kind_sound.taut` と `src/declaration_program_sound.taut` は、宣言の最終検査が
  エラーなしなら、登録された宣言の明記した種の条件が成り立つことを示す。登録の存在・一意性、
  フィールド型自体の整形式性はこの条件に含めず、別に示す。
* `Grows` と `CkSame` は診断リストの保存も含む。`src/operation_error_sound.taut` は単一化・
  適合判定・join・期待型の検査で、先行するエラーが消えないことを示す。
  `src/finish_error_sound.taut` の `ck_finish_input_clean` は、最終レポートがエラーなしなら、
  整数の既定幅を決める前の入力状態もエラーなしだったことを示す。

* `src/checked_frame.taut` の `CkCheckedFrame` は、置換の整列性と、成功した後続処理が
  先行する診断を消さないことを組み合わせる。書かれた型、宣言登録、パターン検査、
  `src/inference_frame_checked.taut` の 26 個の相互再帰、トップレベルまでこれを保つ。
  `src/run_declaration_kind_sound.taut` の `types_check_declaration_kinds` は、この保存と
  最終診断の成功を使い、レポートの宣言環境で、登録された各データ宣言の明記した種の条件を示す。

* `src/data_names_sound.taut` は `struct` と `enum` を合わせた宣言名の一意性を示す。
  `src/run_data_names_sound.taut` の `types_check_declaration_names_unique` は、最終レポートに
  エラーがなければ、データ名と関数名がそれぞれ重複しないことを示す。準備段階の事実を
  最終結果へ運ぶ `PreparedProgramFact` は、後続処理による診断の保存を使う。

* フィールド型は、全データ宣言の登録後に `ck_recheck_datas` で再検査する。これにより、
  後方参照と自己再帰でも型引数の個数を検査する。最初の登録時点では参照先が未登録の場合がある。
  `src/field_recheck_frame.taut` と `src/field_recheck_error_sound.taut` は、この再検査が
  完成した宣言環境・置換と先行診断を保つことを示す。

* `src/run_data_presence_sound.taut` の `types_check_registers_data` は、ソースの各データ宣言が
  最終レポートに登録されていることを示す。登録後の再帰判定・要約計算（燃料切れを含む）・
  本体検査・最終診断はその存在を保つ。登録されたフィールドとソースとの対応は別に示す。
  `src/run_data_invariant_sound.taut` は、準備済みの宣言環境の任意の述語を最終結果へ運ぶ。

* `src/data_metadata_sound.taut` と `src/finish_data_metadata_sound.taut` は、要約と再帰判定が
  宣言の名前・総称・構成子とフィールド・注釈などの内容を保つことを示す。
  `src/data_entries_sound.taut` は、整列したマップの各列挙項目が実際の登録内容であることを示す。
* `src/rules_data_header.taut` の `SourceDataEntry` は、登録されたデータが存在し、その名前・
  種の注釈・総称一覧・view 指定がソースと一致することを表す。
  `src/run_data_header_sound.taut` の `types_check_source_data_entry` は、最終レポートに
  エラーがなければこれが成り立つことを示す。名前の一意性から、後続の宣言による上書きが
  ないことを使う。構成子のフィールドとソースの型式との対応は、この関係には含めない。

* `src/rules_written_name.taut` と `src/rules_written_atomic.taut` は、組み込み型名・総称名・
  名目型名の意味と、通常の型位置での引数の個数を定義する。
  `src/written_name_sound.taut` と `src/written_atomic_sound.taut` は、名前の解決結果が
  この関係を満たすことを示す。

* `src/rules_written_binders.taut` は、関数型の先頭の種の束縛、その後に残る引数、
  総称環境の拡張を定義する。`src/written_binder_sound.taut` は `pi_binders` と `binders_map` が
  この関係を満たし、束縛の個数だけ読み飛ばした引数の検査が、残りの引数を検査することと
  一致することを示す。

* `src/rules_written.taut` は、型適用・関数型・借用型・合併型・タグ付き型を含む
  型式の意味を宣言的に定義する。`src/written_leaf_sound.taut` は名前と種注釈の処理を、
  `src/written_composite_sound.taut` は内側の導出を仮定した借用・合併・タグ・種注釈の
  処理をこの関係へ接続する。`src/written_list_sound.taut` と
  `src/written_parameters_sound.taut` は要素ごとの導出を列へまとめ、
  `src/written_function_sound.taut` は総称束縛・引数・戻り値を関数型へまとめる。
  `src/written_application_sound.taut` は型適用の引数の導出を接続し、
  `src/written_app_choice_sound.taut`・`src/written_app_branch_sound.taut`・
  `src/written_nested_sound.taut` は分岐の分類と入れ子の型適用を接続する。
  `src/written_sound.taut` の `ck_written_sound` は、型式・型の構文・型引数列・関数引数列の
  相互帰納により、型式の検査結果にエラーがなければ `WrittenTerm` が成り立つことを示す。
  これは型式の意味の定理であり、登録されたフィールドとの対応や宣言の整形式性は別に示す。
  `src/written_context_sound.taut` は、型式を読む相互再帰全体について型構成子の位置が
  保存され、型式を読み終えると借用直下のフラグが消えることを示す。

* `src/rules_data_fields.taut` は、ソースと生成されたフィールド・構成子の名前および
  型式の対応を定義する。`src/data_fields_sound.taut` と `src/data_ctors_sound.taut` は、
  検査時の宣言環境でこの対応が成り立つことを示す。
  `src/written_unique_sound.taut` は、宣言環境が異なっても同じ型式の導出の値が一意である
  ことを示す。`src/written_stability_sound.taut` はこれを検査器の再検査へ適用する。
  `src/field_recheck_sound.taut` は、再検査が成功すれば、登録時のフィールド型・構成子型を
  変えずに再検査時の宣言環境へ導出を移せることを示す。
  `src/rules_data_body.taut` は登録された構成子列の存在と、そのフィールド型の導出を
  `DataBodyRegistered`・`DataBodyChecked` として定義する。
  `src/registration_body_sound.taut`・`src/program_data_body_sound.taut` は登録と後続宣言に
  よる保持を示し、`src/prepare_data_body_sound.taut` は再帰判定と要約計算を接続する。
  `src/program_body_recheck_sound.taut`・`src/prepare_body_recheck_sound.taut` は全宣言が
  そろった環境での再検査を接続する。`src/report_data_body_sound.taut` の
  `types_check_data_bodies` は、最終診断が空ならソース中の各データ宣言の構成子列が
  最終レポートに存在し、その環境でフィールドの型式の導出が成り立つことを示す。

* `src/rules_data_shape.taut` は、不透明な view がフィールドを持たない構造体である条件を
  定義する。`src/program_view_shape_sound.taut` の `types_check_view_shapes` は、最終診断が
  空ならプログラム中のデータ宣言がこの条件を満たすことを示す。
  `src/run_prepared_data_fact.taut` は、データ準備の成功から得る命題を最終診断へ接続する。

* `src/rules_signature_types.taut` は、署名の型注釈と借用指定の意味を定義する。
  `src/signature_written_sound.taut` は、注釈があればその型式の導出を、省略されれば
  推論変数を得ることと、引数の借用指定による型の構築を示す。`ck_sig_param_reset` は
  引数処理後に借用位置のフラグが消えることを示す。注釈のない借用引数の後にフラグが
  残らず、裸の `Slice` を戻り値や次の署名で受理しない。`src/signature_generics_sound.taut` は総称束縛を、
  `src/signature_body_sound.taut` は引数列と戻り値の型式を関数型にまとめる処理を示す。
  `src/signature_header_sound.taut` の `ck_signature_elaborates` は、この二つと署名に
  保存される総称・型構成子の一覧を `SignatureElaborated` にまとめる。

  `src/program_signature_sound.taut` の `ck_program_decls_elaborates` は、宣言処理が返す
  本体検査用の署名列の各要素に、対応するソースからの `SignatureElaborated` の導出が
  あることを示す。`src/signature_registration_context.taut` は、この宣言処理全体で
  型式の文脈を保つことを示す。`src/program_signature_sources.taut` は返す署名列が
  ソース中の本体を持つ関数を順番どおりに含むことを示す。
  `src/classes_normal.taut`・`src/instances_normal.taut` はクラス・インスタンス準備が
  通常の型位置を保つことを示し、`src/prepare_signature_sources.taut` は準備全体で
  ソースの署名列を接続する。`src/run_function_signatures.taut` の
  `types_check_function_signatures` は、最終診断が空なら最終データ環境でソースの各関数に
  署名の導出があることを示す。
  `src/rules_registered_signatures.taut` は、本体検査用の署名列と名前検索用の関数表の一致を
  定義する。`src/signature_table_frame.taut` は署名を読む処理が関数表を保つことを示し、
  `src/function_table_registration.taut` は登録直後の検索と別名の登録による保存を示す。
  `src/program_function_registered.taut` の `ck_program_decls_registered` は、入力の関数表が
  整列しソースの関数・extern の名前が一意なら、宣言列が返す各署名を最終の関数表から
  そのまま検索できることを示す。`src/prepare_function_registered.taut` はクラス・インスタンス・
  前置きの宣言を含む準備全体を接続する。`src/run_registered_functions.taut` の
  `types_check_registered_functions` は、最終診断が空なら、本体を持つソース関数の署名の導出と
  その検索が一致する共通の関数環境があることを示す。この環境は宣言準備時のもので、
  `src/tracked_body_frame.taut` と `src/tracked_finish_sound.taut` は、この関数表が
  本体検査から最終検査まで変わらず、登録された署名の検索が保たれることを示す。

* `src/rules_where.taut` は、クラス名の存在、宣言済み総称への制約、同じ組の重複がない
  制約列を定義する。`src/where_constraint_sound.taut`・`src/where_list_sound.taut` は
  一つの制約とその列の検査を接続する。`src/signature_where_sound.taut` の
  `ck_signature_where_sound` は、署名の検査後のクラス環境で、生成された述語列が
  ソースの `where` に対応することを示す。`src/where_order_sound.taut` は総称一覧の
  反転を通して導出を移し、`ck_signature_where_declared` で実際に署名に保存された総称を
  参照することを示す。インスタンス探索の健全性はこの定理に含まない。

上の保存定理は宣言環境を変えないことを示すもので、クラス解決や式の型付けの健全性の代わりにはならない。

### 層 4：基本値と名前の検索

`src/rules_local.taut` は同名の局所変数による隠蔽と、文字列・真偽値・局所変数の型付けを
定義する。`src/local_lookup_sound.taut` は `env_find` とこの束縛規則の両方向を示し、
`src/atomic_inference_sound.taut` はエラーなしの推論結果を型付けへ接続する。
`src/rules_function_reference.taut` は、局所変数に隠されない関数名と、総称・クラス制約を
持たない関数値の規則を定義する。`src/function_inference_sound.taut` はこの場合の推論の
健全性を示す。`src/substitute_empty_sound.taut` は空の置換が型の等しさを保つことを示す。
合併・タグ・型適用は置換時にも正規化されるため、構文上の等号とは区別する。
`src/rules_call.taut` は関数・借用された関数・型の等しさによる変換の呼び出し規則を定義する。
`src/argument_sound.taut` は引数列の照合が成功すれば、最後の状態ですべての引数が対応する
パラメータへ適合することを示す。`src/call_result_sound.taut` の `ck_app_result_sound` は、
確定した関数型・未確定の型変数の単一化・関数でない型の拒否を含む、呼び出し結果の検査を
この規則へつなぐ。既知のパラメータを使って先行検査した経路では、その検査が最終状態で
成立すること（`KnownCallArguments`）を前提に取る。この前提と、呼び出し先・引数の式の
型付けは、推論全体から導かない。`src/argument_inference_count.taut` はエラーなしの
引数推論がソースと同じ個数の型を返すことを示す。
`src/rules_literal.taut` は数値の解析、幅の条件、型の等しさによる自然数リテラルの規則を
定義する。`ck_infer_natural_recorded` は式推論の成功から解析値・型・位置の記録を導き、
`natural_record_checked_sound` はその記録の最終検査から型付けを導く。最終検査は、幅の
既定値を補った後でも未解決・非整数型のリテラルを拒否する。`ck_finish_natural_sound` は最終検査中の記録の保持と rigid な総称の条件の解消を含み、
`ck_infer_natural_final_sound` は単独の自然数式を推論から最終検査までつなぐ。
`src/tracked_inference_frame.taut` は、相互再帰する式・パターンの推論を通して、
既存のリテラル・種・型構成子・クラス制約の記録が残り、関数表が変わらないことを示す。
記録の追加は許す。
`src/tracked_body_frame.taut` は関数本体列とトップレベル文へ接続し、
`src/tracked_natural_final_sound.taut` は後続の検査を経た記録から最終的な型付けを導く。
`src/stable_state_frame.taut` は単一化・適合性・合併について、
`src/instantiation_stable_frame.taut` は具体化について、記録と関数表の保持を証明する。
`src/widen_stable_frame.taut` は、置換を広げるため `Grows` では扱えないハンドラの結果型の
更新についても、この二つが保持されることを示す。
`src/instantiation_domain_sound.taut` は具体化の置換表が全総称名を含むことを示す。
`src/where_predicates_declared.taut` は、署名の `where` の各述語が宣言された総称を参照する
ことを取り出す。`src/instantiation_scheme_records.taut` の
`ck_signature_instantiation_records` は、検査済みの署名の具体化が同じ置換表で戻り値の型を
作り、各クラス制約を利用箇所の仮定とともに最終検査用の記録へ追加することを示す。
`src/instantiation_obligations.taut` の `ck_signature_instantiation_obligations` はさらに、
同じ置換表の各束縛に対して型・型構成子の種の制約を記録し、後続の具体化とクラス制約の
追加でその記録が保たれることを示す。`src/rules_kind_bindings.taut` は宣言順に環境を
拡張する種の規則を定義する。通常の総称では `ck_instantiate_map_final_kinds` が、具体化から
最終検査までをこの規則へ接続する。`src/tracked_instantiation_sound.taut` は、後続の
式・本体の検査でも、型と各制約が同じ置換表に対応することを保存する。
`ck_signature_instance_continued_kinds` は署名の具体化と後続検査から、最終状態で種が
正しい具体化を導く。総称に解決されるクラス制約も `continued_instance_predicate_parameter`
で利用箇所の仮定へ接続する。

ハンドラは全操作腕の結果を集めた後、その結果型を継続へ与えて操作腕を再検査する。
後の腕で結果が広がる前に、先の腕が継続の戻り値を狭い型で使う誤受理を防ぐ。
再検査では当該ハンドラの結果の置換を書き換えず、腕の型が結果型へ適合することを確認する。
`src/expect_sound.taut` の `ck_expect_sound` と
`src/handler_result_sound.taut` の `ck_handle_validate_sound` は、この照合がエラーなしなら
後の検査状態で `TySub` が成り立つことを示す。合併型の要素への適合もこの規則に帰着する。
`src/widen_substitution_sound.taut` は、結果を広げる処理が自身の結果変数以外の
代入を保つことを示す。その変数が未使用だった時点の代入表については、全束縛を保つ。
`src/substitution_freshness.taut` は未割当の番号に束縛がない条件を、
`src/type_allocation.taut` は型に含まれる番号が割当済みである条件を定める。
`src/allocation_normalization.taut`・`src/allocation_resolution.taut` は正規化と型解決、
`src/allocation_state.taut`・`src/binding_allocation.taut` は初期状態、新規割当、代入更新、
変数束縛について、この範囲を保つことを示す。`src/allocation_substitution.taut` と
`src/allocation_poly_map.taut` は総称置換と多相型間の名前対応について同じ範囲を保つ。
rigid な置換表には全総称名が存在するため、名前対応の既定値の `TyVar(0)` は使われない。
`src/typing_state_extension.taut` は型付けに必要な状態の拡張を定め、
`src/widen_typing_sound.taut` の `ck_handle_widen_preserves_arguments` は結果変数の
割当前の状態で成立した引数の適合性が型拡張後にも成立することを示す。
`src/unify_allocation_sound.taut` の `ck_unify_allocation` と
`ck_attempt_unify_allocation` は、型解決・型引数列・型構成子の適用・多相型を含む
単一化全体と失敗時の復元について、割当カウンタと割当範囲を保存することを示す。
`src/instance_allocation_sound.taut` は適合性判定で使う多相型の具体化について、
割当カウンタが後退せず、生成した置換表と置換後の型が最終的な割当範囲に収まることを示す。
`src/fits_allocation_sound.taut` は15個の相互再帰関数を燃料への帰納法でまとめ、
適合性判定と試行的な判定が割当範囲を保ち、割当カウンタが後退しないことを示す。
`src/join_allocation_sound.taut` は型合併の状態と返される型、
`src/widen_allocation_sound.taut` はハンドラの結果型拡張について範囲の保存を示す。
`src/instantiation_allocation_sound.taut` は関数・効果の具体化について、生成された
置換表と返される型が割当範囲に収まることを示す。局所変数の検索・束縛と引数束縛、
新規変数列の生成は `src/local_allocation_sound.taut`・
`src/local_parameters_allocation.taut`・`src/fresh_allocation_sound.taut` で接続する。
`src/data_field_allocation.taut` はデータ型引数によるフィールドの置換を、
`src/constructor_allocation_sound.taut`・`src/lookup_allocation_sound.taut` は
コンストラクタ生成と全名前検索経路を、`src/field_allocation_sound.taut` は借用と
`Info` を含むフィールド参照を扱う。これらは入力の宣言表・局所環境の範囲を前提とする。
`src/argument_allocation_sound.taut` は引数列の照合、
`src/call_allocation_sound.taut` は既知の関数と未確定の関数への呼び出し結果、
`src/effect_allocation_sound.taut` は効果署名の具体化と `perform` の結果を接続する。
`src/control_allocation_sound.taut` は期待型・戻り値・budget の照合を扱う。
`src/written_allocation_sound.taut` は型注釈の宣言的な導出から割当範囲を導く。
`src/written_counter_sound.taut` は注釈を読む相互再帰全体でカウンタが後退しないことを、
`src/written_state_allocation.taut` は既存の置換と割当範囲を保ち、成功時に返す型も
範囲内に収まることを示す。
`src/data_body_allocation_sound.taut` は登録・再検査済みのデータ宣言のフィールド型が
任意の割当上限に収まることを示す（特に上限 0 でも成立し、推論変数を含まない）。
`types_check_data_bodies_allocated` はこの性質を最終診断が空のプログラムへ接続する。
自己ホストの証明テストは、llk・nibcheck・scan・text の証明群を
公理なしの基準で検査する。実行用の tote や明示的な公理のライブラリを同じ
証明環境に混ぜない。実行コードへの抽出では、消去される命題のレコードをフィールド名の
候補から除く。

同名のコンストラクタを値として参照した箇所は、`TyConstructorUse` に名前・型変数・位置を
記録する。`ck_resolve_constructor_uses` は整数の既定幅を補う前に、制約から分かった
結果型の名前で所有する型を選ぶ。他の参照の解決で型が決まることがあるため、未解決の
件数が減る間は繰り返す。決まらない参照は候補の修飾名を伴う診断になる。
構造体にも修飾名を登録し、レポートでは一意な非修飾名と必要な修飾名を表示する。
`src/constructor_resolution_frame.taut` は、この処理が宣言環境と置換の整列を保ち、
既存のエラーを成功として扱わないことを示す。

### 層 5：クラスの仮定と最終検査

`src/rules_class_assumption.taut` は文脈にある制約と、`DecEq` から `PartialEq` を得る
規則を定義する。`src/class_assumption_sound.taut` は仮定検索をこの規則へ接続する。
`src/final_class_parameter_sound.taut` の `final_parameter_class` は、最終診断が空で
記録された制約の型が総称に解決されたなら、その総称のクラスが利用箇所の仮定から導ける
ことを示す。構造的クラスと利用者定義クラスの両方を扱う。

構造的なクラス判定の燃料切れは拒否する。型変数を含むだけで構造全体の検査を省略する
分岐も除いた。これにより `fn identity(x) { x }; identity == identity` の誤受理を防ぐ。
未確定の要素型を持つ空リスト同士の比較は引き続き受理する。
`src/structural_fuel_sound.taut` は燃料切れと関数型の拒否を、
`src/final_pending_sound.taut` は記録された制約の最終検査と、関数型に対する構造的クラスの
制約が成功しないことを示す。

## 差分試験の実行ファイルのキャッシュ

`tools/selfhost-harness/src/native_cache.rs` は、差分試験に使う tote の release 実行ファイルを
内容アドレスで保存する。実行結果や証明の判定は保存しない。呼び出すたびに tote が実行され、
独立カーネルを含む比較対象の検査も実行される。

* tote の鍵は、推移的な依存のマニフェスト、選ばれたソースと import、`include_text!` の
  読み込み先、構文表、およびコンパイラの鍵から作る。読めなかった include のパスと、
  include の境界を決める祖先の `Tauto.eure` も追跡する。無関係な tote の本文は鍵に入らない。
* コンパイラの鍵は、正規化したソースの絶対パス、コンパイラ・生成器・実行時のソース、
  埋め込む prelude、ロックファイル、設定と環境、Rust ツールチェーンの内容を含む。
  環境は保守的に、子プロセスへ渡すもの全体をハッシュするため、ビルドに影響しない環境の変更でも失効する。
  呼び出し元の試験用に設定された既知のライブラリ検索パス、`CARGO_BIN_EXE_*` とシェルの `_` は渡さず、
  コンパイラのビルド自身が環境を設定する。
  同じコンパイラの tote はそのコンパイラのビルド領域を共有するが、別のソース配置や
  コンパイラの鍵とは共有しない。生成物の中間領域も明示した target の内側に置く。
* Rust ツールチェーンはプロセス内で最初に内容をハッシュする。以後は全ファイルの集合と
  device、inode、サイズ、mtime、ctime（ナノ秒まで）を照合し、一致する場合だけその
  内容ハッシュを再利用する。細かい時刻を持たない環境では再利用しない。
  これはローカルのファイルシステムとインストールされたツールチェーンを信頼する仕組みで、
  OS やシステムライブラリ全体の真正性を保証するものではない。
* 独自のホスト依存、wrapper、設定の間接参照、未対応のフラグ、シンボリックリンクなどで
  入力を閉じて追跡できないときは、再利用せず独立した領域でビルドする。ビルド中やロック待ちの
  間に入力が変わった場合は、古い鍵で返さず再実行を求める。
  生成した Rust を整形する実行ファイルも同じツールチェーンの内容として追跡する。
  `RUSTFMT` による差し替えや独自の整形設定がある場合は再利用しない。
* 同じ tote の生成はプロセス間ロックで直列化する。実行ファイルを専用の一時ファイルへ
  コピーし、内容を照合したあとに記録を rename する。成功記録のないもの、サイズや
  SHA-256 が一致しないものは使わない。キャッシュのパスの既存シンボリックリンクは拒否する。
  失敗は記憶しない。使用中のパスを消さないため、公開済みの実行ファイルは自動削除しない。
* 保存先は `$TAUTO_TARGET_DIR`、なければ `$CARGO_TARGET_DIR`、それもなければリポジトリの
  `target` の中の `selfhost-harness-cache/v1`。生成中の専用領域はビルドの結果を受け取った時点で除去する。強制終了で残った領域、公開済みの
  実行ファイルとコンパイラの領域は、その target を明示的に掃除するときに除去する。
  `TAUTO_SELFHOST_CACHE_TRACE` を設定すると、検証済みの hit、miss、再利用しない build を表示する。

## 証明のキャッシュ（`crates/tauto-kernel/src/check/cache.rs`）

一度検査を通った定理の証明は、それが依るものが変わらない限り検査し直さない（項目ごと、内容アドレス）。

* **鍵**は SHA-256 で、検査器自身のソース、束縛済みの定理、検査環境から作る。
  環境には宣言の型、展開される値、族と構成子の対応、公理依存、instance を含む。
  位置は鍵から除き、宣言の参照と局所束縛は環境内の番号で表す。
* 定理の証明は展開される値に含まれないため、証明だけを書き換えても使う側は無効にならない。
  検査環境の型・値・instance が変わった場合は、その環境で検査する項の鍵が変わる。
* 保存された宣言の番号は、その鍵を作った環境の参照表から ID に結び付く。
  表示名をソース名として読み直さない。局所束縛とその使用箇所も番号を共有する。
  未解決の参照や表にない番号を持つ項は使わず、精密化から検査し直す。
* キャッシュに当たっても、文はキャッシュがないときと同じく精密化され、二つの検査器（`check.rs` と `check/core.rs`）が
  検査する。証明だけを検査済みとして扱う。失敗・未完の宣言を名指す定理はキャッシュしない。
* 関数（`mutual` の組を含む）は値が展開されるので、同じ作りの鍵で精密化した項を保存する。鍵は検査器の
  ソースを含むので、当たった項はこの検査器が一度検査したものであり、定理の証明と同じく検査済みとして扱う。
  当たったときは精密化と両方の検査を省き、`check/core.rs` は文（型）だけを検査して値を展開できるようにする。
  証明の検査をキャッシュで省くのと同じ信頼で、関数の値の検査も省く（同じ検査器で検査し直しても結果は変わらないため）。
  保存された項が文を通らなければ（壊れたキャッシュなど）、精密化からやり直して書き直す。
  no-confusion は作り直し、コアが検査する。
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
| 6 | nibcheck の健全性：関数本体・トップレベルの式・最終診断を含む検査全体が `datas` を保つこと、データと関数の宣言（種・借用の制約を含む）が宣言的な規則でよく形成されていること、層 4〜8（式、クラス、効果、線形性、全体）の健全性 |
| 7 | 宣言の整形式性の宣言的な規則と、最終レポートの各診断の条件をその規則へ移す証明 |
| 8 | 複合した型式（型適用、関数型）の名前解決の規則、署名の推論変数の解決、戻り値の借用制約、署名全体の整形式性、登録表の検索、extern・生成された関数、署名の具体化と式の型付け |
| 9 | 型構成子の種の規則、記録後のクラス解決全体、複合式と本体全体の型付け、式推論全体での範囲の保存、実際の推論経路から前提を導く接続 |
| 10 | record 構築とパターンの同名コンストラクタを期待型から選ぶ処理（自己ホスト版）、ハンドラ全体の式・効果・継続の型付けの証明 |
| 11 | データ構造のクラス導出とインスタンス探索全体の健全性 |

## native checker の比較

`CARGO_PROFILE_BENCH_LTO=thin cargo bench --manifest-path tools/selfhost-harness/Cargo.toml --bench compiler`
は `totes/nibcheck` の rows・types・lin を Rust 実装と比較する。bench の LTO を
生成 crate の release 設定（thin LTO）に揃える。双方が同じファイルを読み、マクロを実行しない構文読み取りから同じ
診断の出力までを行う。カーネル検査、精密化、コード生成を含むコンパイラ全体の比較ではない。

各標本は別プロセスで、起動・ファイル読み取り・表と prelude の準備・出力・終了を含む。
最初の標本と、それ以降の中央値・95 パーセンタイルを区別する。後者で温まるのは
ファイルシステムのキャッシュであり、プロセス内のキャッシュではない。OS のキャッシュを
消さないため、最初の標本もディスクの cold-start とは呼ばない。実行順は交互にする。
各標本の標準出力が Rust の参照出力と完全に一致しなければ比較は失敗する。

`--samples N` は最初の標本の後の標本数、`--filter TEXT` は corpus の入力名の絞り込み、
`--native PATH` は生成済みの native 実行ファイル、`--analysis rows|types|lin` は対象の分析を指定する。
絞り込みと入力数を報告に残す。中央値は偶数個なら中央の二値の平均、95 パーセンタイルは
nearest-rank とする。
生成物と Rust 側で同じ最適化設定を使う。表の読み取りを除いた値や一部の入力の値を
全体の速度として扱わない。
