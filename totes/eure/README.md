# eure

データ記述言語 [Eure](https://github.com/hihaheho/eure) の読み書き。テキストを文書（`Node`）に読み、文書を Eure のテキストに書き出し、形（`Shape`）に合っているかを検査する。依存はなく（10 進数の読み書きは `src/decimal.taut`）、公理を使わずに検査が通る。

```
parse("name = \"tauto\"\nversion = 3\n")
  -- parsed(map_node([entry("name", str_node("tauto")), entry("version", nat_node(3))]))
parse("a = 1\na = 2\n")
  -- parse_error(6, "a path that has no value yet")
```

## 文書

`src/value.taut`。文書は `Node` で、値と拡張（`$name` の付いた、データではない情報）を持つ。

| 値 | 書き方 |
| --- | --- |
| `vhole(None)`・`vhole(Some(l))` | `!`・`!label`（まだ埋まっていない値） |
| `vnull`・`vbool(b)` | `null`・`true`・`false` |
| `vint(neg, n)` | `-12`、`1_000` |
| `vdec(neg, mant, eneg, exp)` | `1.25`、`5e-3`。`± mant × 10^(± exp)` を書いたとおりに持つ（`1.10` と `1.1` は別の値） |
| `vtext(lang, t)` | `"…"`・`'…'`・`: …`（`plaintext`）、`` `…` ``・言語のないコードブロック（`implicit`）、`` rust`…` ``・` ```rust ` のブロック（`named`） |
| `varr(xs)`・`vtup(xs)` | `[1, 2]`・`(1, "a")` |
| `vmap(entries)` | `{ k => v }`、`k = v` の並び、`k { … }`、`@ k` |

map のキー（`Key`）は文字列・整数・キーの組。`name`・`"name"`・`'name'` は同じキー。
読むための関数: `get`、`field`、`ext`、`at`（名前のパス）、`as_text`・`as_bool`・`as_nat`・`as_items`・`as_entries`。

## 読む

`src/read.taut` がテキストを文（`src/syntax.taut` の `Stmt`）に読み、`src/lower.taut` がパスをたどって文書を作る。`src/eure.taut` の `parse` が両方を行い、`parsed(doc)` か、問題のあったバイト位置と期待したものの `parse_error(at, what)` を返す。

- 束縛 `a.b = v`、`a: テキスト`（行末まで、前後の空白を除く）、ブロック `a { … }`、根の値 `= v`。
- セクション `@ a.b` は次のセクションまでの束縛を、`@ a.b { … }` は中の束縛を `a.b` の下に置く。
- パスの段: 名前、`"…"`、整数、キーの組 `(1, "a")`、拡張 `$name`、配列の `[]`（末尾に新しい要素）と `[n]`、組の `#n`。`@ indexes[]` を繰り返すと要素が増える。
- 文字列のエスケープ `\\ \" \' \n \r \t \0 \u{…}`、`\` での連結 `"a" \ "b"`、`//` と `/* */` のコメント。
- コードブロックは 3 から 6 個のバッククォートで、閉じるバッククォートの前の空白を各行から取る。
- 同じパスに二度値を与えるのは誤り。書いた `!` も値なので、後から値を与えたり中に入ったりするのは誤り。パスが作っただけのまだ値のないノードに入ると、段に応じて map・配列・組になる。中身のないブロックとセクションは空の map、拡張だけのノードは `!`。

どの読み取りも入力の長さより多い燃料で構造的に再帰するので、どんな入力でも止まる。

## 書く

`src/write.taut` の `to_text(doc)`。map は `key { … }` のブロックで一行に一つの束縛、ほかは `key = [1, "a", { k => v, }]` のようにその場に書く。拡張のある値は `{ = v, $name => w, }`。名前として書けるキーは引用符なしで書く。コードは改行もバッククォートもなければ `` lang`…` ``、それ以外はブロック。

## 形

`src/shape.taut`。`Shape` は文書に期待するもの: `text_s`・`bool_s`・`int_s`・`nat_s`・`array_s(item)`・`map_of_s(value)`・`any_s`、レコードは `field_s(name, optional, shape, rest)` を並べて `fields_end`（ほかのキーも許す）か `closed_end`（許さない）で終える。`check(shape, doc)` は合わない場所を `problem("indexes[0].id", "this field")` の形ですべて返し、`conforms` はそれが空かどうか。

## 証明していること

- `proof/roundtrip.taut`: 文書全体の往復 `roundtrip`。`wf_node(d) = yes` のどの文書 `d` でも `parse(to_text(d)) = parsed(d)`。`wf_node`（`proof/doc.taut`）が求めるのは、ラベルと拡張の名前が名前であること、キーが文字列か整数であること、同じ map に同じキーが、同じノードに同じ拡張が二度ないこと、コードが改行もバッククォートも含まずその場に書けること。証明は次の層に分かれる。
  - `proof/values.taut` の `node_back`: その場に書いた値（配列・組・`{ k => v, }`・`{ = v, $e => w, }`・スカラー）を `read_value` が読むと、`expr_node(d)` が返る。
  - `proof/build.taut` の `node_lower`・`node_unblank`: その式を `lower_expr` で組み立てると `d` に戻り、`unblank` は何も変えない。
  - `proof/stmts.taut` の `st_entries`・`st_exts`: `key = v` の行・`key { … }` のブロック・`$name = v` の行を、入れ子も含めて `read_stmts` が読み戻す。
  - `proof/lowstmts.taut` の `lw_entries`・`lw_exts`: 読んだ文を `lower_stmts` が組み立てると元の map と拡張になる。ブロックの中の文は、外側の文書のどこを書き換えるかを表す `Ctx` の下で扱う。
  - 燃料は、読む位置からの残りのバイト数で上から押さえる（`proof/mono.taut`）。`read_eure` が渡す `4 × (長さ + 1)` で足りる。
- `proof/strings.taut`: `read_put_string`。どのテキスト `t` と後続 `r` でも、`read_string(put_string(t, r)) = rd(text_bytes(t), r)`。エスケープする 6 種のバイトとそれ以外のバイトの場合分けと、燃料が足りること（`Escape::longer`）。
- `proof/numbers.taut`: 数の往復。後続 `r` が数の続き（数字・`_`・`.` と数字・`e`・`E`・`f32`・`f64`）で始まらなければ、
  - `read_put_int`: `read_int(put_int(neg, n, r)) = rd(Pair { fst: neg, snd: n }, r)`
  - `read_put_vint`: `read_number(put_scalar(vint(neg, n), r)) = rd(vint(neg, n), r)`
  - `read_put_vdec`: `read_number(put_scalar(vdec(neg, mant, eneg, e), r)) = rd(vdec(neg, mant, eneg, e), r)`
- `proof/keys.taut`: パスのキーの往復。後続 `r` が名前の続きのバイトで始まらなければ、
  - `read_seg_put_str`: `read_seg(put_key(kstr(t), r)) = rd(skey(kstr(t)), r)`（名前として書いたときも引用符で書いたときも）
  - `read_seg_put_num`: `read_seg(put_key(knum(neg, n), r)) = rd(skey(knum(neg, n)), r)`
- `examples/basic.taut`: 束縛・パス・セクション・`[]`・テキスト束縛・コードブロック・拡張・文字列のエスケープの読み取り、誤りの位置、書き出した文字列、書き出したものを読むと同じ文書に戻ること（すべて `refl`）。
- `examples/trust.taut`: tote の `Trust.eure` と同じ形のポリシーを読み、形で検査し（合わないポリシーでは問題の一覧）、`@ indexes[]` の別名や `defaults.min_age` を取り出す。
- `tests/src/roots.taut`: 根が map でない文書（`= 1`、配列、拡張のある値）を書いて読むと同じ文書に戻ること（`refl`）。
- `tests/src/errors.taut`: 読まないものと誤りの位置と理由（同じパスへの二度目の値、`!` への値、値の下のキー、`inf`、`f32`、負の添字、閉じていない文字列）と、拡張だけのノードが `!` になること（すべて `refl`）。

すべて公理を使わない。

## Eure の実装との違い・まだないもの

- 往復の証明は、タプルのキーと、その場に書けないコード（改行かバッククォートを含み、ブロックで書くもの）を除く。そうした文書も例では往復するが、証明はまだない。
- 読まないもの: 集合 `#{…}`、`inf`・`nan`、`f32`・`f64` の付いた数、区切り付きの文字列とコード（`<'…'>`、`` <`…`> ``）、配列の `[^]`、キーの穴。読めない理由は `parse_error` で返す。
- 名前に使えるのは ASCII の英字・数字・`_`・`-` と、ASCII でない文字（Unicode の識別子の規則は見ていない）。
- Eure のスキーマ（`$types` などを Eure で書いたもの）は読まない。形は Tauto の値として書く。
- 証明側の `Text` で書いているので遅い。`tools/selfhost-harness/tests/eure.rs` はリポジトリの `.eure` と `Tauto.lock` をすべて読み、`eure-reader` と同じ文書になるかを比べる（小数は値を比べない）。

## 検査

```sh
for f in src/*.taut proof/*.taut tests/src/*.taut examples/*.taut; do tauto check "$f"; tauto lint "$f"; done  # examples は計算に数分かかる
tauto fmt --check src/*.taut proof/*.taut tests/src/*.taut examples/*.taut
```
