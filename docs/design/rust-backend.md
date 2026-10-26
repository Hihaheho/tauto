# Nib / tauto の Rust バックエンドと相互運用：設計

[`ownership.md`](ownership.md)（以下 **OWN**）の種・借用・再開量を前提にする。

この文書は長い。全部を一度に読む必要はないが、**「設計の原則」と「要約」** を先に読む。その後は、知りたい節だけを読めばよい。

---

## 設計の原則

- **カーネルは変えない。** 証明・型・命題の扱いはそのまま。第 I 部の構文はカーネルの扱う項に展開されるか、型の位置で消えるか、中身のない公理（extern）になる。
- **生成コードに `unsafe` を入れない。** `tauto-rt` にも入れない。`#![forbid(unsafe_code)]` を `tauto-rt` と生成コードの両方に付けるので、違反はビルドが落ちて分かる（O 層の駆動は `Waker::noop()` で足りる）。
- **所有権の判断は `lin.rs` が一手に持つ。** バックエンドは独自に所有権を推論せず、`lin.rs` の結果をそのまま使う。二つの検査器が食い違ったときにどちらが正しいか分からなくなるのを避ける。rustc の検査は、`lin.rs` の判断を確かめ直す二つ目の検査器として働く。
- **rustc の指摘を `.clone()` や `Rc<RefCell<…>>` で黙らせない。** clone を足すのは「型の写像」「式と文の生成」が clone と定める場所だけ、`Rc<RefCell<…>>` に包むのは「`var` の表現」の表が定める場合だけ。rustc が「moved value」と言うなら、それは `lin.rs` か生成器の誤りの報せである。
- **インタプリタ `eval.rs` は参照実装として残る。** 実行の意味の正は `eval.rs` で、生成コードは同じ出力を返す。
- **依存は増やさない。** 外部の crate を足すのは「Cargo の生成と `tauto build`」が挙げるものに限る。
- **一つのことに二つの書き方を作らない。** たとえば `direct` の腕に `k` を省く糖衣、`?` 演算子、メソッド呼び出し構文は入れない。

---

## 要約

1. tauto（Nib）のプログラムを **安全な Rust のソース** に変換するバックエンドを持つ。生成コードは `#![forbid(unsafe_code)]`。rustc の型検査と借用検査が `lin.rs` の判断を確かめ直す「二つ目の検査器」になる。
2. 前段（構文・型・行・`lin.rs`）はそのまま使う。その後ろに中間表現 **NIR**（`crates/tauto-nir`）、Rust の生成（`crates/tauto-rustgen`）、実行時（`crates/tauto-rt`）がある。
3. 種は Rust にそのまま写る：copy → `Copy`、shared → `Clone`（`Rc`）、affine → 所有、linear → 所有 + debug の drop bomb。借用 `&x` / `&mut x` は Rust の `&` / `&mut`。
4. 効果は行の再開量で四つの **層** に分ける：S（効果なし・direct だけ）→ 普通の `fn`、A（`resume 0`）→ `Result` と `?`、O（`<=1` と `1`）→ `async` を自前の同期ドライバで回す、M（`ω`）→ 複製できる状態機械。
5. 言語の側に六つの機能がある（第 I 部の「`direct` 操作」〜「名前空間」）：`direct` 操作、`Result` と `fail` / `raise` / `catch` と `&Slice(A)`、view 型、`-> &mut A` と `let &mut x`、中立な `extern` と `Tauto.eure` の `rust` 節、名前空間。どれも Nib の層のもので、カーネルに規則を足さない。
6. `direct` 操作の腕は、どの経路も末尾が `k(e)` で終わり、`k` はそこにしか現れない（末尾再開）。行が direct だけなら S 層で、継続を作らない。
7. `Result(T, E)` は値のまま。`raise` で効果 `fail(E)` に変え、`catch` で `Result` に戻す。`?` の構文は入れない。
8. `extern { … }` は言語として中立。Rust のどのパスに対応するかは `Tauto.eure` の `rust` 節が決める。
9. Rust のクレートは、手書きの `extern`、または `tauto bind` が rustdoc JSON から生成する `bind/<crate>.taut` と `bind/<crate>.eure` で使う。生成物はコミットする。
10. Rust から tauto を使うときは `crates/tauto-build` を `build.rs` から呼ぶ。
11. 正しさは三つで確かめる：rustc による再検査、`eval.rs` との差分比較、drop bomb と動的所有権検査の照合。

---

## 用語

| 用語 | 意味 |
|---|---|
| OWN | [`ownership.md`](ownership.md)。種・借用・再開量・CFL の仕様。 |
| 種（kind） | `copy ⊑ shared ⊑ affine ⊑ linear`（OWN「種」）。 |
| 複製可 | 種が copy か shared。 |
| 再開量（quant） | 効果の宣言の `resume 0 / <=1 / 1 / ω`（OWN「宣言」）と `direct`（「`direct` 操作」）。 |
| direct 操作 | 腕のどの経路も末尾の `k(e)` で終わる操作（「`direct` 操作」）。 |
| 層（tier） | 生成する Rust の形。`S ⊑ A ⊑ O ⊑ M`（「層の決定と単相化」）。 |
| 関数の実体（instance） | 一つの `fn` を「行変数を実体化した層」と「budget の下か」で単相化したもの（「単相化の鍵」）。通常の Rust の関数一つに当たる。再開しない budget には別の同期実体を生成できる（「再開しない budget の同期実体」）。 |
| NIR | Nib IR。型・種・行・層が付いた A 正規形の中間表現（「NIR」）。 |
| 証拠（evidence）、`Ev` | direct 操作の腕を探すための、実行時のハンドラの連鎖（「S 層と direct の操作（証拠 `Ev`）」）。 |
| 入れ物（slot） | O 層で `perform` の要求と答えを置く、スレッドに一つの場所（「O 層（`resume <=1` と `resume 1`）」）。 |
| 中継（forward） | O 層のハンドラが、自分の操作でない要求を外のハンドラに任せること（「`handle`（本体が O 層のとき）」）。 |
| view 型 | 借用を抱える二級の値の型（「view 型」）。`Option(&T)`、Rust の `Iter<'a, T>` に当たる extern の型など。 |
| tote | `Tauto.eure` で定義される、ビルド・依存・配布の単位（Rust の crate に当たる）。 |
| 橋渡しクレート（bridge） | 利用者が tote の中に書く Rust のクレート。名前は `<tote 名>-bridge` に決まっている。自動の変換で足りないときに Rust の関数を書いて渡す（「橋渡しクレート（bridge）」）。 |
| drop bomb | debug ビルドで、linear の値が消費されずに捨てられたら panic する印（「drop bomb（linear）」）。 |

---

# 第 I 部　言語の側

六つの機能はどれも **Nib の層**（`surface.rs`、`types.rs`、`rows.rs`、`lin.rs`、`fmt.rs`、`tauto.par`）にあり、カーネルに規則を足さない。カーネルから見れば、これらの構文はカーネルの扱う項に展開されるか、型の位置で消えるか、中身のない公理（extern）になる。

各節は同じ順で書く：構文 → 型と行の規則 → 所有権の規則（`lin.rs`）→ 実行時（`eval.rs`）→ エラーの文。

---

## `direct` 操作

### 何のためか

腕が「値を返して、その場で続ける」だけの操作を、型で分かるようにする。`direct` の操作だけを行うコードは中断も打ち切りもしないので、Rust では普通の関数呼び出しになり（S 層）、Rust の高階関数に閉包として渡せ、Rust から trait の実装を渡して呼べる。tauto 単体でも、linear の値を跨がせられる、腕が `&mut` を捕まえられる、という利点がある。

### 構文

```nib
effect log: (t: Text) -> () direct
effect get: () -> i64 direct
effect put: (v: i64) -> () direct
effect Store = {get, put}          // 効果の集まりの書き方は direct でない効果と同じ

var out = buf_new()
var s = 0
handle { body } with {
  log(t), k => k(buf_push(&mut out, &t))
  get(), k => k(s)
  put(v), k => k({ s := v })
}
```

`tauto.par`：

- キーワード `KwDirect: 'direct'` がある（`KwResume` と同じ状態集合）。
- `EffectSignature` の末尾：`[ KwResume Quant | KwDirect ]`。`resume` と `direct` を両方は書けない（構文で一つしか書けない形にする）。
- `Generic` の行変数の境界に `direct` を許す：`<e: direct>`。
- 腕の構文は他の効果と同じ（`op(p…), k => e`）。

`surface.rs`：効果の宣言の `resume: Quant` を `Quant` の値 `Quant::Direct` で表す（別のフィールドにしない）。`fmt.rs` は `direct` を `resume` と同じ位置に出す。

### 規則

**D1（腕の形：末尾再開）。** direct の操作の腕の本体は、次の **末尾形** `T` でなければならない。これは構文の検査で、型推論を使わない。

```text
T ::= k(e)                                  e に k が現れない
    | { s1; …; sn; T }                      s1 … sn に k が現れない（let、var、:=、式の文を含む）
    | if c { T } else { T }                 c に k が現れない。else は必須
    | match x { p1 => T, …, pm => T }       対象とガードに k が現れない。どの腕も T
```

- つまり **どの実行経路も、最後に `k(e)` を一度だけ呼んで終わる**。`k` はその位置以外に現れない（閉包の中、`let` の右辺、引数、入れ子の `handle` の中にも現れない）。
- 腕の中の `return`、`break`、`continue`（腕の外へ抜けるもの）は不可。腕の中に書いたループの中の `break` は、そのループが D2 で不可なので起こらない。
- 通る：
  - `log(t), k => k(())`
  - `log(t), k => { let s = fmt(t); buf_push(&mut out, &s); k(()) }`
  - `get(), k => if s > 0 { k(s) } else { k(0) }`
  - `get(), k => match m { Some(v) => k(v), None => { log_miss(); k(0) } }`
  - `log(t), k => k({ buf_push(&mut out, &t) })`（`e` がブロックでもよい）
- 通らない：`log(t), k => k(k(()))`、`log(t), k => ()`、`log(t) => ()`（`k` がない）、`log(t), k => { k(()); () }`（`k` が末尾でない）、`log(t), k => if b { k(()) } else { () }`（一つの経路が `k` で終わらない）、`log(t), k => { let g = () => k(()); g() }`（`k` を閉包が捕まえる）、`log(t), k => if b { k(()) }`（`else` がない）。
- エラー（`types`）：`"error: log is direct; every path of its arm must end in k(e)"`。`log` のところは操作の名前。
- 腕のパターン（`log("x"), k => …`）とガードは他の腕と同じに許す。
- **意味**：末尾形の腕は、各末尾 `k(e)` を `e` に置き換えた式 `T[e/k(e)]` を計算して、その値で一度 `k` を呼ぶのと同じ（評価の順が同じなので）。生成器（「direct のハンドラの生成」）はこの置き換えた式を腕の答えとして生成する。
- **書き方**：書く形は `{ s; k(e) }`。`k({ s; e })` も末尾形として受理し、意味は同じだが、`fmt.rs` が `{ s; k(e) }` に直す（`k` の引数が文を持つブロックなら、文を外に出す）。整形したコードには `{ s; k(e) }` の形だけが現れる。

**D2（腕が行える効果）。** direct の腕の `e` の行は、**direct の操作だけ** でなければならない。`resume 0`、`<=1`、`1`、`ω` の操作、`Div`（`while`、再帰、`unbounded`）、`Exceeded`、`Match(A)` はどれも不可。

- 腕の中から他の direct 操作は行える（外のハンドラに届く。腕は自分のハンドラの外で動く）。
- エラー（`rows`）：`"error: the arm of log performs ask, which is not direct"`。`Div` なら `"error: the arm of log performs Div, which is not direct"`。

**D3（行の量）。** `rows.rs` の行の量 `q(e)` には `Direct` がある。CFL（OWN「制御フロー線形性（CFL）の規則」）では `Direct` を `1` と同じに扱う（`q(ρ) \ {1}` の計算で `Direct` を `1` と見なす）。したがって linear の値も direct の効果を跨いで生きられる。

**D4（行変数の境界）。** `<e: direct>` に代入できるのは、direct の操作だけからなる行（空の行を含む）。`<e: <=1>` には direct の操作も代入できる（`1` と同じ扱い）。エラー（`rows`）：`"error: ask is not direct but e is direct"`。

**D5（腕の捕獲）。** OWN「腕と `k`」の「腕が外から捕まえる変数は複製可」は、**direct でない腕にだけ** 掛かる。direct の腕は、OWN「借用閉包」の借用閉包と同じ規則で、`handle` の外の借用の変数、`&x`、`&mut x`、affine な `var` を使ってよい。

- direct の腕は、`handle` の式の始まりで作られ、`handle` の式の終わりで消える **借用閉包** と見なす。腕が `&mut out`（または affine な `var` の `out` の move 以外の使用）を含むなら、`handle` の式の間、`out` は `&mut` で借用されている。`&out` だけなら `&` で借用されている。
- その間、`handle` の本体と、他の腕と、`return` 腕は、OWN「凍結」〜「一つの呼び出しの中の衝突」の衝突の規則に従う：`&mut` で借用された `out` は本体で一切使えない、`&` で借用された `out` は本体で `&` だけ使える。
- 腕が affine な値を **move** する（`consume(out)`）のは不可。腕は何度も走るので。エラー（`lin`）：`"error: the arm of log moves out, but it runs many times"`。
- 衝突のエラー（`lin`）：`"error: out is borrowed by the arm of log"`。
- 腕が `k` を捕まえる閉包を作ることは D1 によって起こらない。

**D6（`show`）。** 組み込みの `show` は direct：`effect show<A>: (name: Text, value: A) -> () direct`。ホストの応答は `()` を返すだけなので、末尾再開の腕と同じに動く。

### 実行時

`eval.rs` に direct のための規則はない。direct の腕は `resume 1` の腕と同じく動く（経路に沿って文を評価し、末尾の `k(e)` で `k` を呼ぶ）。D1〜D5 は静的な制限だけである。

`show` を処理する腕も D1 に従い、満たさない腕は型検査が拒否する。

## `Result`、`fail` / `raise` / `catch`、`Slice`

### 方針

- 失敗しうる Rust の API（`Result<T, E>`）は、tauto でも **`Result(T, E)` の値のまま** 受け渡しする。extern と公開 API の境界はいつも `Result`。
- 本体の中で失敗を自動で伝えたいときは、構文でなく std の関数で効果に変える。Rust の `?` に当たる構文は **入れない**。
- OWN「`extern`」の Rust の `Result<T, E>` と `Option<&T>` の行は、この節を指す。

### std にあるもの

`std/prelude/Std.taut`（`Option` と同じファイル）に次がある。

```nib
enum Result<T, E> { Ok(T), Err(E) }

effect fail<E>: (e: E) -> Never resume 0

// Result を効果に変える。Err なら fail(E) を行い、戻らない。
fn raise<T, E>(r: Result(T, E)) -> T ! {fail(E)} {
  match r {
    Ok(v) => v,
    Err(e) => perform fail(e),
  }
}

// 効果を Result に戻す。body の中の fail(E) を捕まえる。
fn catch<T, E, e>(&body: () -> T ! {fail(E), e}) -> Result(T, E) ! {e} {
  handle { Ok(body()) } with {
    fail(x) => Err(x)
  }
}
```

- `Result` の種は構造で決まる（`T` と `E` の join）。
- コンストラクタの名前は `Ok` / `Err`（Rust と同じ）。std の `Option` のコンストラクタの書き方（`Some` / `None`）と大文字・小文字をそろえる。`Option` のコンストラクタの大文字・小文字が変われば、`Result` もそれに合わせる。
- `perform fail(e)` の型 `Never` が `T` に収まらない（`types.rs` が `Never` を任意の型の部分型として扱わない）なら、`match perform fail(e) {}` と書く。
- `catch` の `body` は `&body`（借用閉包）。だから `catch(() => { … raise(…) … })` の閉包は `&mut` を捕まえてよい。

### 効果の型引数の同一性

`fail` は型引数つきの効果で、`fail(IoError)` と `fail(ParseError)` は **別の効果**（行の別の要素）。ハンドラの腕 `fail(x) => …` がどちらを処理するかは、`rows.rs` / `types.rs` が `State(T)` や `Exceeded(T)` の腕で型引数を決めているのと同じ方法で、本体の行と単一化して決める。本体の行に `fail(…)` が二つあって決まらなければエラー（`rows`）：`"error: fail is ambiguous here: fail(IoError) or fail(ParseError)"`。この場合は内側にもう一つ `catch` を書けばよい。

### 所有権

`fail` は `resume 0` なので、OWN「手で確かめる表」の通り、affine の値は `raise` を跨いで生きてよく（失敗すれば Drop される）、linear の値は跨げない。`fail` のための規則はない。

### `&Slice(A)`

- std に型 `Slice(A)` がある。`Slice(A)` は **借用の後ろにしか書けない**：`&s: Slice(A)` の引数、`&mut s: Slice(A)` の引数、`-> &Slice(A)` の結果、`let &s = …`。それ以外（`x: Slice(A)`、`Vec(Slice(A))`、構造体のフィールド）は型エラー `"error: Slice(A) can only be borrowed"`。
- 関数（組み込み）：

```nib
fn vec_as_slice<A: linear>(&v: Vec(A)) -> &Slice(A)
fn vec_as_mut_slice<A: linear>(&mut v: Vec(A)) -> &mut Slice(A)     // 「`-> &mut A` と `let &mut x`」の後
fn slice_len<A: linear>(&s: Slice(A)) -> u64
fn slice_get<A: linear>(&s: Slice(A), i: u64) -> Option(&A)          // 「view 型」の後
```

- `eval.rs` では `Slice(A)` の借用は `Vec(A)` の借用と同じ値で表してよい。
- Rust では `&[A]` / `&mut [A]`。`&Vec<A>` から `&[A]` への変換は deref（「自動の変換（これ以外はしない）」）。

## view 型

### 何のためか

Rust の API の多くは借用を抱える値を返す：`Option<&T>`、`slice::Iter<'a, T>`、`regex::Captures<'h>`、`Entry<'a, K, V>`。OWN の二級の借用は「`&A` を返す関数」までしか言えない。view 型は、借用を抱える値を **借用の変数と同じ二級の扱い** で受け取れるようにする。

### 何が view 型か

次の型を **view 型** と呼ぶ。

1. `&T`、`&mut T`（借用そのもの。OWN の `-> &A` の結果）。
2. `view` と宣言した extern の型：`view struct Iter(A) {}`（「extern の view 型」）。利用者が tauto で定義する struct / enum は view にできない。
3. std の `Option`、`Result`、`Pair` に view 型を入れたもの：`Option(&T)`、`Option(&mut T)`、`Result(&T, E)`、`Pair(&A, &B)`。

型変数は view 型で実体化できない（`fn f<A>(x: A)` に `Option(&T)` を渡すのは型エラー `"error: a view cannot be a type argument"`）。例外は 3 の std の三つの型だけで、これは型の宣言の特例として `types.rs` に書く。この制限のおかげで、生成する Rust のジェネリクスの型引数はいつも `'static` にできる（「借用、lifetime、型変数」）。

`&A ≡ A`（OWN「引数」）は view にも及ぶ：`A` が複製可なら `Option(&A) ≡ Option(A)`、`Pair(&A, &B)` も同様。`&mut` は複製可でも縮まない（`&mut A` は `A` ではない）。

### どこに書けるか

借用の変数（OWN「どこに書けるか」〜「借用の変数」）と同じ。

- 関数の結果：`-> Option(&A)`、`-> Iter(A)`。関数に少なくとも一つの借用の引数が要る（OWN「結果」と同じ。`"error: -> Option(&F) needs a borrowed parameter"`）。結果は **すべての借用の引数から派生する** と見なす。
- 受け取り：`let &x = f(&v)`、`var &x = f(&v)`（「`var &x`（view の可変な束縛）」）、`match f(&v) { … }`（その `match` の間だけ凍結）。
- 引数：view 型の値を `&x` / `&mut x` で渡す（`iter_next(&mut it)`）。
- できないこと：`let x = f(&v)`（`&` を書かずに受ける）、構造体・セル・`Vec` に入れる、効果の引数・結果にする、脱出する閉包に捕まえさせる、関数の結果として返す（返せるのは借用の引数から派生した view を、その関数の結果の型として返すときだけ）。エラーは OWN の借用のエラーと同じ文（`"error: a borrow cannot be stored"` など）を使う。

### `var &x`（view の可変な束縛）

イテレータのように **view 自身を進める** には `&mut` が要る。OWN では「`&mut` は `var` だけ」なので、view を可変に持つ束縛は `var &x` で書く。

```nib
var &it = vec_iter(&v)            // it: Iter(i64)。v はブロックの終わりまで凍結
while true {
  match iter_next(&mut it) {      // iter_next(&mut it: Iter(A)) -> Option(&A)
    Some(x) => perform show("x", x),
    None => break,
  }
}
```

- `var &x = e` は、`e` が view 型の値を返す呼び出しのときだけ書ける。`x` は view 型の借用の変数で、`&mut x` を渡せる。
- `x := e2` は **できない**（`"error: a view var cannot be reassigned"`）。凍結の範囲が変わるのを避けるため。
- 凍結は `let &x` と同じ（OWN「凍結」）：`x` の生きている間、`e` の借用の引数の持ち主は凍結される。

### `match` と view

- `match` の対象が view 型なら、腕のパターン変数は借用の変数になる（OWN「借用の `match`」と同じ）。`Some(x)` の `x` は `Option(&A)` の中の `&A`。
- `match f(&v) { … }`：対象の view は `match` の間だけ生き、`v` の凍結も `match` の終わりで解ける。

### extern の view 型

```nib
view struct Iter(A) {}               // 借用を抱える不透明な型
extern {
  fn vec_iter<A: linear>(&v: Vec(A)) -> Iter(A)
  fn iter_next<A: linear>(&mut it: Iter(A)) -> Option(&A)
}
```

- `view struct X(…) {}` は中身のない宣言だけ（フィールドは書けない）。種は持たない（view は所有されないので）。
- Rust への対応は 「extern の生成と橋渡しクレート」：`Iter(A)` は `std::slice::Iter<'a, A>` のように、lifetime を一つ持つ Rust の型。`Tauto.eure` の `rust.types` に Rust の型を書く（「`Tauto.eure` の `rust` 節」）。

### 実行時

`eval.rs` では view 型の値は普通の値（借用は値そのものか持ち主への参照、OWN「実行時の意味論」）。`Iter(A)` のような extern の view は eval では呼べない（`run_error = "extern is not runnable"`）。std の `vec_iter` / `iter_next` を組み込みとして持つかは実装の任意。

### std の関数

- std は、無いことを `Option` で返す `vec_get<A: linear>(&v: Vec(A), i: u64) -> Option(&A)` と `hashmap_get<K: linear, V: linear>(&m: HashMap(K, V), &k: K) -> Option(&V) where DecEq(K), Hash(K)` を持つ。効果で知らせる `vec_index(…) -> &A ! {out_of_bounds}` と `hashmap_index(…) -> &V ! {missing}` も持つ（OWN「affine の std（Rust と同じコストモデル）」）。`hashmap_get` の名前は `Option(&V)` を返す方のもので、`vec_get` と揃う。`Option<&T>` を効果にしない（「`Result`、`fail` / `raise` / `catch`、`Slice`」の「方針」）のは std も同じ。

---

## `-> &mut A` と `let &mut x`

### 規則

`-> &mut A` は次の規則で書ける（OWN「結果」の「`-> &mut A` は ない」より、この節が優先する）。

- `fn f(…) -> &mut A`：関数に少なくとも一つの `&mut` の引数が要る（`"error: -> &mut A needs a &mut parameter"`）。結果は **すべての借用の引数から派生する**（`&` の引数も含む）。
- 本体で返せるのは、`&mut` の引数そのもの、その field path、または `-> &mut A` の関数を `&mut` の引数に適用した結果だけ。
- 受け取り：`let &mut x = f(&mut v, &w)`。`x` は `&mut` の借用の変数（OWN「借用の変数」：`x := e`、`&mut x`、`&mut x.f`、`&x` ができる）。
- 凍結：`x` の生きている間（ブロックの終わりまで）、`v` は **一切** 使えない（`&v` もできない）。`&w` で渡した `w` は、`&` だけできる。
- `&mut A` は `A` が複製可でも `A` と同じにならない（書き込みが持ち主に届かなければならないので）。
- view：`Option(&mut A)` も view 型（「何が view 型か」）。`match hashmap_get_mut(&mut m, &k) { Some(x) => { x := x + 1 }, None => () }`。
- 閉包は `&mut` を返せない（`&` と同じ）。

### std にあるもの

```nib
fn vec_get_mut<A: linear>(&mut v: Vec(A), i: u64) -> Option(&mut A)
fn vec_last_mut<A: linear>(&mut v: Vec(A)) -> Option(&mut A)
fn hashmap_get_mut<K: linear, V: linear>(&mut m: HashMap(K, V), &k: K) -> Option(&mut V) where DecEq(K), Hash(K)
```

### 実行時

`eval.rs`：`&mut` の結果は持ち主の要素への参照（OWN「実行時の意味論」の affine の借用と同じ表現）。`x := e` が持ち主の要素を書き換えること。

## 中立な `extern` と `Tauto.eure` の `rust` 節

### 方針

- 言語（`.taut` / `.nib`）に Rust のことを書かない。extern の宣言は **`extern { … }`** で、`"rust"` のようなバックエンドの名前を書かない。`extern` は「中身を外から与える関数」の宣言だけ。
- 各 extern がどのバックエンドの何に当たるかは、tote の設定 `Tauto.eure` の `rust` 節（と、それが指す `.eure` ファイル）が決める。別のバックエンドは `wasm` のような別の節で対応を持てばよく、`.taut` はバックエンドに依存しない。
- カーネルから見れば extern は中身のない公理で、`tauto check` の信頼の一覧に出る（OWN「`extern`」）。

### 構文

```nib
affine struct File {}
affine struct IoError {}

extern {
  fn file_open(&path: Text) -> Result(File, IoError)
  fn file_read_to_buf(&mut f: File, &mut buf: Buf) -> Result(u64, IoError)
  fn io_error_message(&e: IoError) -> Text
}
```

- `tauto.par`：`ExternDecl: KwExtern OpenBrace { ExternItem } RBrace`。`ExternItem` は本体のない `fn` の署名。`KwExtern` の後に文字列は書けない（`extern "rust"` は構文エラーにして、エラーの文で `extern { … }` を案内する：`"error: write extern { … }; the rust path goes in Tauto.eure"`）。
- extern の行は **空でなければならない**（「extern と効果」）。失敗は `Result(T, E)` の値で返す。
- 名前空間（「名前空間」）の中に書ける：`module File { extern { fn open(&path: Text) -> Result(File, IoError) } }`。

### `Tauto.eure` の `rust` 節

`Tauto.eure` は `eure-document` と `eure-reader` で読む。

```eure
package {
  name = "files-demo"
  version = "0.1.0"
  sources = ["src"]
}

rust {
  # 橋渡しクレート（任意）。tote からの相対パス。クレートの名前は files-demo-bridge でなければならない（「橋渡しクレート（bridge）」）。
  bridge = "bridge"
  # tauto bind が生成した対応表（任意、いくつでも）。
  bindings = ["bind/regex.eure"]

  # extern の型 → Rust の型。lifetime を持つ view の型は '_ で書く。
  types {
    File = "std::fs::File"
    IoError = "std::io::Error"
    Iter = "std::slice::Iter<'_, A>"
  }

  # extern の関数 → Rust のパス。名前空間の中の関数は修飾名で書く（"File.open" = …）。
  extern {
    file_open = "std::fs::File::open"
    file_read_to_buf = "files_demo_bridge::read_to_buf"      # 橋渡しクレートの関数
    io_error_message = "files_demo_bridge::io_error_message"
  }

  # Cargo の依存。Cargo.toml の [dependencies] の書き方をそのまま写す。
  dependencies {
    regex = "1.11.1"
  }
}
```

eure の正確な書き方（ブロック、文字列のキー）は `eure-document` の文法に従う。持つ情報が同じなら、eure としての書き方は文法に合わせて変えてよい。

### 解決の規則

extern の関数 `f`（修飾名なら `M.f`）の Rust のパスは次の順で探す。

1. `Tauto.eure` の `rust.extern` の `f`。
2. `rust.bindings` の各ファイルの `extern` の `f`（ファイルの順に、最初に見つかったもの）。二つ以上のファイルにあればエラー `"error: file_open is bound twice: bind/a.eure and bind/b.eure"`。
3. 橋渡しクレートの同じ名前の関数：`rust.bridge` があれば `<bridge>::f`（`<bridge>` は橋渡しクレートの Rust での名前、例 `files_demo_bridge`）。修飾名 `M.f` なら `<bridge>::m::f`（モジュールの名前を snake_case にする。`File.open` → `files_demo_bridge::file::open`）。
4. どれもなければ、`tauto build` がエラー：`"error: file_open has no rust binding (add it to rust.extern in Tauto.eure)"`。`tauto check` はこのエラーを出さない（Rust のことを知らない）。

型も同じ順（`rust.types`、bindings の `types`、`<bridge>::Type`）。

### 信頼の一覧

`tauto check` は信頼の一覧（公理と extern）に、extern ごとに **宣言の位置（`.taut` のファイルと行）** を出す。`tauto build --backend rust` はさらに **対応の位置（`.eure` のファイルと行）** と Rust のパスを並べて出す（「extern の生成と橋渡しクレート」の「信頼の一覧」）。

## 名前空間

### 前提

- 名前空間は **単純なモジュールと修飾名** だけ。型ごとの特別な仕組み（メソッド、`impl`、`self`）は入れない。
- `tauto bind` は Rust の型ごとに同じ名前のモジュールを作る：Rust の `File::open` は tauto の `File.open`。

### 名前空間の規則

```nib
affine struct File {}

module File {
  extern {
    fn open(&path: Text) -> Result(File, IoError)
  }
  fn open_or_default(&path: Text) -> … { … open(&path) … }   // 中では修飾なしで書ける
}

fn main() -> () {
  let r = File.open(&"a.txt")
  …
}
```

1. **宣言**：`module M { 宣言… }`。トップレベルと、他の `module` の中に書ける（入れ子：`A.B.f`）。一つの tote で同じ名前の `module` は一度だけ（`"error: module File is declared twice"`）。
2. **型とモジュールは別の名前の空間**。`affine struct File {}` と `module File` は並んでよい。型の位置の `File` は型、項の位置の `File.open` はモジュールの関数。
3. **修飾名**：項の位置で `M.f`、`M.N.f`。型の位置で `M.T`。
4. **解決**：修飾のない名前は、内側のモジュール → 外側のモジュール → トップレベル の順に探す。`import "x.taut"`（ファイルの宣言を取り込む）はそのまま。`use` / `open` のような「修飾を省く」宣言は **入れない**（短さより明示性）。
5. **フィールドとの区別**：`x.f` の `x` が局所変数ならフィールド（と `info.more(…)` のような、フィールドの関数の呼び出し）、そうでなく `x` がモジュールの名前なら修飾名。局所変数にモジュールと同じ名前を付けるのはエラー（`"error: file is the name of a module"`。名前の大文字・小文字は区別するので、`file` と `File` はぶつからない）。
6. **カーネル**：名前の解決は `surface.rs` の段で済ませ、カーネルには **点を含む平らな名前**（`File.open`）を渡す。カーネルは名前を見ないので、名前空間はカーネルに現れない。点はモジュールの区切りとクラスの member の区切りに使われるので、モジュール名はクラス名・効果名と衝突してはならず、`@` を含められない（衝突は `error: module X collides with class X`）。
7. **公開**：すべて公開（`pub` は入れない）。
8. `fmt.rs`：`module M {` の中を一段字下げする。

## 入れないもの

| 入れないもの | 代わり | 理由 |
|---|---|---|
| `?` 演算子 | `raise` / `catch`（「`Result`、`fail` / `raise` / `catch`、`Slice`」） | 一つのことに書き方は一つ。どこで効果に変えたかが呼び出しとして見える |
| `direct` の腕の `k` を省く糖衣（`log(t) => e`） | `log(t), k => k(e)` | 再開が腕の上で見える方がよい |
| メソッド呼び出し（`f.read(…)`） | `File.read(&mut f, …)` | 型ごとの名前空間の仕組みを持たない（「名前空間」） |
| 利用者の定義する view の struct | extern の `view struct` だけ | 借用を抱える構造体の規則は未設計 |
| `use` / `open` | 修飾名 | 明示性 |
| extern の `copy` / `shared` の型 | `affine struct` だけ | 未決定（「未決定の問い」の「extern の型を `copy` / `shared` と宣言できるようにするか」。方向は許す）。決めるまでは入れない |
| extern の副作用を行に出す（`! {io}`） | 信頼の一覧に出すだけ | 「未決定の問い」の「extern の副作用を行に出すか」 |
| `direct ! {Div}`（腕の中の `while`） | 腕では `Div` を行えない | 「未決定の問い」の「`direct ! {Div}`」 |

型クラス・trait は [`classes.md`](classes.md) にある。Rust への写像は同「Rust バックエンド」。

---

# 第 II 部　Rust バックエンド

## 全体像とクレート

### 流れ

```text
.taut / .nib
  │ tauto-parol, surface.rs        構文
  │ types.rs, rows.rs              型と行
  │ lin.rs                         種・使用・借用・CFL（OWN）
  ▼
TypeReport + LinReport             （検査の結果。バックエンドはここまでをそのまま使う）
  │ tauto_nir::lower               下降：A 正規形、var の表現、clone の位置、層、単相化
  ▼
NIR（tauto_nir::Package）
  │ tauto_rustgen::emit            Rust のソース（quote のトークン列を rustfmt で整形）
  ▼
target/tauto/<package>/            生成した Cargo のワークスペース
  │ cargo build --offline --locked
  ▼
実行ファイル / ライブラリ
```

カーネル（`check.rs`、`check/core.rs`）は通らない。証明・型・命題は NIR に入らない（「消去」）。

## NIR

### 方針

- NIR は **A 正規形**：関数の引数・コンストラクタのフィールド・演算の項は、局所変数かリテラルか、借用の place。入れ子の式は一時変数の `let` に切り出す。
- NIR は `lin.rs` の結果を **写すだけ**。どの使用が move か、どこが借用か、どこで凍結が解けるかは `LinReport` から取る。NIR を作る途中で所有権を判断し直さない。
- NIR の各ノードは元の位置（`Span`）を持つ。生成コードのコメントと実行時エラーの位置に使う。

### 名前

Rust の名前は衝突しないように機械的に作る：局所変数 `{name}_{id}`、関数の実体 `{name}__{tier}{b?}`（例：`map__o`、`count__ob`。`b` は budget の下）、修飾名は `__` でつなぐ（`File.open` → `File__open__s`）、型はそのまま（tauto の型名は大文字始まりで Rust と同じ規約）、Rust の予約語に当たる名前は `r#` を付ける。

### 消去

`theorem`、`axiom`、`inductive`、`def` はコードを生成しない。実行される `fn` の中の型の位置の出現（OWN「型・命題・証明との関係（tauto）」）も消す。`@a T` のタグは消して `T` にする。証明の引数を持つ `fn` は、その引数を消した署名にする（OWN「型・命題・証明との関係（tauto）」で「使用に数えない」とされた位置）。

---

## 層の決定と単相化

### 操作の層

| 操作 | 層 |
|---|---|
| `direct`（`show` を含む） | S |
| `resume 0`（`fail(E)` を含む） | A |
| `resume <=1`、`resume 1`、`Exceeded(T)` | O |
| `resume ω` | M |
| `Div` | budget の外なら S（ホストの中断の検査だけ）、budget の下なら O（「`budget`、`Div`、`Interrupted`」） |
| `Match(A)` | 層に数えない（網羅的でない `match` は Rust の `match` の最後の腕で実行時エラーにする、「`match`」） |

### 関数の実体の層

`tier(inst) = max(行の具体的な操作の層, 行変数に代入された層, forced)`。行が空なら S。

### 単相化の鍵

- **型変数は単相化しない**：Rust のジェネリクスにし、rustc に任せる。
- **行変数は層で単相化する**：`fn map<A, B, e>(…)` を `e` に S の行で呼べば `map__s`、O の行で呼べば `map__o`。鍵は `InstKey`（層と budget の下かどうかと、行変数・型変数の実体化の組）。同じ鍵の実体は一つだけ作る。
- 呼び出しの鍵の求め方：呼ばれる関数の行変数ごとに、その呼び出しで代入された行（型検査が単一化で決めたもの）の層を取る。代入された行がさらに呼ぶ側の行変数を含むなら、呼ぶ側の実体の鍵の層を使う。

### 層を上げる場合

**どのコードも、本来の層より上の層の形で生成できる**（S のコードは A / O / M の関数の中にそのまま書ける）。次の二つの場合に、呼ばれる側の実体を上の層で作る。

1. **M の中から O の関数を呼ぶ**：M の実体のコードから、本来の層が O の関数を呼ぶときは、その関数の M の実体（`forced = Some(M)`）を呼ぶ。O の実体（Future）を M の状態機械の中に持たないため（「M の外とのつなぎ」）。
2. **関数の型の部分型**：閉包リテラルや関数の値を、それより大きい行の関数の型の位置に渡す（`() -> i64` を `() -> i64 ! {ask}` の引数に渡す）ときは、閉包を **受ける側の型の層** で生成する。関数の値の Rust の型は、tauto の関数の型の行の層で決まる（「関数の型（呼び出し規約）」）ので。

A の関数は O / M の中からそのまま呼ぶ（`Err` を受けて、その場で操作を行い直す。「O / M の中から A の関数を呼ぶ」）。

### 関数の値の層

関数の **型** `(…) -> R ! ρ` の層は、`ρ` の層（行変数を含めば、その実体の鍵で決まる）。関数の値（閉包、関数名を値として使ったもの）はその型の層の呼び出し規約（「関数の型（呼び出し規約）」）を持つ。

---

## 型の写像

### 表

| tauto | 種 | Rust | 備考 |
|---|---|---|---|
| `i32` `i64` `u8` `u32` `u64` | copy | 同名 | 演算は `checked_*`。溢れ・0 での除算は実行時エラー（「`show`、実行時エラー、位置」） |
| `Bool` | copy | `bool` | |
| `Float` | copy | `f64` | |
| `()` | copy | `()` | |
| `Never` | copy | `tauto_rt::Never`（空の enum） | `Never` から任意の型へは `match x {}` |
| `Decimal` | 未決定 | — | **生成しない**。使うプログラムは `tauto build` がエラー `"error: Decimal is not supported by the rust backend"`（OWN「未決定」） |
| `Text` | shared | `tauto_rt::Text`（`Rc<str>` の型の別名） | `&Text` は `&str` に deref |
| `Buf` | affine | `String` | |
| `Vec(A)` | affine | `Vec<A>` | |
| `HashMap(K, V)` | affine | `std::collections::HashMap<K, V>` | 鍵は `DecEq(K)`・`Hash(K)` を満たす型（[`classes.md`](classes.md)「std の鍵の制約」） |
| `Option(A)` | 構造 | `Option<A>` | |
| `Result(T, E)` | 構造 | `Result<T, E>` | |
| `Pair(A, B)` | 構造 | `(A, B)` | |
| `Slice(A)`（借用の後ろだけ） | — | `[A]`（`&[A]` / `&mut [A]`） | |
| tauto の `struct` | 構造 | 同名の `struct`（フィールドは `pub`） | 「struct と enum」 |
| tauto の `enum` | 構造 | 同名の `enum` | 「struct と enum」 |
| `A \| B` | join | 生成する enum | 「union」 |
| `@a T` | kind(T) | `T` | タグは消す |
| 関数の型 | 種による | 「関数の型（呼び出し規約）」 | |
| `Info(T)` | affine | `tauto_rt::Info<'a, T>` | 「`budget`、`Div`、`Interrupted`」 |
| extern の型 | affine | `Tauto.eure` の `rust.types` の Rust の型 | 「extern の生成と橋渡しクレート」 |
| extern の `view struct` | view | lifetime を一つ持つ Rust の型 | 「extern の生成と橋渡しクレート」 |
| `&T` / `&mut T`（引数、`let &x`） | — | `&'a T` / `&'a mut T` | 「借用、lifetime、型変数」 |
| 型変数 `<A>` / `<A: shared>` / `<A: linear>` | 境界 | `A: 'static + Show` / `A: 'static + Show + Clone` / `A: 'static + Show` | 「借用、lifetime、型変数」 |

### struct と enum

- copy の型：`#[derive(Clone, Copy)]`。shared の型：`#[derive(Clone)]`。affine で clone 可能（OWN「Drop と clone」）な型：`#[derive(Clone)]`。それ以外の affine と linear：derive しない。
- **再帰する位置**（enum のフィールドが自分自身、または相互再帰する型を含む）は `Rc<…>` にする。再帰する enum は OWN では shared 以上なので `Rc` で正しい。affine な再帰型（`affine enum Expr { … Buf … }`）は `Box<…>` にする（`Rc` は中身を move で取り出せないので）。
- `match` で中身を取り出すとき、`Rc<T>` の位置は `(*rc).clone()` で取り出す（shared なので複製してよい）。`Box<T>` の位置は `*boxed` で move する。
- linear の型には debug ビルドでだけ drop bomb を付ける（「drop bomb（linear）」）。

### union

- 型検査が `A | B` を正規化した形（結合・可換・冪等、OWN の `union` 関数の結果）ごとに、enum を一つ生成する。名前は成員の型の名前を決まった順（`types.rs` の正規形の順）に並べたもの：`Union__i64__Text`。成員の名前に使えない文字は `_` にする。
- 変種は `V0(i64)`、`V1(Text)`、…（正規形の順）。
- **注入**（`A <: A | B`）：型検査が部分型を使った位置で `Union__…::V0(x)` を挟む。その位置は、`types.rs` が `TypeReport` に「この式は型 X で、期待された型 U に部分型で収めた」として記録する。
- **出口**（すべての成員が `C` の部分型なら `A | B <: C`）：`match u { V0(x) => <x を C へ>, V1(y) => <y を C へ> }` を挟む。
- 種は成員の join。derive は 「struct と enum」と同じ規則。
- `show` の表示は中身の表示（union は表示に現れない）。eval がそう表示することを確かめる。違えば eval に合わせる。

### drop bomb（linear）

```rust
// tauto-rt
pub struct Bomb { armed: bool, what: &'static str }
impl Bomb { pub fn new(what: &'static str) -> Bomb; pub fn defuse(mut self) { self.armed = false; } }
impl Drop for Bomb { fn drop(&mut self) { if cfg!(debug_assertions) && self.armed && !std::thread::panicking() { panic!("tauto: a linear value was dropped: {}", self.what) } } }
```

- linear の struct / enum に `bomb: tauto_rt::Bomb` のフィールドを足す（enum なら各変種に）。作るときに `Bomb::new("Handshake")`。
- linear の値を **消費する** 位置（`match` で分解する、`proj` で取り出す、OWN「Lean での証明」の T3 の位置）で `defuse()` する。
- `std::thread::panicking()` のときは鳴らさない（実行時エラーで巻き戻る途中なら捨ててよい。OWN「制御フロー線形性（CFL）の規則」の通り linear は `resume 0` を跨がないので、正しいプログラムでこれは起こらない）。

### 関数の型（呼び出し規約）

`Ev` は 「S 層と direct の操作（証拠 `Ev`）」。`Fut<'a, T>` は `Pin<Box<dyn Future<Output = T> + 'a>>`（`tauto_rt::Fut`）。

| 層 | shared な関数の値 | affine な関数の値 | linear | 借用閉包（`&f` の引数） |
|---|---|---|---|---|
| S | `Rc<dyn Fn(&Ev<'_>, A…) -> R>` | `Box<dyn FnOnce(&Ev<'_>, A…) -> R>` | affine と同じ + `Bomb` を捕まえる | `&mut dyn FnMut(&Ev<'_>, A…) -> R` |
| A | 同上で `-> Result<R, Abort>` | 同上 | 同上 | 同上で `-> Result<R, Abort>` |
| O | `Rc<dyn tauto_rt::OFn<(A…), R>>` | `Box<dyn tauto_rt::OFnOnce<(A…), R>>` | 同上 + `Bomb` | `&mut dyn tauto_rt::OFnMut<(A…), R>` |
| M | `Rc<dyn tauto_rt::MFn<(A…), R>>` | `Box<dyn tauto_rt::MFnOnce<(A…), R>>` | 同上 + `Bomb` | `&mut dyn tauto_rt::MFnMut<(A…), R>` |

- `Ev` を **呼ぶときに** 渡す（定義したときに捕まえない）。tauto の効果は呼ばれた時点のハンドラが処理するので（[`semantics.md`](semantics.md)）、閉包が作られたときのハンドラを捕まえると意味が変わる。
- O の閉包を Rust の閉包にしないのは、借用閉包（`FnMut`）が返す Future が閉包の捕まえた `&mut` を借りられないため（Rust の `FnMut` は呼び出しの間しか自分を貸さない）。`tauto_rt::OFnMut::call(&'s mut self, …) -> Fut<'s, R>` は `self` を Future の間ずっと借りるので、捕まえた `&mut` を `.await` を跨いで使える。O の閉包リテラルは、捕まえた変数をフィールドに持つ struct と、その trait の実装として生成する（「O 層の閉包」）。
- 借用閉包の `&mut dyn FnMut` の引数に閉包リテラルを渡すときは、呼び出しの式の中で `&mut |ev, x| …` と書く（その文の間だけ生きる一時値、OWN「閉包」）。

### 借用、lifetime、型変数

- 引数 `&x: A` は `x: &'a A`、`&mut x: A` は `x: &'a mut A`。
- **関数の lifetime は一つ `'a` だけ**：すべての借用の引数、view の結果、`-> &A` / `-> &mut A` の結果、O / M の層の `Ev<'a>` と戻りの `Fut<'a, R>` を同じ `'a` にする。OWN「結果」の「結果はすべての借用の引数から派生する」をそのまま Rust の署名にしたもの。
- 借用の引数のない S / A の関数は lifetime を書かない。
- **型変数にはいつも `'static` を付ける**。「何が view 型か」で view は型変数にならないと決めたので、tauto の値の型はいつも借用を含まない（閉包の型は 「関数の型（呼び出し規約）」の `Rc<dyn …>` で、`'static` でない捕獲を持たない。借用を捕まえた閉包は借用閉包で、型変数にならない）。`'static` があると効果の引数を `Box<dyn Any>` で運べる（「O 層（`resume <=1` と `resume 1`）」）。
- **型変数にはいつも `Show` を付ける**（`show` の引数にできるように。「`show`、実行時エラー、位置」）。`Show` は生成したクレートの中で定義する trait。
- `<A: shared>` は `Clone` を足す。copy の境界は tauto にないので `Copy` は付けない（copy の値も `Clone` で複製する）。

---

## 式と文の生成

ここでは S 層の形で書く。A / O / M の違いは 「A 層（`resume 0`）」〜「M 層（`resume ω`）」。

### 関数

```nib
fn add(p: P, &q: P) -> i64 { p.x + q.y }
```

```rust
// src/main.taut:3:1 add
pub fn add__s(ev: &Ev<'_>, p_0: P, q_1: &P) -> i64 {
    tauto_rt::int::add_i64(p_0.x, q_1.y, L3_33)
}
```

- **すべての** 生成した tauto の関数は、最初の引数に `ev: &Ev<'_>` を取る（使わなくても取る。`#[allow(unused_variables)]` をクレートの先頭に付ける）。規約を一つにすると、呼び出しの生成が単純になり、間違いが減る。
- `L3_33` は位置の定数（「位置」）。
- トップレベルの文は `pub fn top__<tier>(ev: &Ev<'_>) -> …` という一つの関数にする。

### 使用

| NIR | Rust |
|---|---|
| `Use::Move(x)` | `x` |
| `Use::Copy(x)` | `x` |
| `Use::Clone(x)` | `x.clone()` |
| `Use::Deref(x)`（x: `&A`、`A` は copy） | `*x` |
| `Use::Deref(x)`（x: `&A`、`A` は shared） | `(*x).clone()` |
| `Field { how: Copy }` | `p.f` |
| `Field { how: Clone }` | `p.f.clone()` |
| `Arg::Ref(p)` | `&p`（`p` がすでに `&A` の借用の変数なら `p` のまま） |
| `Arg::Mut(p)` | `&mut p`（`p` がすでに `&mut A` の借用の変数なら `&mut *p`） |

- shared の値の **値としての使用は `.clone()`**。ただし **最後の使用は move** にする（`crates/tauto-nir/src/last_use.rs`）：関数の式を Rust の評価順に後ろ向きの生存解析で辿り、後で誰も読まない局所変数の clone を move に変える。追えないもの（閉包、`handle`、`budget`）は不透明で、中で触れる名前はすべて生きているものとし、中は変えない。これがないと、ループや再帰で辿るリストが一歩ごとに複製される。
- これと 「struct と enum」の `Rc` の取り出し、「`var` の表現」のセルの読み出し、「`match`」の配列要素の所有束縛が、clone を書いてよい **すべての** 場所。
- 引数の借用（`crates/tauto-nir/src/borrow.rs`：読むだけの再帰的な値を参照で受ける）と最後の使用の move は、環境変数で切れる。`TAUTO_KEEP_OWNED=1` ではすべての引数が所有のまま、`TAUTO_KEEP_CLONES=1` では clone がすべて残る。

### 一時値と Drop の順

OWN「Drop の時点と順序」：束縛は宣言の逆順に、ブロックの終わりで捨てる。式の途中の一時値は **その文の終わりで** 捨てる。

- tauto のブロックを Rust のブロックに写す。束縛の順を変えない（Rust も宣言の逆順に捨てるので一致する）。
- A 正規形で切り出した一時変数は、元の文ごとに Rust のブロックで囲む：`f(g())` の `g()` が affine で `f` が借用で受けるなら `{ let t_5 = g(); f(&t_5) }`。`let x = f(&g())` なら `let x = { let t_5 = g(); f(&t_5) };`。一時変数を関数の先頭やブロックの外に出さない（Drop の時点が変わる）。
- `x := v`（`var`）は Rust の代入 `x = v;`。Rust は古い値をその場で捨てる。OWN「`let` と `var`」と同じ。
- move された束縛は Rust も捨てない。`lin.rs` が move と言った使用を `Use::Move` にすれば、Rust の Drop は OWN と一致する。
- struct のフィールドは Rust の順（宣言の順）に捨てられる。OWN はフィールドの順を決めていない。動的所有権検査（「検証の方針」の drop bomb と動的所有権検査の照合）でフィールドの順が食い違えば、eval の方を Rust の順に合わせる（tauto の型だけなら観測できないので）。

### `if`、ループ、`return`

- `if c { a } else { b }` は Rust の `if`。
- `while c { body }` は Rust の `while`。`Tick`（「`budget`、`Div`、`Interrupted`」）をループの本体の **先頭** に入れる。
- `loop`、`break`、`continue`、`return` は Rust の同じもの。

### コンストラクタとフィールド

- `P { x: 1, y: 2 }` → `P { x: 1, y: 2 }`。再帰する位置は `Rc::new(…)` / `Box::new(…)` で包む。linear なら `bomb: Bomb::new("P")` を足す。
- enum のコンストラクタ `cons(1, xs)` → `List::cons(1, Rc::new(xs))`。Rust の enum の変種の名前は tauto のコンストラクタの名前そのもの（小文字でもよい。`#![allow(non_camel_case_types)]` を付ける）。

### `match`

- tauto の `match` を Rust の `match` にする。入れ子のパターンは `check/nested.rs` / `check/matching.rs` の展開に頼らず、Rust の入れ子のパターンにそのまま写す（Rust が入れ子のパターンを持つので）。ただし `Rc` / `Box` の位置は Rust のパターンで中に入れないので、その位置では一度変数に束縛し、内側の `match` に分ける。
- ガード `p if g => b` は Rust のガード。
- 網羅的でない `match`（`exhaustive: false`）には最後に `_ => tauto_rt::no_arm(L…)` を足す。文は eval の「どの腕も合わない」ときの文（`messages.rs`）。
- 借用の `match`（OWN「借用の `match`」）は `match &v { … }`（Rust の default binding modes で、パターン変数が `&` になる）。
- 所有の `match` は値を消費する（Rust と同じ）。linear の値なら、腕の始めで `bomb.defuse()` する（パターンで `bomb` を束縛して）。
- 直接生成する `match` の対象が純粋な `array_get` で、腕が所有の `Some` / `None` / `_` のパターンだけでガードを書いていなければ、配列要素の形を参照で調べる。配列と添字は元の順で一度ずつ評価し、配列の所有値を保持してから調べる。配列が単独所有なら通常の `array_get` と所有の `match` を実行し、再帰的なフィールドを move できる性質を保つ。ほかにも所有者がいる配列では、選ばれたパターンの束縛だけを clone して所有値にし、配列の保持を解いてから腕の本体を実行する。無視するフィールドは clone しない。束縛の型と公開 API は所有のままで、`array_get` 自体の `Option(A)` を返す契約は変わらない。分岐した腕の複製が増殖しないよう、腕の本体に別の `array_get` の `match` や `handle` を含む外側の `match` は通常の生成に従う。入れ子のパターン自体は参照で調べられる。`Option` 全体を束縛する腕、ガード、保存した取得結果、継続に分割する `match` も通常の生成に従う。

### 閉包

- S / A 層の閉包リテラルは Rust の閉包：`Rc::new(move |ev: &Ev<'_>, x_3: i64| -> i64 { … })`。捕まえ方は 「`var` の表現」の `var` の表現と、`lin.rs` の捕獲の判断（move か借用か）に従う。
- 借用閉包は `&mut |ev: &Ev<'_>, x_3: i64| -> i64 { … }` を `&f` の引数の位置にその場で書く。名前の付いた借用閉包（`let g = (s) => write_line(&mut f, s)` を後で `&g` で渡す）は `let mut g_4 = |ev: &Ev<'_>, s_5: Text| { … };` として、渡すときに `&mut g_4`。
- affine な閉包は `Box::new(move |…| …)`。
- O / M 層の閉包は 「O 層の閉包」 / 「M 層（`resume ω`）」。

### 演算

`tauto_rt::int` に幅ごとの関数を置く：`add_i32(a, b, at)`、`sub_…`、`mul_…`、`neg_…`、`div_…`、`rem_…`。中身は `a.checked_add(b).unwrap_or_else(|| tauto_rt::error(messages::TOO_LARGE, at))`。比較と `==` は Rust の演算子（`Text` は `*a == *b`）。

---

## `var` の表現

`var` は捕まえ方と、`ω` の効果を跨ぐかで表現を変える。NIR を作るときに束縛ごとに一つ決める（`VarRepr`）。

| 条件（上から順に、最初に当たったもの） | 表現 | 読み | 書き | 借用 `&x` |
|---|---|---|---|---|
| 1. 脱出する閉包（借用閉包でない閉包）に捕まる、または M 層のコードで `ω` の中断点を跨いで生きている | copy なら `Rc<Cell<T>>`、shared なら `Rc<RefCell<T>>` | `x.get()` / `x.borrow().clone()` | `x.set(v)` / `*x.borrow_mut() = v` | 中身を一時変数に複製して、その一時変数を借用する（`&A ≡ A` なので意味は同じ） |
| 2. 借用閉包か direct の腕にだけ捕まる | `let mut x` | `x` | `x = v` | `&x`（閉包は `&mut x` を捕まえる） |
| 3. それ以外 | `let mut x` | `x` | `x = v` | `&x` |

- 1 の中身はいつも複製可（OWN「閉包」：affine な `var` を捕まえる閉包は借用閉包。OWN「制御フロー線形性（CFL）の規則」：affine な `var` は `ω` を跨げない）。もし 1 に affine の中身が来たら、それは `lin.rs` の誤りなので、生成を止めて「コンパイラの誤り」のエラーを出す。
- 1 の `RefCell` は、読み書きの一瞬だけ借りて、借りたまま他のコードを呼ばない。だから実行時の借用の検査は失敗しない。失敗したら生成器の誤り。
- `ω` の継続を複製したとき、1 のセルは **共有** される（`Rc` の複製）。これは eval の「継続の複製は環境を複製し、セルは複製しない」と同じ。
- O 層の `async` の中の `var`（3）は Future の中の局所変数になる。継続は一度しか再開しないので共有の問題はない。

---

## S 層と direct の操作（証拠 `Ev`）

### `Ev` の形

`Ev` は「その時点で張られている direct のハンドラ」の連鎖。内側のハンドラが先頭。

```rust
// tauto-rt/src/ev.rs
pub type OpId = u32;
pub type Payload = Box<dyn std::any::Any>;

// trait に lifetime の引数を持たせない（持たせると Ev<'a> が 'a について不変になり、短い Ev に渡せなくなる）。
pub trait DirectHandler {
    /// op を処理できれば Ok(答え)。腕のパターンが合わなければ Err(args) で返す（外へ探しに行く）。
    /// outer は自分より外の連鎖。腕の中の perform はこれを使う。
    fn handle(&self, outer: &Ev<'_>, op: OpId, args: Payload) -> Result<Payload, Payload>;
    fn handles(&self, op: OpId) -> bool;
}

#[derive(Clone)]
pub struct Ev<'a> { top: Option<Rc<Node<'a>>> }
struct Node<'a> { handler: Rc<dyn DirectHandler + 'a>, outer: Ev<'a> }

impl<'a> Ev<'a> {
    pub fn host(show: impl Fn(&str, String) + 'a) -> Ev<'a>;          // 最上位：show をホストが処理する
    pub fn push<'b>(&self, h: Rc<dyn DirectHandler + 'b>) -> Ev<'b> where 'a: 'b;
    pub fn perform(&self, op: OpId, args: Payload, at: Loc) -> Payload;  // 見つからなければ "nothing handles …"
}
```

- `perform` は先頭から順に `handles(op)` のノードを探し、`handle(&node.outer, op, args)` を呼ぶ。`Err(args)` が返れば（パターンが合わない）、さらに外を探す。
- 腕は **自分より外の連鎖** `outer` で動く。腕の中の `perform` は外のハンドラに届く（「`direct` 操作」の「規則」 D2、デコレータの形）。
- `Ev<'a>` は `'a` について共変にする（`Rc<dyn … + 'a>` は共変）。長い `Ev<'long>` を `&Ev<'short>` として渡せる。
- `Ev` を `push` しても元の `Ev` は変わらない（不変の連鎖）。

### direct のハンドラの生成

```nib
effect log: (t: Text) -> () direct
var out = buf_new()
handle { body } with {
  log(t), k => k(buf_push(&mut out, &t))
}
```

```rust
let mut out_2 = String::new();
{
    struct H7<'b> { out_2: RefCell<&'b mut String> }
    impl<'b> DirectHandler for H7<'b> {
        fn handles(&self, op: OpId) -> bool { op == OP_LOG }
        fn handle(&self, outer: &Ev<'_>, op: OpId, args: Payload) -> Result<Payload, Payload> {
            let ev = outer;                                   // 腕は外の連鎖で動く
            let (t_3,): (Text,) = *args.downcast().expect("tauto: payload type");
            // 腕の本体。末尾形（「`direct` 操作」の「規則」 D1）の各 k(e) を e に置き換えた式を生成し、その値を答えにする。
            let mut out_guard = self.out_2.borrow_mut();          // 腕の実行の間だけ借りる
            let out_2: &mut String = &mut **out_guard;
            let v: () = { tauto_rt::std::buf_push(ev, out_2, &t_3) };
            drop(out_guard);
            Ok(Box::new(v))
        }
    }
    let h = Rc::new(H7 { out_2: RefCell::new(&mut out_2) });
    let ev = &ev.push(h);
    /* body を ev で生成 */
}
// ここで out_2 の借用が終わる（handle の式の終わり。「`direct` 操作」の「規則」 D5 の凍結の終わりと一致）
```

- 腕のパターンが合わない（`log("x"), k => …` に `"y"` が来た）ときは `Err(args)` を返す。
- 腕が捕まえる `&mut` は `RefCell<&'b mut T>` に入れる。同じノードの腕が自分を再び呼ぶことは D2 と「腕は外の連鎖で動く」から起こらないので、`borrow_mut` は失敗しない。失敗したら生成器の誤り。
- 腕が捕まえる `&x` は `&'b T` のまま、複製可な変数は値の複製、`var`（「`var` の表現」の 1）は `Rc` の複製。
- 一つの `handle` に direct の腕と direct でない腕が混ざっていれば、direct の腕だけをこのノードにし、残りは 「A 層（`resume 0`）」〜「M 層（`resume ω`）」の形のハンドラにする。ノードを先に張り、その内側に direct でないハンドラを置く（どちらも同じ `handle` の腕なので、互いの順は意味に影響しない：操作が違うので）。

### `perform` の生成

```rust
let r: () = *ev.perform(OP_LOG, Box::new((t_9,)), L12_5).downcast().expect("tauto: payload type");
```

引数はタプルにして `Box` に入れる。答えも `Box` から取り出す。型が合わなければ生成器の誤り（`expect` のメッセージは `"tauto: payload type"` で統一し、利用者のエラーと区別する）。

### `show` とホスト

- `show` は direct の操作 `OP_SHOW`。最上位の `Ev::host` が処理し、`name = value` の行を出す。値の文字列は生成した `Show` trait（「`show`、実行時エラー、位置」）で作る。
- `show` の引数は `(Text, Box<dyn Show>)` で運ぶ（`show<A>` は型変数を持つので、`Show` の trait object にする）。利用者の `show` の腕（`show(n, v), k => k(perform show(n, v))`）は `v` を `Box<dyn Show>` として持ち回す。

### S 層の関数

普通の Rust の関数。`ev` を受け、direct の操作は `ev.perform`、S の関数の呼び出しは `f__s(ev, …)`。中断も打ち切りもしない。

---

## A 層（`resume 0`）

### 形

```rust
pub struct Abort { pub op: OpId, pub args: Payload, pub at: Loc }
```

- A 層の関数は `-> Result<R, Abort>`。`perform op(v)`（`op` は `resume 0`）は `return Err(Abort { op: OP_FAIL, args: Box::new((v,)), at: L… })`。
- A / S の関数の呼び出しの結果は `?` で伝える（S の関数は `Result` を返さないので `?` を付けない）。
- 伝わる途中の affine な局所変数は Rust がその場で捨てる。OWN「手で確かめる表」（affine は `resume 0` を跨げる、Drop）と一致する。linear は `lin.rs` が跨がせない。

### `handle`（本体が A 層のとき）

```nib
let r = handle { risky() } with {
  fail(e) => recover(e)
  return v => v + 1
}
```

```rust
let r_4 = match (|| -> Result<i64, Abort> { Ok(risky__a(ev)?) })() {
    Ok(v) => v + 1,                                               // return 腕
    Err(a) if a.op == OP_FAIL_TEXT => {
        let (e_5,): (Text,) = *a.args.downcast().expect("tauto: payload type");
        recover__s(ev, e_5)                                       // 腕（外で動く）
    }
    Err(a) => return Err(a),                                      // 自分の操作でなければ外へ
};
```

- 本体は即時に呼ぶ閉包にする（`?` を本体の中に閉じるため）。本体が外の局所変数を借用してよい（その場で呼ぶので）。
- 腕のパターンが合わなければ、`Err(a)` のまま外へ（`a.args` を戻して）。
- `return` 腕がなければ `Ok(v) => v`。
- 包む関数が S 層（`handle` が `resume 0` の効果を全部取り除いた）なら、最後の `Err(a) => return Err(a)` は書けない。そのときは、型検査が「この `handle` の後に `resume 0` の効果は残らない」と保証しているので、`Err(a) => tauto_rt::unhandled(a)`（実行時エラー `nothing handles …`。正しいプログラムでは起こらない）にする。

### O / M の中から A の関数を呼ぶ

```rust
// O 層の中
let v = match f__a(&ev, x) { Ok(v) => v, Err(a) => tauto_rt::o::reraise(a).await };
```

`reraise` は `Abort` を O 層の要求として入れ物に置き、二度と戻らない（`resume 0` の腕は `k` を持たないので答えが来ない。答えが来たら生成器の誤り）。M 層では、フレームが `Step::Perform` を返して戻らない（「M 層（`resume ω`）」）。

---

## O 層（`resume <=1` と `resume 1`）

### 考え方

one-shot の継続は「途中で止まった Future」そのもの。Rust の `async` が状態機械への変換をしてくれるので、tauto は `perform` を「入れ物に要求を置いて `Pending` を返す Future」にし、`handle` を「本体の Future を自分で poll するループ」にする。Waker は使わない（何もしない Waker）。スレッドもランタイムも使わない。

### 実行時（`tauto-rt/src/o.rs`）

```rust
pub type Fut<'a, T> = Pin<Box<dyn Future<Output = T> + 'a>>;

enum Slot {
    Empty,
    Request { op: OpId, args: Payload, at: Loc },   // perform が置いた要求
    Answer(Payload),                                 // ハンドラが置いた答え
    Budget(u32),                                     // budget の燃料切れ（「`budget`、`Div`、`Interrupted`」）
}
thread_local! { static SLOT: RefCell<Slot> = RefCell::new(Slot::Empty); }

/// 一度目の poll で要求を置いて Pending、二度目の poll で答えを取り出して Ready。
pub fn perform(op: OpId, args: Payload, at: Loc) -> impl Future<Output = Payload>;

/// 本体の Future を一度だけ poll する（何もしない Waker で）。
pub fn poll_once<T>(f: Pin<&mut (dyn Future<Output = T> + '_)>) -> Poll<T>;
// Waker は std::task::Waker::noop()（stable、unsafe なし）

pub fn peek() -> Peek;                          // 入れ物に何があるか：Request(op) / Budget(id) / Empty
pub fn take_request() -> (OpId, Payload, Loc);
pub fn put_back(op: OpId, args: Payload, at: Loc);  // パターンが合わなかった要求を戻す
pub fn answer(p: Payload);                      // 答えを置く
/// 一度だけ Pending を返す。入れ物には触らない。外のハンドラに要求を見せるために使う。
pub fn forward() -> impl Future<Output = ()>;
/// 最上位：Future を poll し、Pending のまま要求が残れば "nothing handles <name>" の実行時エラー。
pub fn block_on<T>(f: Fut<'_, T>, names: &dyn Fn(OpId) -> &'static str) -> T;
```

- 入れ物はスレッドに一つ。生成コードは単一スレッドで、同時に二つの要求は起こらない（要求を置いた Future はすぐ `Pending` で上に戻り、どこかのハンドラが取るまで他のコードは動かない）。
- `perform` の Future は、二度目の poll で `Answer` がなければ生成器の誤りとして panic する。

### O 層の関数

```rust
pub fn count__o<'a>(ev: &Ev<'a>, n_0: i64) -> Fut<'a, i64> {
    let ev = ev.clone();
    Box::pin(async move {
        let ev = &ev;
        /* 本体。O の呼び出しは f__o(ev, …).await、perform は 「O 層の `perform`」 */
    })
}
```

- O 層の通常の実体は `Fut<'a, R>` を返す（`async fn` にしない、`impl Future` にしない）。再帰しても大きさが決まり、関数の値の型（「関数の型（呼び出し規約）」）とも揃う。再開しない budget の本体には、別の同期実体を使える（「再開しない budget の同期実体」）。
- 借用の引数は `&'a T` で、Future の中に入る（「借用、lifetime、型変数」の一つの `'a`）。

### `handle`（本体が O 層のとき）

```nib
effect ask: (n: i64) -> i64
let r = handle { perform ask(5) + 1 } with {
  ask(n), k => k(n * 10)
  return v => v + 100
}
```

```rust
fn handle_12<'a>(ev: Ev<'a>, mut body: Fut<'a, i64>) -> Fut<'a, i64> {
    Box::pin(async move {
        loop {
            match tauto_rt::o::poll_once(body.as_mut()) {
                Poll::Ready(v_1) => {
                    let ev = &ev;
                    return v_1 + 100;                                     // return 腕（ハンドラの外で動く）
                }
                Poll::Pending => match tauto_rt::o::peek() {
                    Peek::Request(OP_ASK) => {
                        let (op, args, at) = tauto_rt::o::take_request();
                        let (n_2,): (i64,) = *args.downcast().expect("tauto: payload type");
                        // パターンが合わなければ：tauto_rt::o::put_back(op, args, at); tauto_rt::o::forward().await; continue;
                        let ev2 = ev.clone();
                        let k_3 = move |x: i64| -> Fut<'a, i64> {           // 継続：一度だけ呼べる（FnOnce）
                            Box::pin(async move {
                                tauto_rt::o::answer(Box::new(x));
                                handle_12(ev2, body).await                 // 同じハンドラを張り直す（deep）
                            })
                        };
                        let ev = &ev;
                        return k_3(n_2 * 10).await;                        // 腕（ハンドラの外で動く）
                    }
                    _ => tauto_rt::o::forward().await,                     // 自分のでない要求、budget：外に任せる
                },
            }
        }
    })
}
// 使う側
let r_4 = handle_12(ev.clone(), Box::pin(async move { /* 本体 */ ask_perform + 1 })).await;
```

確かめる点：

- **deep**：`k(x)` は答えを置いてから **同じハンドラのループ** で本体を poll し直す。だから本体の次の `ask` も同じハンドラが受ける。
- **中継**：自分のでない要求のときは、要求を入れ物に残したまま `forward().await` で一度 `Pending` を返す。外のハンドラが要求を取り、答えを置いて、自分の本体（このハンドラの Future を含む）を poll し直す。するとこのループが続き、本体の `perform` の Future が答えを取り出す。
- **捨てる**：腕が `k` を呼ばずに値を返すと、`body` の Future は `k` と一緒に捨てられ、その中の affine な局所変数が Rust の Drop で捨てられる（OWN「腕と `k`」の `<=1`）。
- **一度だけ**：`k` は `FnOnce` なので、二度呼ぶコードは rustc が拒否する（二つ目の検査器）。`resume 1` の `k` は linear なので、`k` に `Bomb` を捕まえさせ、呼んだときに `defuse` する（debug の drop bomb）。
- **借用**：本体が外の局所変数を `&'a` で借りていれば、`k` も `'a` を持ち、`'a` より長く生きられない。だから `k` を `handle` の外に返そうとするコードは rustc が拒否する。継続が借用を持って脱出する穴は OWN「借用と効果」の規則が塞いでいて、`lin.rs` が「`k` holds a borrow of x, so it may only be called in its arm」で先に拒否する。rustc の拒否はその二重の防御になる。
- 腕の中の `perform` は、このハンドラのループの外（`return` で抜けた後の `await`）で起こるので、外のハンドラに届く。
- `ev`（direct の連鎖）は `handle` の外のものを使う。腕は外で動くので。

### O 層の `perform`

```rust
let v_7: i64 = *tauto_rt::o::perform(OP_ASK, Box::new((5i64,)), L4_14).await.downcast().expect("tauto: payload type");
```

direct の操作は O 層の中でも `ev.perform(…)`（同期）。

### O 層の閉包

```rust
// tauto-rt
pub trait OFn<Args, R> { fn call<'s>(&'s self, ev: &Ev<'s>, args: Args) -> Fut<'s, R>; }
pub trait OFnMut<Args, R> { fn call<'s>(&'s mut self, ev: &Ev<'s>, args: Args) -> Fut<'s, R>; }
pub trait OFnOnce<Args, R> { fn call<'s>(self: Box<Self>, ev: &Ev<'s>, args: Args) -> Fut<'s, R> where Self: 's; }
```

閉包リテラルは、捕まえた変数をフィールドに持つ struct と、その trait の実装として生成する。

```rust
struct C21<'a> { out_2: &'a mut String }
impl<'a> OFnMut<(i64,), ()> for C21<'a> {
    fn call<'s>(&'s mut self, ev: &Ev<'s>, (x_3,): (i64,)) -> Fut<'s, ()> {
        let ev = ev.clone();
        Box::pin(async move { let ev = &ev; /* 本体：self.out_2 を使う */ })
    }
}
// 渡す側
vec_each__o(ev, &v_1, &mut C21 { out_2: &mut out_2 }).await;
```

`OFnMut::call` は `self` を Future の間ずっと借りるので、捕まえた `&mut` を `.await` を跨いで使える（Rust の `FnMut` ではできない）。呼ぶ側（`vec_each__o`）は Future を `.await` してから次を呼ぶので、借用が重ならない。

### 層の境目

- S / A の関数を O の中から呼ぶ：S はそのまま、A は 「O / M の中から A の関数を呼ぶ」。
- O の関数を S / A の中から呼ぶことは起こらない（呼ぶ側の行に O の効果が入るので、呼ぶ側も O）。ただし `handle` が O の効果を全部取り除けば、その `handle` を含む関数は S / A になりうる。そのときの `handle` は `tauto_rt::o::block_on` ではなく **その場で回すループ** にする：

```rust
// S 層の関数の中の handle（本体は O）
let r = tauto_rt::o::run_local(handle_12(ev.clone(), Box::pin(async move { … })));
```

`run_local` は `block_on` と同じく poll し、`Pending` で要求が残れば（`handle` が取らなかった操作）、行の検査が「残らない」と保証しているので生成器の誤りとして panic する。direct の操作は `ev` で処理されるので入れ物を通らない。

---

## M 層（`resume ω`）

### 考え方

stable の Rust には複製できる Future がない。そこで M 層のコードは **継続渡し（CPS）** で書く。継続 `Kont` は `Rc<dyn Fn>` で、何度でも呼べる。OWN「制御フロー線形性（CFL）の規則」（CFL）により、`ω` の効果を跨いで生きているのは複製可の値と `&` の借用だけなので、継続は取り込んだ局所変数を `clone` して持てる。

- M 層の関数は、いま有効なハンドラの連鎖 `m` と自分の継続を受け取り、トランポリンに渡す `Step` を返す。深く呼ぶ代わりに `Step` を返すので、長いループでもスタックが伸びない。
- 中断できない式は他の層と同じ形で書き、値を継続に渡す。中断できる式（M の実体の呼び出し、direct でない `perform`、`handle`、`k(…)`）は、その後の計算を閉包にして継続として渡す。
- 閉包は `Fn` で、使う局所変数を先頭で `clone` する。affine な値が混ざれば rustc が拒否する。つまり rustc が `lin.rs` の CFL を確かめ直す。
- ハンドラの連鎖 `M` は永続的な列で、すべての継続が呼ばれるときに渡される。後でもう一度呼ばれる継続（`k(a) + k(b)`）は、捕まえたときのハンドラを、いま `k` を呼んでいる腕のハンドラの上に組み直して使う。これでハンドラが deep になる。

実装は `tauto-rt/src/cps.rs`（実行時）と `tauto-rustgen/src/cps.rs`（生成）。

### 駆動

- `Step` は、`Done`（値を駆動に渡した）、`More`（スタックを巻き戻して続ける）、`Escape`（連鎖のどのハンドラも取らない操作。駆動が答えて継続を呼ぶ）、`Fail`（どのハンドラも拾わない `Abort`）、`NoMatch`（腕のパターンが合わない。引数を戻して外を探す）。
- `perform` は連鎖を内側から探して、操作を取るハンドラの腕を、`handle` 式の継続・操作・引数・`k` で呼ぶ。見つからなければ `Escape`。
- 腕の中の `k(v)` は `Resume::call`。連鎖を組み直して継続を呼ぶ。

### M の外とのつなぎ

- M の関数を呼べるのは M のコードと、`ω` の効果を全部取り除く `handle` だけ（行の量から）。そういう `handle` は、外の関数の層（S / A / O）の中で駆動 `run` を回す。
- 駆動で処理されない操作（`Escape`）：
  - 外が O 層：`tauto_rt::o::perform` で外に出し、答えを継続に渡す（`run_o`）。
  - 外が A 層で操作が `resume 0`：`Err(Abort)` で返す（`run_a`）。
  - それ以外：行の検査が起こらないと保証しているので、生成器の誤りとして panic。
- M の中から S / A の関数を呼ぶのは普通の呼び出し（A なら `Err` を `Abort` にして戻らない）。
- M の中から O の関数を呼ぶときは、その関数の M の実体を呼ぶ（「層を上げる場合」の 1）。

### M の中の `return`

S / A / O 層の関数の中の `handle` が M 層になるとき（「M の外とのつなぎ」の駆動）、その本体や腕に書かれた `return e` は、関数全体から抜ける。M 層のコードは継続で書かれているので、`return` は `fk(v)` ではなく、駆動の **二つ目の継続** `fret` に値を渡し、残りの計算を捨てる。

- `return` を含む駆動だけが `tauto_rt::cps::run_r` / `run_ar` / `run_or` を使う。本体は `|m, fin, fret| …` で、結果は `Flow<T, R>`（`Value(T)`：`handle` の値、`Return(R)`：関数の戻り値）。含まなければ `run` / `run_a` / `run_o`。
- 呼び出し側は `match … { Flow::Value(v) => v, Flow::Return(r) => return r }`（A 層の関数では `return Ok(r)`）。
- M 層の関数そのもの（`fn_def_m`）の中の `return` は、関数の継続 `fk` を呼ぶ。

### M の中の `budget`

M 層のコードの `budget(steps: n) { body }` は、ハンドラの連鎖 `M` の中の **budget のフレーム**（`M::push_budget`）になる。フレームは残りの歩数（`Rc<Cell<u64>>`。連鎖の複製の間で共有される）と、値の型 `T` ごとの `Info` / 答えの読み取りを持つ。本体が終わると `m.pop()` でフレームを外し、値をフレームの `target` に渡す。

- 歩数を数える場所は 「燃料を数える場所」と同じ（`Div` のあるループと呼び出し）だが、M 層では `tauto_rt::cps::tick(m, at, k)`。連鎖のすべての budget から一歩ずつ引き、どれかが 0 なら（一番内側のもの）、そのフレームの **外** に向けて `Exceeded` を perform する。途中の（本体の中の）ハンドラは `Exceeded` を受けないが、`k` の一部として残る。
- 答えは `BudgetAnswer<T>`：`Value(v)` はその budget を `v` で終える（連鎖をフレームの外まで戻して `target` へ）、`More(m)` は歩数を `m` にして `tick` の続きから、`Unbounded` は上限なしで続ける。
- budget の下の `Div` のある関数と `while` は、M 層のコードの中では M の実体（`under_budget` と `m` の両方を持つ実体）になり、`tick` を呼ぶ。
- 位置が観測の対象でないのは 「budget の下」と同じ。Rust 側の期待値は別に持つ。

### 借用の引数

継続は `&'a T` を持てる（外から借りたもの）。M の関数の局所変数を `&` で渡すのは、CFL により複製可の値でしか起こらない。継続は `Fn` なので `&mut` を持ち越さない。これも rustc が確かめる。

---

## `budget`、`Div`、`Interrupted`

### 燃料を数える場所

`Div` を持たない行のコードは停止することが証明済み（`Halt.lean`）なので、**燃料は `Div` の出どころでだけ数える**：

- `while` / `loop` の本体の先頭。
- 行に `Div` を持つ関数（再帰する関数）の呼び出しの直前。
- `info.unbounded()` の後の本体の再開。

この位置に NIR の `Tick` を置く。

### budget の外

`Tick` は `tauto_rt::host_tick(at)`（同期）。スレッドに一つの数を一つ増やし、ホストの上限（`TAUTO_STEP_LIMIT` の環境変数、なければ `tauto_rt::DEFAULT_STEP_LIMIT`、`eval.rs` の `DEFAULT_BUDGET` と同じ値）を超えたら実行時エラー `interrupted: the step limit ran out`（`messages.rs`）。Div を持つ関数でも、budget の外なら S 層のまま。

### budget の下

- `budget(steps: n) { body }` の本体から届く、行に `Div` を持つ関数は、`under_budget = true` の実体（O 層）で生成する。`Div` を持たず、O 層以上の callback を受け取らない関数は budget の下でもそのまま（S / A）。
- budget の内側で作る `Div` のある借用閉包は O 層の callback として渡す。行変数を持つ高階関数も、callback の行を O 層として単相化し、budget の文脈を転送する。`OFnMut` の呼び出しが借りる状態は Future が終わるまで保持し、`more` / `unbounded` は同じ Future を再開する。
- 所有する `Div` 閉包と複数回再開する `Div` 閉包、budget の外で作った `Div` または抽象行の関数値を内側へ渡す経路、発散する名前付き関数を内側で値として渡す経路、発散する可能性のある callback を捕獲する局所関数は未対応として拒否する。外側の同期 ABI の関数値を内側で O 層と見なしたり、燃料の検査を省いたりはしない。抽象行の外側 callback は具体的には停止する場合でも拒否する。同期 ABI の既存の関数値を O 層の引数へ暗黙に変換する経路も拒否する。リテラルの借用閉包は引数の宣言する層で生成する。callback の層だけでは helper 自身の効果行に表れない中断を導入しない。そのような callback 引数や、効果行が発散の可能性を持つ計算済み関数値の呼び出しも未対応として拒否する。
- `Tick` は `tauto_rt::budget::tick(at).await`。poll の最中の budget の連鎖（スレッドに一つのスタック。budget のドライバが本体を poll する間だけ自分の数を積む）のすべての数を一つ減らす。どれかが 0 を下回れば、入れ物に `Slot::Budget(id)` を置いて `Pending` を返す（`id` は 0 を下回った budget のうち一番内側のもの。`eval.rs` の `exceeded_budget` と同じ選び方）。
- budget の式はドライバのループ（「`handle`（本体が O 層のとき）」のハンドラと同じ形）：

```text
loop:
  自分の数を積んで body を poll、終わったら外す
  Ready(v)                   → 式の値は v
  Pending, Budget(自分の id)  → info = Info { body, id } を作り、Exceeded(T) を外へ perform（O の perform）
                                 答えが BudgetAnswer::Value(v) なら 式の値は v
                                 答えが BudgetAnswer::More(info, m) なら body = info.body、数 = m で loop を続ける
                                 答えが BudgetAnswer::Unbounded(info) なら 数 = 無限で続ける
  Pending, それ以外           → forward().await（外の budget の燃料切れ、外のハンドラへの要求）
```

- `exceeded(info), k` の腕の `info.more(m)` は、[`semantics.md`](semantics.md) の通り `k(more(info, m))` で、これを `k` に `BudgetAnswer::More(info, m)` を渡すことで実現する。`info.unbounded()` は `BudgetAnswer::Unbounded(info)`。`k(v)` は `BudgetAnswer::Value(v)`。つまり `Exceeded(T)` の操作の Rust での答えの型は `BudgetAnswer<'a, T>` で、tauto の `T` ではない。腕の中の `k(v)` の生成でこれを包む。
- `Info<'a, T>` は affine（`Clone` しない）。本体の Future を持つ。`info.more` / `info.unbounded` は `info` を消費する（OWN「`budget`」）。
- budget の位置（どこで燃料が切れるか）は観測の対象ではない（[`nib.md`](nib.md)「budget」、[`semantics.md`](semantics.md)）。Rust の燃料の数え方は eval と違ってよい。検証では budget を含むものの期待値を別に持つ（「検証の方針」）。


### 再開しない budget の同期実体

直下の budget を受ける無条件で全域の `exceeded` 腕が継続を使わず、本体と
到達可能な呼び出しが以下の検査を通るとき、本体は同期コードで走れる。
O 層の呼び出しには `Result<T, Interrupted>` を返す別の実体を使う。
`Interrupted` は燃料切れと `resume 0` の要求を区別する。通常の実体と公開関数の
型は保ち、外側の O ハンドラと元の腕が要求を処理する。同期実体が腕を直接呼ぶ
ことはない。

- 燃料検査だけを持つ本体に加え、`resume 0` の操作を扱う。操作ごとに、同じ
  ペイロード型を受ける、ガードのない全域の腕が直近のハンドラに必要になる。
  操作名・ペイロード・位置を保って `o::reraise` で要求を渡す。外へ抜ける操作、
  条件付きの捕捉、direct 操作、再開する操作は通常の Future の経路を使う。
- 共有借用 callback は、名前付き Tauto 関数か借用閉包の本体と、その推移的な
  呼び出し先を検査できる場合に扱う。callback 自体は同期で、燃料検査や中断、
  変更操作を持たない範囲に限る。補助関数の引数を経由する転送でも、実引数の
  出自をその呼び出しの文脈に結び付ける。一つの呼び出しで確認した出自を、同じ
  補助関数へ渡す未知の callback に流用しない。Rust から来る未知の `Fn` は、
  共有借用や空の効果行だけではこの検査を通らない。
- 値・局所変数・引数・フィールド・コンテナの要素を再帰的に調べる。linear、
  extern に束縛された型、内容を確認できない型変数や標準型、所有する関数値、
  `RcRefCell` の借用ガードを持ちうる式は対象外になる。生成された非 `Copy`
  データ型、union、`Shown` も、埋込み側が独自の `Drop` を実装できるため、
  通常の入口では対象外になる。埋込み全体の明示的な信頼契約がある入口では扱えるが、
  データ型と union は内部の型も検査する。契約は他の型や借用の検査を省かない。
- 同期的な巻き戻しは、通常の Future が腕の実行中まで保持する値を先に破棄する。
  その差を観測させないため、`exceeded`・abort・return の腕とその推移的な
  呼び出し先も別に検査する。暗黙の `Clone`・`Drop` を含む型の検査に加え、
  動的な整数演算、全域性をこの検査で確認しない match、ループ、燃料検査など、panic hook
  に到達しうる処理は非 panic の検査を通らない。検査された定数演算や既知の
  非 panic builtin は扱う。腕だけで参照する関数を同期実体へ変えることはない。
- 入れ子の budget・ハンドラ、追跡できない呼び出し、複数回再開する制御は対象外に
  なる。extern は、rust-backend.md「非再開 budget の信頼契約」にある入口の契約と個別の
  束縛の契約を両方必要とする。契約があっても同期の scalar 引数・結果に限る。

呼び出し前・ループ本体の先頭という NIR の燃料検査の位置と消費量を保つ。
燃料切れは同じ位置と `Info(T)` を持つ `Exceeded` 要求になり、元の腕が受ける。
`steps` は経路を選ぶ前に一度だけ評価する。その評価が終わった時点で実行中の
外側の budget があれば通常の Future の本体を使う。外側の budget の再開能力を、
内側の腕だけから判断しない。

燃料は `Rc<Cell<u64>>` で共有し、通常の poll と同期本体のどちらも、実行中だけ
同じ `STACK` に登録する。実行中の Rust から再入して通常の `tick` が走る場合も、
登録された外側の燃料を消費する。登録を持つ RAII ガードは正常終了と unwind の
両方で元の深さまでスタックを戻す。Rust 側で panic を捕捉しても、終了した budget
の登録を残さない。要求を元の腕へ渡す時点では本体の登録を外す。この実行時の
仕組みは、未知の host callback の純粋性や破棄の観測不能性を証明するものではない。

生成対象が `sync` の場合は静的に対象外になり、実際の `tauto-rt` が `sync` feature
で作られている場合も `can_run_nonresuming` が通常経路を選ぶ。埋込み側の feature
選択が生成時と異なっても、スレッド間で共有値を観測できる実体を同期化しない。

CLI の `--explain-budget` は、トップレベルから呼ばれないライブラリ関数も下げて
診断する。`rust.nonresuming.entries` を指定する場合もライブラリの入口を下げ、
`rust.exports` の選択を適用してから契約を解決する。このモードは出力にもその関数を
含めうるため、診断を付けない成果物とのバイト一致は要件ではない。どちらも指定
しない CLI はトップレベルから到達する関数だけを下げる。

`budget_diagnostics` は、生成器と同じ検査から budget の位置・関数の実体・入口の
variant ごとの適格性と理由を返す。理由には機械可読な分類があり、通常の入口と
契約付き入口を分けて報告する。`assumptions` は契約の種類・名前・宣言位置・版を
記録し、コンパイラが検査した条件とは区別する。静的に適格であっても、実行時の
スタックと feature の条件を通るとは限らない。テスト用の経路・燃料・呼び出し回数
のカウンタはその実行を観測するためのもので、任意の Rust callback の契約を
証明するものではない。

---

## `show`、実行時エラー、位置

### `Show`

生成したクレートの中に trait を一つ定義する（`tauto-rt` に置かないのは、Rust の孤児規則で、extern の型（`std::fs::File` など）に `tauto-rt` の trait を実装できないため）。

```rust
pub trait Show { fn show(&self) -> String; }
```

- 実装：整数・`bool` は `to_string()`、`Text` は `format!("{:?}", &*t)`（eval の `{t:?}` と同じ）、`()` は `"()"`、関数の値は `"<function>"`、継続は `"<continuation>"`、`Info` は `"<budget info>"`。
- struct / enum / union / `Option` / `Result` / `Pair`：**eval.rs の表示と一字一句同じ** にする。eval の表示の規則は `tauto-rt/src/show.rs` に置き、eval もそれを使うと食い違いが起きない。
- extern の型：`format!("<{}>", "File")`（tauto の型の名前）。eval では extern は走らないので比べる相手がない。

### 実行時エラー

- 生成コードの実行時エラーは `tauto_rt::error(message, at) -> !`。中身は `std::panic::panic_any(TautoError { message, at })`。
- `main` は `std::panic::catch_unwind` で本体を走らせ、`TautoError` なら `{file}:{line}:{col}: {message}` を標準エラーに出して終了コード 1。`TautoError` 以外の panic（Rust の extern が panic した、生成器の誤りの `expect`）は `interrupted: {panic のメッセージ}` として出す（OWN「`extern`」：panic は `Interrupted`）。
- 生成した `Cargo.toml` の `[profile.*]` で `panic = "unwind"` を固定する（`abort` だと捕まえられない）。
- 文は `tauto-rt/src/messages.rs` の定数（eval と共有する。`tauto` が `tauto-rt` に依存する）。

### 位置

生成時に、位置ごとに定数を作る：`const L12_5: Loc = Loc { file: "src/main.taut", line: 12, col: 5 };`。`tauto run --backend rust` のエラーの出力は、`tauto run`（eval）の `locate` の出力と **同じ形** にする。eval のエラーが位置を持たないものは、比べるときに位置を除いて文だけ比べる。

---

## スレッド（`spawn`）

[`nib.md`](nib.md)「並列のプリミティブ」の `spawn`・`Task`・`Ref`・`Mutex`・`Atomic` を、スレッドで走らせる。

- `perform spawn(f)` はハンドラを通らず `Task { result: pending_spawn(f) }` になり、本体は `Executor` が走らせる。
  `spawn` のハンドラの腕は生成しない（`spawn<A>` の `A` は、ペイロードの型を消した腕の形では書けないため）。
- `spawn` を実行するプログラムは `sync` で作られる：`tauto_rt::Rc` が `Arc`、関数の値は
  `Send + Sync`、型パラメータは `Send + Sync`、`Ref` / `Mutex` / `Atomic` はスレッド安全。
  使わないプログラムは `Rc` のまま（`Arc` の参照カウントは原子的な操作なので `Rc` より遅い）。`TAUTO_SYNC=1` で強制できる。
- `tauto_rt::exec::Executor` が本体を走らせる。既定はタスクごとのスレッド。
  `Tauto.eure` の `rust { executor = "tokio" }` を書くと、生成する `main` が tokio の runtime を作り、
  本体を blocking pool に載せる（生成する `Cargo.toml` が `tokio` を版を固定して依存に足す。「生成するワークスペース」）。別の実行系は
  `Executor` を橋渡しクレートで実装して `set_executor` で選ぶ。
- 外部の型が `Send + Sync` でなければ、`spawn` を使うプログラムではその型の束縛の位置で拒否する。
  `Send` でない資源はホストに置き、`direct` の効果に id（affine）を渡して使う。
- 使い方は `examples/rust/tasks`。

# 第 III 部　Rust 資産を使う

## extern の生成と橋渡しクレート

### extern の包み関数

extern は、生成したクレートの `src/externs.rs` に **包み関数** として一つずつ生成する。tauto のコードは包み関数を呼ぶ。

```rust
#[doc = " extern file_open  declared src/files.taut:5:3  bound Tauto.eure:21  -> std::fs::File::open"]
pub fn file_open(path: &Text) -> Result<std::fs::File, std::io::Error> {
    std::fs::File::open(&**path)
}
```

- 包み関数の署名は、tauto の宣言を「型の写像」で Rust にしたもの（extern は `ev` を取らない。「extern と効果」）。
- 中身は Rust のパスの呼び出し一つと、「自動の変換（これ以外はしない）」の変換だけ。
- rustc がこのファイルでエラーを出したら、`tauto build` は `cargo build --message-format=json` の出力からエラーの行を見つけ、その行の包み関数の **宣言の位置と対応の位置の両方** を指すエラーにする：

```text
src/files.taut:5:3: error: the rust function std::fs::File::open does not fit the extern file_open
  Tauto.eure:21: file_open = "std::fs::File::open"
  rustc: expected `&Path`, found `u64` …
```

- 生成コードの **他のファイル** で rustc がエラーを出したら、それは「コンパイラの誤り」：`error: internal: the generated rust does not compile (this is a bug in tauto; please report it with --emit rust)` と rustc の出力を出す。利用者のエラーにしない。

### extern の型

`rust.types` の Rust の型をそのまま使う。型引数 `A` は tauto の型の実体に、`'_` は関数の `'a` に置き換える。extern の型の種は affine だけ（「未決定の問い」の「extern の型を `copy` / `shared` と宣言できるようにするか」）。生成クレートに `impl Show for std::fs::File { fn show(&self) -> String { "<File>".into() } }` を生成する（「`Show`」）。

### 自動の変換（これ以外はしない）

| tauto の位置 | 渡し方 / 受け取り方 |
|---|---|
| 引数 `&x: Text` | `&**x`（`&str` として渡す。`impl AsRef<Path>` のようなジェネリックな引数でも通るように、いつも明示する） |
| 引数 `&x: Buf` | `x`（`&String` のまま渡す。`&str` を受ける関数には Rust の deref の型強制で通る） |
| 引数 `&x: Slice(A)` | `x`（もともと `&[A]`） |
| 引数 `&x: Vec(A)` | `x`（`&Vec<A>`。`&[A]` を受ける関数には deref の型強制で通る） |
| 引数 `&f: (A…) -> R`（S 層だけ） | `&mut |a…| f(ev, a…)`（tauto の借用閉包を Rust の `FnMut` にする包み） |
| 結果 `Text` | `Text::from(…)`（`String`、`&str`、`Box<str>`、`Rc<str>` のどれからでも作れる） |
| 結果の `Option` / `Result` / `Pair` / `Vec` 内の `Text` | 所有する要素を再帰的に `Text::from(…)` で変換する。`Result` は両側を対象にする |
| それ以外 | 何もしない。型が合わなければ rustc が落とし、「extern の包み関数」のエラーになる |

結果のコンテナ変換は借用・view・利用者のデータ型の中には入らない。`List` は生成される再帰的なデータ型であり、Rust の `Vec` ではない。橋渡しでは `Vec(Text)` または `Vec(Buf)` を返し、Tauto 側で必要な `List` に明示的に変換する。引数のコンテナにはこの変換を適用しない。

`usize` と `u64` の変換は手書きの extern ではしない（`tauto bind` だけがする。「`usize` の変換」）。手書きで要るなら橋渡しクレートに関数を書く。

### 橋渡しクレート（bridge）

- `Tauto.eure` の `rust.bridge = "bridge"` は、tote からの相対パスにある普通の Cargo のクレート（`bridge/Cargo.toml`）。
- **名前は tote ごとに決まっている**：橋渡しクレートの `package.name` は `<tote 名>-bridge`（`package.name` が `files-demo` なら `files-demo-bridge`、Rust での名前は `files_demo_bridge`）。違えば `tauto build` がエラー `"error: the bridge crate must be named files-demo-bridge (bridge/Cargo.toml says glue)"`。こうすると crates.io のクレート（`rust.dependencies`）と名前がぶつからず、読み手も生成コードの `files_demo_bridge::…` を見ればどの tote の手書きの Rust か分かる。
- 生成した `Cargo.toml` には、その名前のまま依存に足す：`files-demo-bridge = { path = "<絶対パス>" }`（`package = …` で付け替えない）。`rust.dependencies` に同じ名前があればエラー（`"error: files-demo-bridge is the bridge crate and cannot be a dependency"`）。
- 橋渡しの関数は、包み関数（「extern の包み関数」）と同じ署名で書く（`pub fn read_to_buf(f: &mut std::fs::File, buf: &mut String) -> Result<u64, std::io::Error>`）。
- 修飾名の extern `File.open` の橋渡しは `files_demo_bridge::file::open`（モジュールの名前を snake_case にする）。
- 橋渡しクレートは `tauto-rt` に依存してよい（O 層の閉包 `OFnMut` を受けたいとき）。そのときは生成したワークスペースの `tauto-rt`（「`tauto-rt` のソースを埋め込む」）を path で指す。
- `tauto-build`（「`tauto-build`（Rust のプロジェクトから使う）」）で使うときも同じ名前で、利用者のクレートの `Cargo.toml` の依存に足す。

### extern と効果

- extern の行は **空でなければならない**（direct も不可）。エラー（`rows`）：`"error: an extern cannot perform effects; wrap it in a tauto function"`。失敗は `Result(T, E)` の値で返し、呼ぶ側が必要なら `raise` する（「`Result`、`fail` / `raise` / `catch`、`Slice`」）。
- extern に渡す閉包は **S 層だけ**（効果がないか、direct だけ）。Rust の関数の中のフレームは中断できないので。エラー（`rows`）：`"error: a closure passed to an extern cannot perform ask, which may suspend"`（`ask` は閉包の行の、direct でない最初の操作）。
- extern の副作用（IO）は行に出ない。信頼の一覧に出るだけ（「未決定の問い」の「extern の副作用を行に出すか」）。
- Rust の panic は効果ではなく、`Interrupted` になる（「実行時エラー」）。

### 信頼の一覧

`tauto build --backend rust` は、ビルドの最後に信頼の一覧を出す（`--quiet` で省ける）。

```text
trusted externs (rustc checks the types; the rest is trusted):
  file_open        src/files.taut:5:3   Tauto.eure:21          std::fs::File::open
  io_error_message src/files.taut:7:3   Tauto.eure:23          files_demo_bridge::io_error_message
  Regex.new        bind/regex.taut:12:5 bind/regex.eure:30     regex::Regex::new   (regex 1.11.1)
```

rustc が確かめるもの：引数と結果の型、値渡し・`&`・`&mut` の別、`-> &A` が引数から派生すること（lifetime）。人が信じるもの：行が空であること（効果を行わない、再入しない）、Drop が効果を行わず panic しないこと、種の宣言。

---

## Cargo の生成と `tauto build`

### 生成するワークスペース

```text
target/tauto/<package>/
  Cargo.toml              生成
  Cargo.lock              tote の直下の Cargo.lock を写したもの（「`Cargo.lock`」）
  .cargo/config.toml      tauto のリポジトリの .cargo/config.toml を写したもの（14 日の cooldown）
  src/lib.rs              生成コード（型、関数、Show、OP_ の定数、位置の定数）
  src/externs.rs          extern の包み関数
  src/main.rs             top があれば：fn main() { tauto_rt::run_main(|ev| <crate>::top__s(ev)) }
  tauto-rt/               tauto-rt のソース（「`tauto-rt` のソースを埋め込む」）
```

`Cargo.toml`：

```toml
[package]
name = "<package の name を snake_case に>"
version = "<package の version>"
edition = "2024"

[dependencies]
tauto-rt = { path = "tauto-rt" }
# rust.dependencies をそのまま写す
regex = "1.11.1"
# rust.bridge があれば（名前は <tote 名>-bridge のまま）
files-demo-bridge = { path = "<絶対パス>" }
# rust.executor = "tokio" なら（版は `=` で固定。crates/tauto-rustgen/src/cargo.rs の TOKIO_DEPENDENCY）
tokio = { version = "=<版>", default-features = false, features = ["rt", "rt-multi-thread"] }

[profile.dev]
panic = "unwind"
[profile.release]
panic = "unwind"
```

### `tauto-rt` のソースを埋め込む

`tauto` のバイナリは `crates/tauto-rt/` のソースを `include_str!` で持ち、ワークスペースに書き出す（`target/tauto/<package>/tauto-rt/`）。こうすると、生成コードと実行時の版がいつも一致し、ネットワークがなくてもビルドできる。`tauto-rt` は依存を持たないので書き出すだけで足りる。

### `Cargo.lock`

- tote の直下（`Tauto.eure` の隣）に `Cargo.lock` を置いてコミットする（外部の依存は固定する、というプロジェクトの規則）。
- `tauto build`：直下に `Cargo.lock` があればワークスペースに写して `cargo build --locked`。`--locked` が lock の古さで失敗したら、エラー `"error: Cargo.lock is out of date; run tauto build --update-lock"` で止まる。
- 直下に `Cargo.lock` がなければ、`cargo generate-lockfile` を走らせ、できた `Cargo.lock` を tote の直下に写して、「Cargo.lock を作った」と出す。
- `tauto build --update-lock`：`cargo update` を走らせて直下に写し戻す。
- `rust.dependencies` が空（`tauto-rt` だけ）なら、`--offline` を付ける。

### `tauto run --backend rust FILE`

`FILE` だけの一時的な tote（`target/tauto/run-<ファイル名のハッシュ>/`）を作り、`cargo build`（debug）して走らせる。`Tauto.eure` がなくても動く（extern がなければ）。出力の形は `tauto run`（eval）と同じ。

---

## `tauto-build`（Rust のプロジェクトから使う）

```rust
// 利用者の build.rs
fn main() {
    tauto_build::compile("logic/Tauto.eure").unwrap();
}

// 利用者の src/lib.rs
mod logic {
    include!(concat!(env!("OUT_DIR"), "/tauto_logic.rs"));
}
```

- `compile` は「流れ」の手順で Rust のソースを一つのファイルにし、`$OUT_DIR/tauto_<package>.rs` に書く。各ソースについて `cargo:rerun-if-changed=…` を出す。
- 利用者のクレートは `tauto-rt` に依存する（`Cargo.toml` に自分で書く）。
- `rust.dependencies` の各名前が利用者の `Cargo.toml` の `[dependencies]` にあることを確かめ、なければエラー（`"error: Tauto.eure needs the rust dependency regex; add it to Cargo.toml"`）。版は利用者の `Cargo.toml` が決める。
- `rust.exports` は Rust の facade (`generated::api`) に出す関数名の任意の一覧。省略時は以下の既定の規則、空の一覧では関数を出さない。指定した名前の重複、存在しない名前、ジェネリック関数、残る効果、Rust に写せない型はエラー。選ばなかった補助関数も検査・lowering するが、公開されないことの警告は出さない。データ型の公開は変えない。これはアクセス制御ではなく、raw generated モジュールの `pub` な内部項目を隠す保証ではない。
- `SynDiag` と `SynSpan` は `Debug` で `Show` と同じ内容を表示できる。任意の生成 AST や外部型に `Debug` の制約を要求するものではない。
- **公開する関数**：tauto の `pub` はない（「名前空間の規則」）ので、tote のトップレベルの `fn` のうち、型変数を持たず、引数と結果が 「型の写像」で Rust の型になるものを公開する。行によって形を変える：

| 関数の行 | Rust に公開する形 |
|---|---|
| 空 | `pub fn f(args…) -> R`（中で空の `Ev` を作って `f__s` を呼ぶ） |
| 空でない（direct、`Div`、`resume 0`、中断する効果を含む） | 公開しない。既定では関数名と残る効果を `cargo:warning=` で知らせる。`rust.exports` で指定した関数ならエラー。Tauto 側でハンドラを張り、行が空の関数を入口にする |

### Rust から渡す借用 callback

空の効果行を持つ関数の共有借用引数は、公開 facade では `&dyn Fn(…) -> R`
になる。Rust のローカル変数を借りる closure を渡せる。`'static` は要求しない。
facade 内の adapter が内部の evidence 引数を取り除き、借用は同期的な一回の
公開関数呼び出しの中で終わる。callback を保存・返却する API ではない。

callback の値引数と結果は整数、浮動小数点、Bool、Text、Buf、単位型、Never、
それらを含む Option、Result、Pair、Vec、Array、HashMap、生成データ型を扱う。
引数はこれらの共有借用でもよい。データのフィールドを含め、関数値と借用を
内部に含む値、view 型、callback の借用結果は扱わない。
Text は `tauto_rt::Text` であり、String との暗黙の再帰変換はしない。
所有 callback、可変借用 callback、効果行の空でない callback は公開しない。
callback の効果を関数内の handler で処理しても、この制限は変わらない。

空の行は Tauto 側の型と呼び出し契約を表す。Rust の `Fn` は host の純粋性、
Tauto への再入がないこと、panic しないこと、破棄や参照カウントを観測しないことを
証明しない。通常の facade の型から、非再開 budget の信頼契約を推論しない。
host は IO、内部可変性、panic などの振る舞いに責任を持つ。
実行できる例と拒否例は `crates/tauto-build/tests/build_rs.rs` と
`crates/tauto-build/tests/exports.rs` で検査する。

### 非再開 budget の信頼契約

`Tauto.eure` の `rust.nonresuming.entries` は、別名の契約付き Rust facade と、
その入口になる選択済みの Tauto 公開関数を対応付ける。値は関数名だけであり、
callback の引数名を列挙するものではない。callback を取らない関数も入口にできる。
契約付き facade は先頭に `&tauto_rt::budget_contract::TrustedBudgetHost` を取り、
残りの引数と結果は通常の facade と同じになる。元の facade と裸の `&dyn Fn` の
ABI は変えない。契約付き実体は入口ごとに分け、通常の呼び出しへ契約を広げない。

`TrustedBudgetHost::assert_contract` は、呼び出し元が `closed-host-v1` を明示的に
引き受ける安全な Rust API である。token は callback や host の値を所有・検査せず、
借用して渡す各呼び出しの入力と文脈について、埋込み全体の責任を表す。
この契約はコンパイラの検査結果でもカーネルの証明でもなく、Rust のメモリ安全性の
前提でもない。誤った宣言は最適化の下でプログラムの振る舞いを変えうるが、unsafe
な生成コードを許すものではない。

契約の範囲は callback と extern だけでなく、捕獲値、暗黙の変換、`Clone`・`Drop`、
生成された非 `Copy` 型への埋込み側の実装、呼び出し中に働く hook や他の観測者まで
含む。認める host 呼び出しは正常に戻り、発散・中断・panic・unwind・panic hook の
起動を行わない。host は Tauto や実行時へ再入せず、渡された借用や callback を保存
せず、参照カウント、破棄順序、値や借用の生存期間を観測したり結果に利用したり
しない。戻り値以外の観測可能な host 効果も契約の対象外になる。プログラムの動作に
影響せず観測もされない私的な scalar 計測は、そのような効果ではない。必要な入力の
範囲や文脈は呼び出し元が確かめる。テストのカウンタで経路や呼び出し回数を観測しても、
この信頼の前提を検証したことにはならない。

extern には、さらに `rust.nonresuming.extern` で各 Tauto extern 名に
`closed-host-v1` を明記する。個別の束縛だけでは通常の入口を適格にせず、入口の
契約だけでも未宣言の extern を適格にしない。認める署名は同期で、引数と結果が
整数・浮動小数点・Bool・単位型・Never のいずれかであるものに限る。Text、コンテナ、
借用や外部型を含む署名は通常経路を使う。

契約は主マニフェストからだけ読み、生成された bindings ファイルから取り込まない。
未知の契約版、存在しない extern、選択されていない公開関数、Rust に公開できない
入口、不正または変換後に衝突する facade 名は拒否する。静的診断では埋込み・callback・
extern の前提とその宣言位置を明示する。

契約付きの文脈で調べる budget は、選んだ入口自身の本体にあるものに限る。その
budget 本体の callback を補助関数へ転送する出自は追跡するが、別の関数の内部にある
budget へ入口の契約を転送しない。そのような budget が host の契約を必要とする
場合や、対象の budget の内側に別の budget がある場合は通常の Future の経路を使う。

---

## `tauto bind`

### 何をするか

```text
tauto bind regex --config bind/regex.config.eure
```

1. 一時的なワークスペース（`target/tauto/bind-regex/`）に、`regex` に依存するだけのクレートを作る（版は `Tauto.eure` の `rust.dependencies`、lock は tote の `Cargo.lock`）。
2. `cargo rustdoc -p regex --locked -- -Z unstable-options --output-format json` で rustdoc JSON を作る（ツールチェーンは `rust-toolchain.toml` の nightly。rustdoc の JSON の出力はほかでは不安定）。
3. `rustdoc-types` で読み、設定に従って次の三つを書く：
   - `bind/regex.taut`：型と extern の宣言（人がレビューする信頼の面）。
   - `bind/regex.eure`：Rust への対応（`types`、`extern`、変換の印）。`Tauto.eure` の `rust.bindings` に足して使う。
   - `bind/regex.report.md`：写せなかった公開の項目と、その理由。
4. `--check`：書かずに生成して、書かれているファイルと比べる。違えば `bind/regex.taut is out of date (run tauto bind regex …)` を出して終了コード 1。

三つのファイルの先頭に、クレートの名前・版・rustdoc JSON の `format_version`・設定ファイルの名前を書く。生成物は手で直さない（直したければ設定を変える）。

### 設定 `bind/<crate>.config.eure`

```eure
crate = "regex"
# 取り込む公開の項目（Rust のパス）。書いたものだけを取り込む。
items = ["regex::Regex", "regex::Captures", "regex::Error", "regex::escape"]
# ジェネリックな関数の実体化（型引数を具体的な型で埋めたものだけを出す）
instances {
  "regex::Regex::replace_all" = ["&str"]
}
# 取り込む trait の実装
traits = ["Display", "Clone", "PartialEq", "Iterator"]
# 名前の付け替え（tauto の名前がぶつかるとき）
rename {
  "regex::Error" = "RegexError"
}
```

### 写像の規則

| Rust の項目 | `bind/<crate>.taut` に出るもの |
|---|---|
| `pub struct S`（フィールドに関係なく） | `affine struct S {}`（中身の見えない型）。透明な struct の写像は対象外 |
| `pub enum E` | 同上（`affine struct E {}`）。透明な enum の写像は対象外 |
| lifetime を持つ型（`Captures<'h>`、`Iter<'a, T>`、`Matches<'r, 'h>`） | `view struct S(…) {}`（「extern の view 型」）。Rust の型の lifetime は数だけ `'_` で書く（`Matches<'_, '_>`） |
| `impl S { pub fn f(&self, a: A) -> R }` | `module S { extern { fn f(&s: S, a: A) -> R } }` |
| `&mut self` / `self` | `&mut s: S` / `s: S` |
| 関連関数（`self` なし、`Regex::new`） | `module S { extern { fn new(…) -> … } }` |
| クレートの直下・モジュールの関数（`regex::escape`） | Rust のモジュールのパスと同じ名前の tauto のモジュール（`module regex { extern { fn escape(…) } }`） |
| `Display` | `module S { extern { fn to_text(&s: S) -> Text } }` |
| `Clone` | `fn clone(&s: S) -> S` |
| `PartialEq` | `fn eq(&a: S, &b: S) -> Bool` |
| `Iterator<Item = T>` | `fn next(&mut it: S) -> Option(T)`（`S` は view なら `var &it` で受ける）。`Item = &str` は `Option(Text)`（写し。印 `u`） |
| `Default` | `fn default() -> S` |
| `-> &T`、`-> Option<&T>`、`-> &mut T` | 「view 型」・「`-> &mut A` と `let &mut x`」の view と `-> &mut`（view に対応していなければ、その項目を出さずに report に書く） |
| `&str` の引数 | `&s: Text` |
| `Cow<str>` の結果 | `Buf`（所有する写し。印 `c`）。`replace` の `R: Replacer` は `instances` に `"&str"` を書く |
| `String` | `Buf` |
| `&[T]` | `&Slice(T)` |
| `Vec<T>`、`Option<T>`、`Result<T, E>`、`(A, B)` | `Vec(T)`、`Option(T)`、`Result(T, E)`、`Pair(A, B)` |
| `usize` / `isize` | `u64` / `i64`（「`usize` の変換」） |
| `bool`、`i32`、`i64`、`u8`、`u32`、`u64`、`f64` | 同じもの |
| `impl FnMut(A) -> B` などの閉包の引数 | `&f: (A) -> B`（S 層だけを受ける。「extern と効果」） |
| `dyn Trait`、`Send` / `Sync` の境界、`unsafe fn`、const generics、`async fn`、`i8` `i16` `u16` `i128` `u128` `f32` `char`、型引数の実体化が設定にないジェネリックな関数、マクロ | 出さない。report に「項目のパス：理由」を書く |

### `usize` の変換

`bind/<crate>.eure` の各 extern に、引数と結果ごとに変換の印（`usize`、`isize`）を書く。包み関数の生成器（「extern の包み関数」）は印に従って `usize::try_from(x).unwrap_or_else(|_| tauto_rt::error(messages::TOO_LARGE, at))` / `x as u64` を挟む。

同じ表には、結果の変換の印もある：`Cow<str>` の結果は `c`（`.into_owned()`）、`Iterator<Item = &str>` の `next` は `u`（`.map(Text::from)`）。

# 第 IV 部　検証

## 検証の方針

- **rustc による再検査。** 所有権の判断が `ok` の例題は、生成した Rust が rustc の型検査と借用検査を通る。通らなければ `lin.rs` か生成器の誤りである。
- **差分比較。** 同じプログラムを `eval.rs` と生成コードで走らせ、`show` の列と実行時エラーの文が一致する。ただし budget を含むものは、燃料を数える場所が違うので、Rust 側の期待値を別に持つ（「燃料を数える場所」）。extern を使うものも `eval.rs` では走らないので、同じく別の期待値を持つ。
- **drop bomb と動的所有権検査の照合。** debug ビルドで drop bomb が鳴らず、`tauto run --check-ownership`（OWN「実行時の意味論」）も誤りを出さない。drop bomb は言語の意味ではなく二つ目の検査器の道具で、release では消えてよい。鳴ったら、同じケースを `tauto run --check-ownership` で走らせる。そこでも誤りが出れば `lin.rs` が受理してはいけないものを受理しているので、何より先に直し、拒否の回帰例を足す。出なければ生成器の誤り（`defuse()` の抜けや分解の位置）で、生成器を直す。bomb を外す、`thread::panicking()` の条件を広げる、で済ませない。Drop の順（宣言の逆順、`x := v` の時点、`resume 0` で抜けるとき）は、捨てられた名前を記録する橋渡しクレートで確かめる。
- **`tauto-rt` 単体。** 手書きの Rust で、各層の形が通ることを確かめる。

---

## 未決定の問い

| 問い | 方向 |
|---|---|
| extern の型を `copy` / `shared` と宣言できるようにするか | 許す。生成側が `Copy` / `Clone` の実装を rustc に確かめさせ、`shared` は「`Clone` が安く純粋」という信頼にする。 |
| extern の副作用を行に出すか（ホストの direct の効果 `io`） | 信頼の一覧だけに置く。 |
| `direct ! {Div}`（direct の腕で `while` や再帰を許す） | 許すなら「行に `Div` のある direct は budget の下では O 層」となり、linear は跨げなくなる。 |
| `Decimal` の表現（OWN「未決定」） | 任意精度なら shared。 |
| Rust の `async` との相互運用 | 扱わない。スレッドは [`nib.md`](nib.md)「並列のプリミティブ」。 |

---

## 参考

- OWN：[`ownership.md`](ownership.md)（種、借用、再開量、CFL）。
- [`semantics.md`](semantics.md)（実行の意味。差分比較の正）。
- [`classes.md`](classes.md)（型クラスの Rust への写像）。
- rustdoc JSON：`rustdoc-types` crate、`FORMAT_VERSION`。
