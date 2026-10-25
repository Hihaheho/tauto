# 所有権・借用・再開量

Nib（したがって tauto）に **値の種（copy / shared / affine / linear）**、
**二級の借用（`&x`, `&mut x`）**、**効果の再開量（`resume 0 / <=1 / 1 / ω`）**
の仕様と、Lean での証明です。

この文書には結論だけを書きます（文献と書き味の比較は載せず、却下した案は「決めたこと」の表に一行で挙げるだけにします）。
**この文書に書いてあることは決まったことで、決まっていないのは「未決定」の節にあることだけ**です。
設計を変えるときは、この文書を先に直します。

正の順序は [`nib.md`](nib.md) と同じです。この文書は [`semantics.md`](semantics.md)
を補う仕様で、実装（`crates/`）が正ではありません。食い違えば実装を直します。

---

## 要約

1. すべての型に **種** がある：`copy ⊑ shared ⊑ affine ⊑ linear`。種は型の構造から決まり、宣言（`affine struct File`、`linear struct Handshake { … }`）で締められる。緩める方向はない。
2. copy と shared は **型付けの規則上は同じ**（複製も捨てるも自由）。違いは実行時のコスト（ビットコピーか参照カウントか）だけ。合わせて「複製可」と呼ぶ。
3. affine は **一度しか使えないが捨ててよい**。linear は **ちょうど一度使う**（捨てられない）。
4. 束縛に量は書かない。使い方の検査は型の種から決まる。ジェネリクスの型変数は既定で affine と見なし、`<A: shared>`、`<A: linear>` で変える。
5. **借用は二級**：`&x` / `&mut x` は引数の位置と `let &x = f(&v)` にだけ現れ、構造体・セル・脱出する閉包・効果の引数には入らない。lifetime はない。`&mut` を取れるのは `var` だけ。
6. 借用を返す関数 `-> &A` は、すべての借用引数から派生し、`let &x = f(&v)` は現在のブロックの終わりまで `v` を凍結する（字句的、NLL なし）。
7. 複製可な `A` について **`&A` は `A` そのもの**。
8. 効果は宣言で **再開量** を持つ：`resume 0`（再開しない）、`<=1`（高々一度、**既定**）、`1`（ちょうど一度）、`ω`（何度でも）。multi-shot は `resume ω` と明示する。
9. 腕の継続 `k` の型は再開量で決まる：`<=1` なら affine な関数、`1` なら linear な関数、`ω` なら複製可な関数、`0` なら `k` はない。
10. **制御フロー線形性**：ある部分式の行に `ω` の効果があれば、その部分式を跨いで生きている affine / linear の値があってはならない。行に `1` 以外の効果があれば、跨いで生きている linear の値があってはならない。この検査は関数だけでなく `handle` の本体とブロックにもかかる。
11. ハンドラの腕（`return` 以外）が外から捕まえる変数は複製可でなければならない。
12. 行変数 `<e>` は既定で任意の再開量を許し、`<e: <=1>` で `ω` を締め出す。
13. **Drop は構造的・自動**。affine の値は束縛のブロックの終わりで捨てられる。ユーザー定義の Drop はない。linear は捨てられない（型エラー）。
14. **`clone` は構造的・自動**。構成要素がすべて複製可能な affine 型に `clone(&x)` が付く。不透明な型（extern）には付かない。
15. 閉包は捕まえた値の種を持つ（affine を move で捕まえれば affine な閉包＝一度しか呼べない）。借用や affine な `var` を捕まえた閉包は **借用閉包** で、借用と同じ規則に従う（引数に渡す・呼ぶだけ）。
16. `var` の中身が affine なら、中身を move して出せるのは宣言したブロックの直線的なコードだけ。閉包からは借用と代入だけ。
17. `budget` の本体では、どの部分式も `Exceeded`（`<=1`）を行いうるものとして扱う。したがって linear の値は `budget` の本体に生きていられない。
18. 型・命題・証明の中での出現は使用に数えない（消去される位置）。**カーネル（`check.rs`, `check/core.rs`）は変えない。** この仕様は Nib の層（`types.rs`, `rows.rs`, `lin.rs`）に閉じる。
19. Lean の証明の方針は「**`HasType` と `Safety.lean` を壊さず、使用の判断 `Lin` を別の述語にして、トークンの一意性を不変量として示す**」。

---

## 用語

| 語 | 意味 |
|---|---|
| 種（kind） | 型ごとに決まる、値の複製と破棄の許される度合い。`copy`, `shared`, `affine`, `linear` の四つ。 |
| 複製可（dup） | 種が `copy` か `shared` であること。 |
| 所有（own） | affine / linear の値を名前が持つこと。使う（move）と持ち主が変わる。 |
| 使用（use） | 値を move する出現。借用は使用ではない。型・命題・証明の中の出現も使用ではない。 |
| 借用（borrow） | `&x`（読むだけ）、`&mut x`（書いてよい）。二級：引数と `let &x` にだけ現れる。 |
| 凍結（freeze） | `let &x = f(&v)` の間、`v` を move・`&mut`・代入できない状態。 |
| 再開量（resume quantity） | 効果の宣言が決める、継続 `k` を呼べる回数：`0`, `<=1`, `1`, `ω`。 |
| 行の量 q(ρ) | 行 ρ に含まれる効果の再開量の集合。行変数は宣言の境界で決まる。 |
| 跨いで生きている（live across） | ある部分式が評価される間、所有されていて、その後に使われるか、ブロックの終わりで捨てられる値。 |
| 制御フロー線形性（CFL） | 「affine / linear の値は、それにふさわしい再開量の制御フローの下でしか生きていられない」という規則。 |
| トークン | Lean のモデルで affine / linear の値に付ける一意な番号。一意性を定理にするための道具。 |

---

## 種

### 格子

```text
copy ⊑ shared ⊑ affine ⊑ linear
```

`join` は格子の上限。

| 種 | 複製 | 捨てる | 実行時 |
|---|---|---|---|
| `copy` | 可 | 可 | ビットコピー |
| `shared` | 可 | 可 | 参照カウント（唯一所有なら in-place 更新） |
| `affine` | 不可 | 可 | 所有権の移動。ブロックの終わりで Drop |
| `linear` | 不可 | 不可 | 所有権の移動。捨てると型エラー |

### 型の種 kind(T)

```text
kind(i32) = kind(i64) = kind(u8) = kind(u32) = kind(u64) = copy
kind(Bool) = kind(Float) = kind(Decimal) = kind(()) = kind(Never) = copy
kind(Text) = shared
kind(@a T) = kind(T)
kind(A | B) = join(kind A, kind B)
kind(D(T₁, …, Tₙ))     D は struct / enum
  = join(declared(D), floor(D), kind(各フィールドの型に T を代入したもの))
    declared(D) : 宣言に書いた種。書かなければ copy（= 下限）
    floor(D)    : D が再帰的（自分を直接・間接に含む）なら shared、そうでなければ copy
kind((P₁, …, Pₙ) -> R ! ρ) = 型に書いた種。書かなければ shared
kind(affine (P…) -> R ! ρ) = affine
kind(linear (P…) -> R ! ρ) = linear
kind(Info(T)) = affine
kind(A)  A は型変数 = その境界。書かなければ affine。`<A: shared>` なら shared、`<A: linear>` なら linear
```

- 宣言 `affine struct X { … }`、`linear enum Y { … }`、`shared struct Z { … }`、`copy struct W { … }` が書ける。構造から決まる種より **緩い** 宣言は型エラー（`copy struct P { t: Text }` は `Text` が shared なので拒否）。
- 再帰的な型は少なくとも shared。`enum List(A) { nil, cons(A, List(A)) }` は `kind(List(i64)) = shared`、`kind(List(File)) = affine`。
- 型変数は既定 affine なので、ジェネリックな関数の中では `A` の値を複製できず捨てられる。`<A: shared>` で複製でき、`<A: linear>` で捨てられなくなる。呼び出し側では実際の型の種が境界に収まることを確かめる（`<A>` に `A := Handshake` を当てるのは `linear ⊑ affine` が偽なので拒否。`<A: linear>` なら可。`v: Vec(Handshake)` を `vec_clear<A>(&mut v)` に渡すときがこれにあたる）。
- `Option(A)`、`Pair(A, B)`、`List(A)` は宣言に種を書かない。構造で決まる。
- 関数型の種は型に書く。閉包式の種は捕まえた値の種の `join`（「閉包」）。閉包式の種は、期待される関数型の種に収まらなければ型エラー。

### 複製可の二つの種について

`copy` と `shared` を分けるのは実行時の表現のためだけで、「使用の規則」–「再開量と制御フロー線形性」の規則はどちらも「複製可」として同じに扱う。
`copy struct` と宣言できるのは「ビットコピーで複製できる」ことを型に見せるためで、フィールドに shared があれば型エラー。
関数の署名と局所変数の型に `shared` な型が現れない関数は参照カウントを一切走らせない。これを宣言で検査させる形（たとえば `no shared`）は未決定（「決めたことと未決定」）。

---

## 使用の規則

これらは **束縛ごと、ブロックごと** の規則で、既存の型検査の後に走る別の検査（`lin.rs`）が見る。型検査を通ったプログラムだけが対象。

### 束縛の使用

- 複製可の束縛：制限なし。
- affine の束縛：値として使う（move）のは **各実行経路で高々一度**。使わなければブロックの終わりで捨てられる。
- linear の束縛：値として使うのは **各実行経路でちょうど一度**。`return` や `break` で抜ける経路でも一度。
- 「値として使う」とは：引数に渡す、別の束縛に入れる、構造体のフィールドに入れる、`:=` の右辺にする、関数の結果として返す、`match` の対象にする、閉包が捕まえる（「閉包」）、効果の引数にする。
- 「値として使う」でないもの：`&x`、`&mut x`、`x.f` で `f` が複製可なフィールド（複製）、`==`・`!=` の被演算子（借用として読む。[`classes.md`](classes.md)「`==` と `!=`」）、型・命題・証明の中の出現。

### `let` と `var`

- `let x = e`：`e` の値を `x` が所有する。
- `var x = e`：セルを作る。種は中身の種。
  - 中身が複製可：制限はない。閉包と継続はセルを共有する。
  - 中身が affine：**affine な var**。`x := v` は古い中身を捨てる（Drop）。中身を move して出す（`f(x)`）のは、`x` を宣言したブロックの直線的なコードでだけ許す。閉包の中では借用（`&x`, `&mut x`）と代入だけ。move した後に読むのはエラーで、代入すれば再び使える。
  - 中身が linear：**禁止**（型エラー。`x := v` が古い中身を捨てるため）。
- ループ（`while`, `loop`）の本体で、本体の外で宣言した affine / linear の束縛を move するのはエラー。本体の中で宣言した束縛は普通に扱う。

### フィールドと `match`

- `s.f`：`f` の型が複製可なら複製。affine / linear なら、所有している `s` からは取り出せない（部分的な move はない）。`&s.f` / `&mut s.f` で借用するか、パターンで全体を分解する。
- `match e { … }`：`e` が所有された affine / linear の値なら、`match` が `e` を消費し、腕のパターン変数がフィールドを所有する。消費した後に `e` を使うのはエラー（`_ => e` は書けない。`other => other` と書く）。
- `match` の対象が借用（`&` の引数、`let &x`）なら、腕のパターン変数も借用（「借用の `match`」）。
- `enum` の各腕で、affine のフィールドを束縛しないパターン（`_`、`Some(_)`）はそのフィールドを捨てる（Drop）。linear のフィールドをパターンで捨てるのはエラー。

### `if` と `match` の経路

- 分岐の各経路で使用回数を数える。affine は各経路で ≤1、linear は各経路でちょうど 1。分岐のあとに使うなら、どの経路でも使っていないこと。

### Drop の時点と順序

- affine の束縛が move されずにブロックの終わりに達したら、宣言の逆順に捨てる。`var` は現在の中身を捨てる。式の途中の一時的な値（`f(g())` の `g()` の結果が affine で、`f` が借用で受け取る場合）は、その文の終わりで捨てる。
- 捨てるとは：tauto で定義した型ならフィールドを再帰的に捨てる（構造的）。extern の型なら Rust の `Drop`（「`extern`」）。
- Drop は効果を行わない（行に出ない）。これは extern の型についての **信頼**（「`extern`」）。

### `return`・`break`・`continue`

- 抜ける時点で生きている affine の束縛は捨てられる。linear があればエラー。
- 関数の結果として返す値は move。

---

## 関数と閉包

### 引数

- `fn f(x: A)`：`x` を所有して受け取る（move）。呼び出し側は `f(v)` と書き、`v` は使われる。
- `fn f(&x: A)`：借用で受け取る。呼び出し側は `f(&v)` と書く。`A` が複製可なら `&A ≡ A` で、`x` は値そのもの。
- `fn f(&mut x: A)`：可変の借用。呼び出し側は `f(&mut v)` と書き、`v` は `var`（またはその field path、または `&mut` の引数）でなければならない。
- 引数は左から右に評価され、move はその時点で起こる。`g(&mut v, &v)` は同じ呼び出しの中で `v` の `&mut` と `&` が重なるのでエラー（「一つの呼び出しの中の衝突」）。`g(v, &v)` も、先に `v` が move されるのでエラー。先に `let` で切り出す。

### 結果

- `-> A`：所有を返す。
- `-> &A`：借用を返す。関数に少なくとも一つの `&` / `&mut` 引数があること。結果の借用は **すべての借用引数から派生する** と見なす。本体で返せるのは、借用引数そのもの、その field path、または `-> &A` の関数を借用引数に適用した結果だけ。閉包は借用を返せない（名前付きの `fn` だけ）。
- `-> &mut A` は **ない**。

### ジェネリクス

- `<A>`：既定 affine。`<A: shared>`、`<A: linear>`。
- 行変数 `<e>`：既定で任意の再開量。`<e: <=1>`：`ω` の効果を含まない行だけが代入できる。`<e: 1>` は用意しない。
- 呼び出し側で、実際の型の種・行の量が境界に収まることを検査する。

### 閉包

- 閉包は自由変数を **捕まえる**。所有している affine / linear の変数を捕まえるのは move（その後、外では使えない）。複製可の変数の捕まえ方に制限はない。`var` はセルへの参照として捕まえる（共有）。
- 閉包式の種 = `join`（捕まえた所有変数の種）。何も捕まえなければ `copy`。affine な変数を move で捕まえた閉包は affine な関数型（`affine (…) -> …`）を持ち、**一度しか呼べない**（呼ぶことが使用）。linear を捕まえれば linear な関数（ちょうど一度呼ぶ）。
- 期待される関数型に種が書いてあれば、閉包の種はそれに収まること。書いていなければ shared が期待されているので、affine を捕まえる閉包はエラー。
- **借用閉包**：借用の変数（`&x` / `&mut x` の引数、`let &x`）または affine な `var` を捕まえた閉包は借用と同じ扱い（「借用閉包」）。引数の `&f: (…) -> …` の位置に渡すか、その場で呼ぶだけ。構造体・セル・結果に入れられない。
- 閉包の引数も `&x: A` と書ける。呼ぶ側（たとえば `vec_each` の実装）は借用を渡す。
- `&f: (…) -> …` と宣言された引数に閉包を渡すとき、閉包リテラルはそのまま書く（その文の間だけ生きる一時的な値を借用する）。名前の付いた閉包の変数は `&g` と書く。
- 閉包の種・借用性は閉包式から構文的に決まる。推論は要らない。

### 呼び出し

- 複製可な関数値 `f` を呼ぶのは使用ではない。affine な関数値を呼ぶのは使用（その後 `f` は使えない）。linear な関数値は各経路でちょうど一度呼ぶ。
- 借用閉包を呼ぶのは使用ではない。

---

## 借用

### どこに書けるか

借用式 `&p`、`&mut p`（`p` は局所変数、またはその field path `x.f.g`）が現れてよいのは次の三か所だけ。

1. `&` / `&mut` と宣言された引数の位置：`f(&v)`、`f(&mut v.items)`。
2. `let &x = <借用を返す関数の呼び出し>`。
3. `match` の対象：`match &v { … }`（「借用の `match`」）。

それ以外（`let y = &v`、構造体のフィールド、`:=` の右辺、結果、効果の引数、閉包の捕まえた値として脱出）はすべて型エラー。

### 借用の変数

- `&x: A` の引数、`let &x` の `x`、借用の `match` のパターン変数を **借用の変数** と呼ぶ。
- 借用の変数でできること：`&` の引数に渡す（再借用）、`match` する、複製可なフィールドを読む、field path を借用する（`&x.f`）、`-> &A` の関数に渡す。
- `&mut x: A` の変数でさらにできること：`&mut` の引数に渡す、`x := v`（古い中身を捨てる）、`&mut x.f`。
- 借用の変数でできないこと：move する（所有の位置に置く）、構造体・セル・結果に入れる、効果の引数にする、脱出する閉包に捕まえさせる（捕まえた閉包は借用閉包になる）。
- `A` が複製可なら、`&x: A` の `x` は値そのもの（`&A ≡ A`）で、何にでも使える。

### 凍結

- `let &x = f(&a, &mut b)` は、`x` の生きている間（**現在のブロックの終わりまで**）`a` と `b` を凍結する。凍結された束縛は move・`&mut`・`:=` できない。`&` はできる（`f` の引数が `&` のとき）。`&mut b` から派生した借用があるときは、`b` の `&` もできない。
- `-> &A` の結果が複製可（`A` が複製可に実体化）なら凍結は起こらない。
- 凍結は字句的で、ブロックの終わりで解ける。NLL（最後の使用で解ける）はしない。

### 一つの呼び出しの中の衝突

引数を左から右に見て、同じ呼び出しの中で次が重なればエラー。

- `&mut p` と、`p` と重なる path の `&p'` または `&mut p'`。
- `p` の move と、`p` と重なる path の借用。

重なるとは、一方が他方の接頭辞であること（`a` と `a.b` は重なる、`a.b` と `a.c` は重ならない）。

### 借用閉包

借用の変数か affine な `var` を捕まえた閉包は、「借用の変数」の借用の変数と同じ制約を受ける：`&f: (…) -> …` と宣言された引数に渡すか、その場で呼ぶ。`fold`、`each`、`map` など標準ライブラリの高階関数は閉包を `&f` で受け取る（「標準ライブラリ」）。

### 借用の `match`

`match` の対象が借用の変数または `&v` なら、腕のパターン変数は借用の変数になる（Rust の default binding modes に当たる）。複製可なフィールドは値そのもの。

### 借用と効果

- 借用は効果の引数にできない（`perform e(&x)` はエラー）。腕はハンドラの外で動くので、借用が持ち主の生存期間を越える。
- `&` の借用の変数は、どんな再開量の効果を跨いでも生きていてよい。
- `&mut` の借用の変数と affine な `var` は、`ω` の効果を跨いで生きていられない（「制御フロー線形性（CFL）の規則」）。
- 本体か `return` 腕が `handle` の外の束縛を借用する（`&x`・`&mut x` と書く、または外の借用の変数・借用閉包を使う）とき、その `handle` の `k` は **腕の中でその場で呼ぶだけ** にする。値（構築子の引数、`let` の右辺など）に入れる、閉包や入れ子の `handle` の中で使う、腕の結果として返すことはエラー（「k holds a borrow of x, so it may only be called in its arm」）。継続は本体の残りと `return` 腕を捕まえるので借用も捕まえ、外に出れば持ち主が Drop・move された後に借用を使える。再開量によらない（`<=1` の `k` も affine な値として外に出せる）。

---

## 再開量と制御フロー線形性

### 宣言

```nib
effect ask: (q: Text) -> i64                 // resume <=1（既定）
effect choose: () -> Bool resume ω           // multi-shot
effect fail: (msg: Text) -> Never resume 0   // 再開しない
effect step: () -> () resume 1               // ちょうど一度再開する
```

- `resume` は署名の結果型の後ろに書く。書かなければ `<=1`。
- 組み込み：`Div` は `0`、`Exceeded(T)` は `<=1`、`show` は `<=1`、`Match(A)`（内部）は `<=1`。
- 効果の集まり `effect State(T) = {Get(T), Put(T)}` は各操作の宣言の量を持つ。

### 腕と `k`

`handle { body } with { e(p…), k => arm; return v => r }` について：

| 再開量 | `k` の型 | 腕で許される `k` の使い方 |
|---|---|---|
| `0` | なし。腕は `e(p…) => arm` と書く（`k` を書くとエラー） | — |
| `<=1` | `affine (R) -> T ! ρ_h` | 高々一度呼ぶ。呼ばなければ捨てる（継続の中の affine は Drop） |
| `1` | `linear (R) -> T ! ρ_h` | 各経路でちょうど一度呼ぶ |
| `ω` | `(R) -> T ! ρ_h` | 自由 |

`R` は操作の結果型、`T` はハンドラの結果型、`ρ_h` はハンドルの行。

- 腕（`return` 以外）が **外から捕まえる変数は複製可** でなければならない。腕は `perform` のたびに走り、`k` は腕を含むハンドラを再び張るので、腕の中の affine は複数回使われうる。affine な状態を持ち回すには、腕が関数を返す形（`get(), k => (m) => k(m)(m)`）でパラメータとして渡すか、`var` を使う。
- `return` 腕の自由変数と、本体が使う `handle` の外の束縛（借用するだけのものは除く）は「本体を跨いで生きている」として 「制御フロー線形性（CFL）の規則」の規則を受ける。継続は本体の残りを捕まえるので、そこで使う外の束縛も捕まえる。
- `k` を閉包に入れて返せば、その閉包の種は `k` の種を継ぐ（`<=1` なら affine）。
- ただし本体か `return` 腕が外を借用する `handle` では、`k` はその場で呼ぶことしかできない（「借用と効果」）。

### 行の量

- `q(e)` = 効果 `e` の宣言の再開量。
- `q(ρ)` = ρ に現れる効果の `q` の集合。行変数 `e` は `{0, <=1, 1, ω}`、`e: <=1` なら `{0, <=1, 1}`。
- 「ρ に ω がある」= `ω ∈ q(ρ)`。「ρ に 1 以外がある」= `q(ρ) \ {1} ≠ ∅`。

### 制御フロー線形性（CFL）の規則

部分式 `t` を評価する間に **跨いで生きている** 所有の束縛（「用語」）を `L(t)` とする。各部分式 `t` について：

```text
ω ∈ q(ρ(t))          ⟹  L(t) に affine / linear の束縛も、&mut の借用の変数も、affine な var もない
q(ρ(t)) \ {1} ≠ ∅    ⟹  L(t) に linear の束縛がない
```

`ρ(t)` は `t` の行（`t` が呼び出しなら呼ばれる関数の行、`perform` ならその効果、`handle` なら本体の行から腕が取り除いたもの、など、既存の行の検査が与えるもの）。

- この規則は **すべての部分式** に適用する：ブロックの文、引数、コンストラクタのフィールド、`if` の条件、`handle` の本体、`match` の対象。実装は後ろ向きの生存解析で `L(t)` を求める。
- 呼び出しの引数は左から評価され、評価の済んだ引数の値は呼び出しの中で残りの引数を待つ。`f(x, perform ask())` の `x` は `ask` を跨いで生きている（実装では、引数へ move した値を残りの引数の間だけ束縛として数える）。
- 関数の境界：関数の本体を跨いで生きているものは呼び出し側にあるので、呼び出し側で `ρ(f)` について検査される。関数の本体の中は本体の規則でよい。
- 直観：`ω` の効果は継続を複製するので、継続の中の affine は複製される。`0` と `<=1` の効果は継続を捨てうるので、継続の中の linear は捨てられる。

例：

```nib
effect choose: () -> Bool resume ω

var v = vec_new()            // affine な var
vec_push(&mut v, 1)
let b = handle {
  if perform choose() { 1 } else { 2 }     // OK：v はこの handle の本体の中では生きていない
} with { choose(), k => k(true) + k(false) }

let c = handle {
  var w = vec_new()          // エラー：affine な var w が choose（ω）を跨いで生きている
  if perform choose() { vec_len(&w) } else { 0 }
} with { choose(), k => k(true) + k(false) }
```

二つ目は `w` の宣言を `handle` の外に出し、本体には `&w` だけを持たせれば通る。

### `budget`

`budget(steps: n) { body }` の本体では、**どの部分式の行にも `Exceeded(T)`（`<=1`）があるもの** として 「制御フロー線形性（CFL）の規則」を適用する。したがって linear の束縛は `budget` の本体に生きていられない。affine は生きていてよく、超過で捨てられれば Drop される。

`exceeded(info), k` の `info` は affine：`info.more(m)` と `info.unbounded()` は `info` を使う。`k(v)` を呼んで `info` を使わなければ、止まった本体ごと捨てられる。

`budget` の本体は **外の束縛を借用できない**（`&x`・`&mut x` と書く、外の借用の変数・借用閉包を使う、のいずれもエラー「x is borrowed in a budget, whose stopped body may outlive it」）。止まった本体は `info` として `exceeded` の腕に渡り、腕は `info` を値に入れて返せるので、借用が持ち主の Drop・move の後まで残る（「借用と効果」の `k` と同じ穴）。本体の中で作った束縛は借用してよい。

### 手で確かめる表

| 生きている値 | `resume 0` | `resume <=1` | `resume 1` | `resume ω` |
|---|---|---|---|---|
| 複製可、`&` の借用 | 可 | 可 | 可 | 可 |
| affine、`&mut` の借用、affine な `var` | 可（Drop） | 可 | 可 | 不可 |
| linear | 不可 | 不可 | 可 | 不可 |

---

## Drop と clone

- **Drop は自動で構造的。** 「Drop の時点と順序」。ユーザーが Drop を定義する構文はない（暗黙に効果が走るのを避ける）。
- **clone は自動で構造的。** 型 `A` が affine で、構成要素（フィールド、再帰的に）がすべて複製可か clone 可能なら、組み込み関数 `clone(&x: A) -> A` が使える。extern の不透明な型（`affine struct File`）は clone できない（必要なら extern に `file_try_clone` を書く）。linear な型は clone できない。
- `clone` は関数呼び出しの形の組み込みで、構文ではない。`&x` を受け取る。

---

## 型・命題・証明との関係（tauto）

- **型・命題・証明の中での変数の出現は使用に数えない。** `theorem t(f: File): P(f)` のように affine の値を命題に書いてよい。これは tauto の消去の規則そのものである。
- カーネル（`check.rs`, `check/core.rs`）は **変えない**。種と再開量は Nib の層（`types.rs`, `rows.rs`, `lin.rs`）で検査し、カーネルは種と再開量のないときと同じ項を受け取る。この検査はプログラムを **より多く拒否する** だけで、受理する項の形は変えない。
- `inductive` の宣言に種を書く必要はない（証明のためのデータは複製可）。実行されるデータで affine が要るのは `struct` / `enum` だけ。
- 依存型の中で affine の値を計算に使う（`Vec(n, File)` の `n` を `File` の値から計算する等）必要はまだない。必要になったら線形な依存型を別に検討する。

---

## 標準ライブラリ

二組ある。どちらも tauto の `std/`（Nib の `std/prelude/`）に **tauto 自身の署名** で置く。affine の std の実装は実行系の組み込み（`Vec` などは配列が要る）で、「`extern`」の extern と同じ署名にする。

### ω の std（shared）

`Text`、`List(A)`、`Option(A)`、`Pair(A, B)` のほかに：

```nib
fn map<A: shared, B: shared, e>(xs: List(A), &f: (A) -> B ! {e}) -> List(B) ! {e}
fn each<A: shared, e>(xs: List(A), &f: (A) -> () ! {e}) -> () ! {e}
fn fold<A: shared, B: shared, e>(xs: List(A), init: B, &f: (B, A) -> B ! {e}) -> B ! {e}
fn fold_once<A, B, e: <=1>(xs: List(A), init: B, &f: (B, A) -> B ! {e}) -> B ! {e}
fn words(t: Text) -> List(Text)
fn concat(a: Text, b: Text) -> Text        // 既存
struct Map(K, V)                            // 永続写像。kind = join(shared, kind K, kind V)
fn map_empty<K, V>() -> Map(K, V)
fn map_get<K: shared, V: shared>(m: Map(K, V), k: K) -> Option(V) where DecEq(K)
fn map_insert<K: shared, V>(m: Map(K, V), k: K, v: V) -> Map(K, V) where DecEq(K)
fn map_entries<K, V>(m: Map(K, V)) -> List(Pair(K, V))
struct Array(A)                             // 読むだけの配列（[`self-host.md`](self-host.md)「配列」）
fn array_of_list<A: shared>(l: List(A)) -> Array(A)
fn array_get<A: shared>(a: Array(A), i: u64) -> Option(A)   // O(1)
fn array_len<A: shared>(a: Array(A)) -> u64
fn array_to_list<A: shared>(a: Array(A)) -> List(A)
```

- `fold` は累積値 `B` が `f` の呼び出しを跨いで生きるので、`B: shared` か `e: <=1` のどちらかが要る。両方を用意し、名前で分ける（書き方は一つの原則：同じ署名を二つ用意しない。`fold` と `fold_once` は署名が違う）。
- `map_get` が `Option(V)` を値で返せるのは `V: shared` のとき。affine な `V` には affine の std の `hashmap_get`（借用を返す）を使う。

### affine の std（Rust と同じコストモデル）

```nib
affine struct Buf {}                                 // 所有された文字列（Rust の String）
affine struct Vec(A) {}
affine struct HashMap(K, V) {}
effect missing: () -> Never resume 0
effect out_of_bounds: () -> Never resume 0

fn text_of(b: Buf) -> Text                           // move、ゼロコピー
fn buf_of(&t: Text) -> Buf                           // 複製
fn buf_clone(&b: Buf) -> Buf
fn buf_each_word<e: <=1>(&s: Buf, &f: (&w: Buf) -> () ! {e}) -> () ! {e}

fn vec_new<A: linear>() -> Vec(A)
fn vec_push<A: linear>(&mut v: Vec(A), x: A) -> ()
fn vec_pop<A: linear>(&mut v: Vec(A)) -> Option(A)
fn vec_len<A: linear>(&v: Vec(A)) -> u64
fn vec_index<A: linear>(&v: Vec(A), i: u64) -> &A ! {out_of_bounds}
fn vec_clear<A>(&mut v: Vec(A)) -> ()                // 要素を捨てる：A は affine まで
fn vec_each<A: linear, e>(&v: Vec(A), &f: (&x: A) -> () ! {e}) -> () ! {e}
fn vec_consume<A, e: <=1>(v: Vec(A), &f: (x: A) -> () ! {e}) -> () ! {e}
fn vec_sort_by<A: linear>(&mut v: Vec(A), &lt: (&a: A, &b: A) -> Bool) -> ()
fn vec_truncate<A>(&mut v: Vec(A), n: u64) -> ()
fn vec_swap<A: linear>(&mut v: Vec(A), i: u64, j: u64) -> () ! {out_of_bounds}

fn hashmap_new<K: linear, V: linear>() -> HashMap(K, V) where DecEq(K), Hash(K)
fn hashmap_get<K: linear, V: linear>(&m: HashMap(K, V), &k: K) -> Option(&V) where DecEq(K), Hash(K)
fn hashmap_index<K: linear, V: linear>(&m: HashMap(K, V), &k: K) -> &V ! {missing} where DecEq(K), Hash(K)
fn hashmap_insert<K: linear, V: linear>(&mut m: HashMap(K, V), k: K, v: V) -> Option(V) where DecEq(K), Hash(K)
fn hashmap_into_vec<K: linear, V: linear>(m: HashMap(K, V)) -> Vec(Pair(K, V))

fn replace<A: linear>(&mut x: A, v: A) -> A          // &mut から move して出す唯一の方法
```

- `<A: linear>` を書くのは「要素を捨てない」関数。`vec_clear` は捨てるので既定の affine。
- `vec_consume` は要素を一つずつ `f` に渡し、残りの要素が `f` の呼び出しを跨いで生きるので `e: <=1`。`vec_each` は借用しか渡さないので `e` は任意。
- std の本体にも「制御フロー線形性（CFL）の規則」が掛かるので、署名は次のようになる：
  - `map`・`each`・`fold` は残りのリスト（と `map` では計算済みの頭）が `f` の呼び出しを跨いで生きるので、`e` が任意なら `A`（と `B`）は `shared`。affine な要素には `fold_once` か `vec_each` を使う。
  - `vec_consume` の `A` は affine まで。`e: <=1` は 0 回（`resume 0` の効果）を含み、そのとき残りの要素が捨てられるので、linear な要素は渡せない。
  - `buf_each_word` は単語ごとに作る `Buf` を `f` の呼び出しを跨いで持つので `e: <=1`。
  - `map_get`・`map_insert` は鍵を `==` で何度も比べるので `K: shared` で、比べるために `where DecEq(K)` を要求する（[`classes.md`](classes.md)「std の鍵の制約」）。
  - `vec_sort_by` は要素を `v` に置いたまま並べ替える（挿入整列）。そのために `vec_swap` が組み込みにある。
- `HashMap(K, V)` の `K` は `where DecEq(K), Hash(K)` を要求する（[`classes.md`](classes.md)「構造的な述語 `PartialEq`・`DecEq`・`Hash`」）。構造的な述語なので、フィールドがすべて比べられる struct / enum は鍵にできる。

### 境界

`text_of` / `buf_of` だけが二つの std をつなぐ。日常のコードは中核を ω の std で書き、資源と性能が要る縁だけを affine の std で書く。

---

## `extern`


```nib
affine struct File {}
affine struct IoError {}

extern {
  fn file_open(&path: Text) -> Result(File, IoError)
  fn file_read_to_buf(&mut f: File, &mut buf: Buf) -> Result(u64, IoError)
  fn io_error_message(&e: IoError) -> Text
}
```

- `extern` の署名（型、種、行、再開量）は **tauto 側の主張** で、`axiom` と同じく信頼の対象。`tauto check` は信頼した extern を公理と同じ一覧に出す。
- `affine struct X {}` を extern の型に使う（フィールドのない構造体。波括弧は省けない：構造体の書き方は一つ）。Drop は Rust の `Drop`。`linear` な extern の型はない（Rust は捨てられるから）。
- Rust の `Result<T, E>` は `Result(T, E)` の値のまま受け渡す（効果にするのは std の `raise` / `catch`、[`rust-backend.md`](rust-backend.md) 「`Result`、`fail` / `raise` / `catch`、`Slice`」）。`Option<&T>` を返す API は `Option(&T)`（[`rust-backend.md`](rust-backend.md) 「view 型」）。`panic` は `Interrupted`（効果ではない）。
- `&mut` の引数は Rust の `&mut`、`&` は `&`、所有は値渡し。複製可な tauto の値は Rust 側で `Rc` か値。
- Drop を行に見せる `affine struct File drop ! {io}` は未決定（「決めたことと未決定」）。

---

## 実行時の意味論

[`semantics.md`](semantics.md) の機械にとって、この仕様はほとんど **静的な制限** で、観測できる振る舞いに現れるのは次だけ。

1. **Drop の時点**（「Drop の時点と順序」）。tauto で定義した型だけなら観測できない。extern の型が入ると Rust の `Drop` が走る時点として観測できる。
2. **動的な所有権検査モード**（`tauto run --check-ownership`、テスト専用）：affine / linear の値を作るたびにトークンを付け、(a) 同じトークンが二度使われたら、(b) linear のトークンが消費されずに消えたら、(c) `ω` の効果で複製される継続の中にトークンがあったら、実行時エラーにする。静的検査の **対照試験** に使う：静的検査を通ったプログラムが動的検査で止まれば、静的検査の誤り。
3. 借用は実行時には **値そのもの**（複製可）か **持ち主への参照**（affine）で、どちらにしても新しい値を作らない。

参照カウントの方式は実装の自由で、仕様ではない。

---

## Lean での証明

### 方針

- `lean/Proto/Nib/Typing.lean`（`HasType sg S Γ t A ρ`）と `Safety.lean`（preservation / progress / type_safety）を **壊さない**。
- 使用の判断 `Lin` は **別の述語** で、「`HasType ∧ Lin` が step で保たれ、トークンの一意性が不変量である」ことを示す。文脈分割型の型システムに書き換えない（`Safety.lean` をやり直すことになり、得るものがない）。
- 借用は「持ち主をセルにする」ことでモデル化する（「借用（`Borrow.lean`、`BorrowStep.lean`、`BorrowSafety.lean`）」）。モデルのセル（`Tm.cell`, `loc`, 状態 `S`）をそのまま使う。
- 種と再開量は `Sig` でなく `OwnSig` に置く。`Sig` と `OwnSig` は同じ番号付けで対応する。

### 種・再開量・トークン・CFL（`Kind.lean`、`Lin.lean`、`Own.lean`）

定義：

```lean
structure OwnSig where                             -- 種と再開量は Sig と別に持つ
  dataKind : Nat → Kind                            --   宣言の種（struct / enum の番号で）
  quant : Eff → Quant                              --   再開量
  tvarKind : Nat → Kind                            --   型変数の境界
  rvarQuant : Nat → Set Quant                      --   行変数の境界
inductive Kind | copy | shared | affine | linear   -- 格子、join
def Ty.kind : OwnSig → Ty → Kind                   -- 「型の種 kind(T)」の通り。型変数は境界
inductive Quant | zero | leOne | one | omega
def Row.quants : Row → Set Quant                   -- 行変数は境界
```

- **トークン**：項 `Tm.fresh (t : Tm)` がトークンを作る。`fresh v`（`v` は値）は `cell v` と同じく状態に新しい場所を取り `loc l` に進む。**トークンとはこの場所 `l` のこと** で、状態 `S` に場所の型を記録し、その型の種で owned / linear を決める。`Value` にトークンのための形はない（`loc l` が値）。affine / linear の種の `con` は、検査器が `fresh (con …)` と読む（プログラムには書かない。`loc`, `run` と同じ run-time 由来の形）。`HasType` は `fresh t : A ↔ t : A`。これで「持ち主は場所」になり、借用はその場所への `brw` / `mbrw` で表せる。
- **move**：owned な場所からの `get` が move で、move した（捨てた）セルはゴーストの集合 `D` に入る。
- **使用の判断 `Lin sg Γκ t`**（`Γκ` は各変数の種の列）：「使用の規則」「関数と閉包」「再開量と制御フロー線形性」の規則の形式化。
  - 変数の種が affine なら `t` の中で高々一度、linear ならちょうど一度（`if` の両腕で同じ回数）現れる。
  - 閉包は所有したものを捕まえない（モデルの関数は shared）。その場で呼ばれる関数（`app (lam ps b) args`、ブロック）は何を使ってもよい。
  - `handle`：腕の自由変数（パターン変数と `k` を除く）はすべて複製可。`k` の種は `quant` から。
  - **CFL**：モデルではブロックの続きは `app (lam ps b) args` の `b` なので、跨いで生きている変数は **`b` に残る自由変数**（`args` を評価する間）と、**`args[i+1..]` と `f` の自由変数**（`args[i]` を評価する間）。`args[i]` の行に `ω` があれば、それらに affine / linear の変数がないこと。`handle` では `return` 腕の自由変数が本体を跨ぐ。
  - CFL の第二の規則（`1` でない再開量の呼び出しを linear な変数が跨がない）は `OwnSig.strict = true` のときの前提。`strict` のもとでは `run` と `info` を使わない。
  - モデルの `var`（`cell`）は複製可な中身だけを持つ。owned なセルを `set` で上書きすることは拒否する（古い値が消えるため）。

定理：

- **T1 `lin_preservation`**：`HasType ∧ Lin` な閉じた状態が step すれば `Lin` のまま。
- **T2 `unique`**：`HasType ∧ Lin` な状態から到達するすべての状態で、owned な場所 `m` の出現数（項と全セルの合計）は高々一。
- **T3 `linear_kept`**：種が linear の場所は、それを消費する step（`Consumes`：その場所の `get`（`match` が owned な値を読む形）か `proj`）以外で消えない。`strict` が要り（`ω` や `0` の継続を捨てる・複製すると linear な値が消える）、`budget` のないプログラムについて述べる（`budget` は打ち切ったときに中の linear な値を捨てる）。
- **T5 `captured_noOwned`**：`perform e vs` が `quant e = ω` の effect で `select` に進むとき、捕まえられるフレーム `E`（`captured`）に owned な場所がない。したがって `k` を二度呼んでも T2 が破れない。T3 のための類似が `captured_noLin`：`1` 以外で再開しうる操作は、linear なものを捕まえない。

難所は `k := (x) => handle { E[x] } …` の step：`E` にトークンがあると `k` を複製したときに二重になるが、`Lin` が `ω` のときそれを禁じている（T5）。`<=1` / `1` のときは `k` が affine / linear な関数で、`Lin` が高々一度 / ちょうど一度の呼び出しを保証する。

### 借用（`Borrow.lean`、`BorrowStep.lean`、`BorrowSafety.lean`）

- 所有された affine / linear の `let` を、モデルでは `cell` にする（持ち主をセルにする）。move は owned なセルからの `get`。`Moves l t` は「`t` の次の step がセル `l` から move する」。
- 借用の項は `Tm.brw`, `Tm.mbrw`（`&p`, `&mut p`）と、借用越しの読み書き `Tm.field`（`field i (brw (loc l))`）、`Tm.write`（`write (mbrw (loc l)) v`）。借用の型は `Ty.brw`, `Ty.mbrw` で（Nib の型にはないが、`cell(A)` と同じくモデルの型にはある）、`Ty.Bv`（値が借用でありうる型）で区別する。
- `Tm.bor a t` は `t` が `a` を借用する回数（`brw` / `mbrw` の下の出現）。`occ` は `brw` / `mbrw` の下を数えない（持ち主のセルで数える）。
- 「借用」の規則は `Lin` と別の検査 `BLin` にする（`Lin` の証明が借用に依存しないため）。借用は引数か読み書きの対象にだけ現れ（`Bare`）、部分は左から右に走り、先の部分が所有するものを後の部分は借用せず、借用を保つ部分が借用するものを後の部分は所有しない（`Seq`, `Then`）。閉包、打ち切られうる `budget` の本体、捕まえられうる継続は外の借用を持たない（`Sealed`）。本体か `return` 腕が外を借用する `handle` の `k` は pinned で、腕の中でその場で呼ぶだけ（「借用と効果」）。
- `Sealed` は「自分が所有するもの」と「誰も所有しないもの」（`Fr`）の借用を許す。step で持ち主が消えた場所（値が捨てられた、関数が返った）は `Fr` に入り、`Fr` は step で増える。
- 腕が扱う操作の結果型は借用でない（`BClause` の前提 `¬ R.Bv`）。効果の署名の結果型には `&` を書けないので、検査器はこれを満たす。継続 `k` の穴（操作の答え）を引数の位置に置けるのはこのため。
- 不変条件 `BInv`：T2 の `Uniq` と `BLin`、セルの中身が `BLin` を通り借用でない（`StoreB`）、move したセルと生きたセルが持つ場所を誰も借用しない（`Lent`）。

**T4 `borrow_safety` / `borrow_safety_run`**：検査を通るプログラムから到達するすべての状態で、項は `BLin` を通り、move したセルを項は使わず借用せず、生きたセルも持たず、そのセルに触れる step（`get`, `set`, 借用越しの `field` / `write`、`Touches`）はない。owned なセルからの move は、項の何もそのセルを借用していないときにだけ起こる。`progress` は「move したセルを読む」場合を **持たない**（それが起きないことが T4）。

### 継続の複製（`Duplicate.lean`）

`ω` の操作の中断点で捕まるフレームについて、`captured_dup`：継続は所有されたものを持たず（T5）、フレームが穴の左に持つ値はすべて `Held`（複製可の型で、`&mut` の型でない）。したがって複製されるのは複製可の値と `&` だけで、`&mut p` は入らない。

モデルでは `&mut` の型の種が `shared` なので、`Ty.Mv`（`Kind.lean`）で `&mut` の型を区別し、`Held` に `¬ A.Mv` を、`Inst.Fits` に「型変数に代入する型は `Mv` でない」を置く（「制御フロー線形性（CFL）の規則」が `&mut` を `ω` の効果の左に持つことを禁じるのと同じ）。

### 直接アームの借用捕捉（`Borrow.lean` の `Frozen`）

[`rust-backend.md`](rust-backend.md)「`direct` 操作」の規則（腕の捕獲）の通り、直接アームは `handle` の外の借用を使ってよい（借用閉包）。一方、`k` を値として残す（pin する）アームは、外の借用を持つ中断点を捕まえてはならない。`BLin.handle`・`handleRet`・`select` は `Frozen` を要求し、pin するアームでは「本体が借りているものを、アームが `k` 以外で使わない」。`BClause` の封印の項は `pin = false` のときだけ要る。T4 の捕捉の段（`BorrowSafety.lean`）は `Frozen` を穴の位置（`Frozen.chole`）とアームの尾（`Frozen.tail`）で保つ。「借用と効果」の、外を借用する `handle` の `k` の規則（`cases/lin/borrows.eure` の `continuation-with-borrow-escapes`）のモデル側の形。

### ブロックの終わりの解放（`Free.lean`）

解放のための step はない。解放は持ち主のセルからの move で、値を捨てるだけなので、T4 がすでに扱っている（move したセルはゴーストの集合に入り、あとの step は触れず、move は何も借用していないときにだけ起こる）。`Tm.scoped A R init body` は `body` のあとに持ち主の `get` を置いた owned な `let`。`scoped_lin`：本体が持ち主を自分で使わず、`ω` を再開しうる操作をしない（quiet）なら使用検査を通る。`scoped_blin`：本体の値が借用でないなら借用検査を通る。`scoped_borrow_rejected`：本体が持ち主の借用を返すなら通らない（解放のあとに借用が残るため）。

### view（`View.lean`、`ViewExample.lean`）

**借用を返す extern。** `&T -> &U` や `&mut T -> &mut U` の extern（引数の借用の view を返す）は、prim `reborrow` / `reborrowMut` で表す。呼び出しは受け取った借用をそのまま返す。型は `fn [&T] &T`、`fn [&mut T] &mut T`。呼び出しの結果は借用なので `Bare` ではない。`BLin` は `viewApp` の規則で view の呼び出しを、引数が準備できている（値か変数）ときにだけ通す（評価の途中の借用を step が動かすことを除くため）。`BHole.bare` と `CHole.bare` は「穴が `Bare` なら置き換えた後も `Bare`」という含意で、穴は借用のままでもよい。そのとき穴は、すでに借りていたものしか借りない（`BHole.nb`）。

**宣言した view 関数。** top に宣言した関数のうち、引数が借用か `bool` で、結果が借用、本体がその借用の引数のどれかを選ぶもの（`ViewDecl ps B`：本体は `ViewBody`、結果の型は選ばれた引数の型）を view 関数と呼ぶ。本体は、引数 `var j`、`bool` の引数での `if`（`ite (var c) t f`）、先に宣言した（`d' < d`、自己再帰も相互再帰もない）view 関数の、自分の引数を渡した呼び出し（`ViewPass`：引数は一対一で、型が合う）のどれかである。結果は引数のどれかの借用で、どれかは署名でなく本体が決めるが、検査は「結果はすべての借用の引数から派生する」（「関数と閉包」の「結果」）と数える：呼び出しの `Tm.bor` は引数の借用の和である。

- 呼び出しは prim `vcall d ps`（`Step.vcall`：宣言 `d` の本体を引数で走らせて（`ViewRun`）`i` 番目の引数を選び、それを返す）。選んだ引数の型は結果の型（`ViewRun.ty`）なので、型保存は分岐や呼び出しを通っても同じ形で閉じる。進行は、本体の形（`ViewBody.run`）と、`bool` の引数が `bool` の値であることから出る。`Prim.Ok` は宣言があること、型と行が型変数を持たないことを要る。
- `Prim.IsView`（`reborrow`・`reborrowMut`・`vcall`）の呼び出しは `Bare` でない（`vcall_not_bare`）。`BLin.viewApp` が準備できた引数でだけ通す（`vcall_blin`、借用と `bool` の値の列は互いに衝突しない：`Seq.viewVals`）。
- view 関数は呼ぶだけで、値としては持てない：`BLin.ref` は `¬ ViewDef` を要る（`view_ref_not_blin`）。そうでないと変数や閉包越しの呼び出しが、借用でない結果と数えられる。
- 定義の検査 `DefsB` は view 関数を除く（検査は `ViewDecl`）。`DefsOk`・`DefsLin` は他の定義と同じく要る。
- T4：`bstep` の `vcall` の場合は、結果が引数のどれかで、その借用は呼び出しの借用の部分、その占有は呼び出しの占有の部分なので、`Lent`・`Uniq`・`StoreB` は reborrow の場合と同じ形で閉じる。
- 例：`ViewExample.lean` の `second(a, b) = b`、`choose(c, a, b) = if c { a } else { b }`、`chooseOf(a, b, c) = choose(c, a, b)`。

モデルにまだないもの：field の経路の view（借用の値は cell 全体 `brw (loc l)` だけで、cell の中の部分の借用を表せない）、view への `match`（核に `match` の項がない）、`&` と `&mut` の排他（`Tm.bor` は二つを区別しない。区別するには `Tm.bor` を共有と排他に分け、`ren`・`subst`・`inst` と T4 の `Lent` を通す必要がある）。モデルの引数は A 正規形。

### 書かないもの

- 参照カウント・Drop の実行時の意味（メモリ）。モデルは捨てるだけ。
- extern。モデルでは `affine struct X` はフィールドのない `con` に `fresh` が付いたもの。
- NLL、lifetime、第一級の参照。

### ファイル

```text
lean/Proto/Nib/Kind.lean         Kind, Ty.kind, Quant, Row.quants, Ty.Mv
lean/Proto/Nib/Lin.lean          使用の判断 Lin
lean/Proto/Nib/Own.lean          トークン、T1–T3, T5
lean/Proto/Nib/Borrow.lean       brw/mbrw/field/write、借用の検査 BLin、Frozen
lean/Proto/Nib/BorrowStep.lean   T4 の不変条件、フレームの外の step
lean/Proto/Nib/BorrowSafety.lean 捕まえた継続、bstep、T4
lean/Proto/Nib/Duplicate.lean    継続の複製（captured_dup）
lean/Proto/Nib/Free.lean         ブロックの終わりの解放
lean/Proto/Nib/View.lean         view を返す呼び出し、宣言した view 関数
lean/Proto/Nib/ViewExample.lean  宣言した view 関数の例
lean/Proto/Nib/Examples.lean     受け入れ試験のうち Lean で書けるもの（askSig に対する OwnSig を含む）
```

`Typing.lean` と `Safety.lean` には `fresh` と借用の項、それに伴う腕だけが入る。

---

## 決めたことと未決定

### 決めたこと（根拠つき）

| 決定 | 代わりに退けたもの | 根拠 |
|---|---|---|
| 種は型の性質 | 束縛子ごとに量を書く | Rust の型と一対一になり、コンテナの要素や「捨ててよいか」を型で言える。カーネルは消去（0 / ω）だけ持てばよい |
| Rust の資源は affine、linear はオプトイン | すべて linear | abort（`resume 0`）の下で「ちょうど一度」は守れない。affine なら捨ててよく、Rust の Drop が後始末する |
| 既定の再開量は `<=1`、multi-shot は `resume ω` と明示 | 既定 ω | affine を跨げる効果が既定になり、Rust の資源を普通に使える。multi-shot はまれで、明示する価値がある |
| 二級の借用、字句的な凍結 | 第一級の参照 + lifetime + NLL | 検査が構文木を一度歩くだけで済み、`Safety.lean` の流儀（構文的 progress/preservation）で証明できる。第一級の参照と効果（継続の捕獲）の組み合わせは健全性の論証が大きくなる |
| `&A ≡ A`（複製可） | Rust の `*r` | ジェネリックな `-> &A` が複製可な `A` でそのまま使える |
| `&mut` は `var` だけ | `let mut` の追加 | 「可変なものは `var`」の一つの書き方 |
| 自動の構造的 Drop / clone、ユーザー定義なし | 明示 Drop、ユーザー定義 Drop | 明示は資源のコードを 2〜3 割増やす。ユーザー定義は暗黙に効果を走らせる |
| 腕の自由変数は複製可 | 腕ごとの使用解析 | 腕は何度も走る。状態はパラメータか `var` で持ち回せる（「腕と `k`」） |
| 行変数の既定は任意、`<e: <=1>` で締める | 既定 `<=1` | `each(xs, x => perform choose())` のような ω のコードが注釈なしで書ける |
| 借用閉包は二級 | 閉包の lifetime | 標準ライブラリの高階関数が `&f` で受け取れば足りる |
| `fold` と `fold_once` を分ける | 一つの `fold` | 累積値を跨ぐ効果の量を署名に出す必要がある。署名が違うので「書き方は一つ」に反しない |
| 参照の循環による漏れは許す | 「セルを捕まえた閉包はセルに入れられない」規則 | その規則は関数型に「セルを捕まえている」印を要し、署名に漏れる。漏れは健全性に関係しない。lint の候補として残す |
| `Lin` を `HasType` と別の述語にする | 文脈分割型の型システムに書き換える | `Safety.lean` を壊さず、トークンの一意性という一つの不変量に証明が集まる |
| 外を借用する `handle` の `k` はその場で呼ぶだけ | `k` の型に借用の印を付ける、外を借用する本体では `ω` だけを禁じる | 印は関数型に lifetime を持ち込み署名に漏れる。`<=1` の `k` も値として外に出せるので `ω` だけの禁止では足りない。その場で呼ぶなら継続は腕の間に使い切られ、借用は持ち主より長く生きない |
| 持ち主をセルにして借用をモデル化 | 代入意味論で借用を値の複製にする | 複製はトークンを二重にし、`&mut` の書き込みが持ち主に届かない |

### 未決定

1. `no shared`（関数・モジュールに RC が走らないことを宣言で検査させる）を入れるか。
2. `affine struct File drop ! {io}`（Drop の効果を行に見せる）を入れるか。
3. `Decimal` の種（`copy` としたが、実装が任意精度なら `shared`）。実装に合わせる。
4. `let &x = f(&v)` の凍結を「形状を変える更新だけ禁止」に緩めるか。書き味の例が出てから。
5. 評価順の move の衝突（`map_insert(&mut m, w, map_get(&m, &w) + 1)`）を two-phase borrow で通すか。two-phase borrow はないので、衝突はエラーになり、`let` で先に読む。
