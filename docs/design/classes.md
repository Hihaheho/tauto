# 型クラス

Nib（したがって tauto）の **型クラス** の仕様です。構造的な述語（`PartialEq`・`DecEq`・`Hash`）、制限付きの
利用者定義クラス、高階のクラス、tauto での法則の証明を扱います。

**決まっていないことは「未決定」の節にだけ書きます。**それ以外はすべて今の仕様です。
設計を変えるときは、この文書を先に直します。

正の順序は [`nib.md`](nib.md) と同じです。この文書は [`semantics.md`](semantics.md)
を補う仕様で、実装（`crates/`）が正ではありません。食い違えば実装を直します。所有権の語（種、借用、再開量、
CFL）は [`ownership.md`](ownership.md)（以下 OWN）、Rust バックエンドの語（層、
NIR、`tauto bind`）は [`rust-backend.md`](rust-backend.md)（以下 RB）のものです。

---

## 要約

1. 型クラスを入れる。新しい概念は **クラス**、**インスタンス**、**制約** の三つだけ。
2. 制約は署名の末尾に `where C(T), …` と書く。種は `<A: Shared>` に書き、制約と混ぜない。
3. **構造的な述語** `PartialEq`・`DecEq`・`Hash` は組み込みのクラスで、インスタンスは型の構造から自動で決まる。利用者はインスタンスを書けない（`clone` と同じ扱い）。
4. `==` と `!=` は `PartialEq(T)` を要求する。関数・`Vec`・`HashMap` は `PartialEq` でないので、`f == f` は実行時に止まるのでなく型エラーになる。`==` の被演算子は借用として読む（move しない）。
5. `Float` は `PartialEq` だが `DecEq` ではない（NaN）。`HashMap` の鍵は `DecEq` と `Hash` を要求する。`DecEq(T)` が成り立てば `PartialEq(T)` も成り立つ。
6. 利用者定義のクラスは `class C(A: Type) { fn … theorem … }`、インスタンスは `instance<…> C(H(…)) where … { … }`。
7. パラメータは型付きの列で、後ろのパラメータの型は前のパラメータに依存できる。**インスタンスの選択パターンはプログラム全体で重ならない**。孤児・局所的なインスタンスはない。単一の型パラメータについては、(クラス, 型の頭) ごとに一つ。
8. メソッドはクラス名で修飾して呼ぶ：`Ord::compare(&a, &b)`。オーバーロードではなく、制約付きの一つのジェネリックな関数。
9. 解決は、型の位置では型の頭、項の位置では第一階の構成子・リテラルのパターンで一つを選び、その引数を当てる。後戻りも優先度もない。項のパラメータ列と選択パターンの制限は下記「型と項のパラメータ列」を参照。
10. 既定メソッド、スーパークラス、関連型、演算子の多重定義、メソッド呼び出しの構文（`a.compare(b)`）、`derive` は入れない。
11. **高階のクラス**：クラスのパラメータに型構成子を取れる（`class Functor(F: (Shared) -> Shared)`）。型構成子の変数の適用 `F(A)` は、型の適用と **末尾の引数で構造的に** 合わせる（第一階）。部分適用は末尾の引数だけを残す形（`Pair(A)`）。
12. **単一型パラメータの Nib 経路での展開**：制約は「メソッドの数だけ関数の引数を足す」、メソッドの呼び出しは「その引数を呼ぶ」、インスタンスは「名前の付いた関数」に展開する。辞書はメソッドごとの関数引数として表す。
13. 辞書の引数は shared な関数の値（借用ではない）。CFL を跨げ、閉包に捕まえても借用閉包にならない。
14. 展開後のプログラムを、クラスを知らない `types.rs`・`rows.rs`・`lin.rs`・カーネル（`check.rs`、`check/core.rs`）がそのまま検査する。**カーネルは変えない。** 解決の誤りは展開後の検査が拒否する。
15. メソッドが自分のジェネリクスを持つとき（`map<A, B>`）、辞書の引数は多相な関数になる。Nib の型検査は、展開が作るこの形に限って多相な引数を扱う（利用者は書けない）。カーネルでは普通の Π。
16. **tauto では法則の証明が要る。** クラスは `theorem` の項目（法則）で命題を持ち、インスタンスは各法則の証明を書く。証明のないインスタンスは `tauto run` では動くが、`tauto check` では **incomplete**（穴と同じ扱い）で、`std/` と `meta/` では `tauto lint` が拒否する。
17. 構造的な述語の法則（`DecEq` なら `(a == b) = true ↔ Eq(T, a, b)`）は、検査済みの `inductive` について **生成して検査する**（no-confusion と同じ作り）。
18. Rust バックエンドは、高階でないクラスを生成したクレートの trait と impl に、高階のクラスの型構成子の変数を単相化に写す。構造的な述語は `#[derive(PartialEq, Eq, Hash)]` と境界になる。

---

## 型と項のパラメータ列

`class C(A: Type, key: A) { … }` のように、パラメータは名前と型の列を取る。
各型は、そのパラメータより前の名前を参照できる。先頭を `Type` に固定せず、
`class C(key: Nat)` や、複数の型パラメータも同じ規則で読む。
`instance<A, key: A> C(A, key)` と `where C(A, key)` は列全体を同じ順序で指定する。
関数の項ジェネリクスと同じく、これは既存の Π の引数であり、カーネルの規則は増やさない。

メソッド呼び出しの省略されたパラメータは、通常の引数の型と期待される結果の型から
第一階で決まるものだけである。決まらない項を、周囲の `where` が一つだからという理由で
選ばない。全引数を書いた呼び出しでは辞書も明示する。クラスの引数だけを書いて辞書だけ
省略する専用構文はない。

パラメータに渡せる項と、インスタンスを選ぶパターンは別である。
インスタンス宣言の項の位置は、リテラル・ジェネリクス・第一階の構成子の適用に限る。
関数適用、λ、場合分けなどを選択パターンとして評価する探索はしない。
呼び出し側で既知の引数は弱頭正規化してから照合する。

選択の比較は表示文字列に依存しない。

- 型の位置では型の外側の頭を使う。型引数を変えただけの instance は重複である。
- 項の構成子は宣言の同一性と明示フィールドの列を使う。構成子の暗黙パラメータは、
  ソースで明示されていても省略されていても選択の比較から除く。
- 自然数リテラルと `Zero` / `Succ` の表現は同じ自然数として比較する。
- テキストは省略されていない UTF-8 の内容で比較する。リテラルと、選択された Text の
  構成子に UTF-8 バイト列を渡した表現を同一に扱う。
- ジェネリクスはワイルドカードとして重なりを検査する。繰り返された変数を独立に扱う
  保守的な検査なので、重ならないことを証明できない宣言は拒否する。優先順位は付けない。

辞書の前提を解決する途中で同じ制約に戻る循環はエラーにする。
増大し続ける制約によるホストのスタック枯渇も避けるため、現在の実装は辞書解決の
入れ子 128 段を上限とし、超過を明示的なエラーにする。上限超過を解決成功とは扱わない。

構成子の暗黙引数を選択の比較から除くことは、型検査から除くことではない。
選んだ辞書を全引数付きの項として書き出し、その項と型をカーネルが検査する。
同じ表示名を持つ別の構成子は別の宣言として扱う。

複数または項パラメータを持つクラスの実行経路は、検査済みのクラスを通常の帰納的辞書と
透明な関数に展開してから、依存型の消去を通して Nib に渡す。
後述の単一型パラメータ向け Nib 展開とは別の経路であり、未検査の値を Nib の型として
埋め込んではならない。自己ホストの単相 Nib 検査器へ未展開の項付き制約を渡す場合は、
追加引数を捨てて受理せず、未対応として拒否する。

生成する辞書の universe は `Type` に固定しない。パラメータを文脈に入れ、各メソッドの
関数型が属する sort を既存の型検査器で求め、その上限を辞書の sort とする。
たとえば `Env -> Type` のフィールドを持つ辞書は `Type1` に属する。
メソッドの結果型そのものを大きく読み替えるわけではなく、`Type` を返すという署名に
`Type1` の値を返す実装は拒否する。利用者が書いた帰納型の明示 sort も変更しない。
法則の辞書についても、生成したフィールドを同じ規則で検査する。
高い sort に値を返す辞書の射影には、既存のレベル付き recursor を選ぶ。
この選択も通常の large-elimination 検査を通り、カーネルの universe 規則は緩めない。
型を返すメソッドに後続引数の型が依存する場合、通常の引数から制約全体が既知になった
辞書を先に解決してから、その後続引数を検査する。未知のクラス引数を instance 探索で
推測する規則は追加しない。

この検査済み辞書経路の現在の実装範囲は、純粋で、メソッド固有のジェネリクスを持たない
メソッドである。効果・高階の種・メソッド固有の多相性を扱う単一型パラメータ向け
Nib 経路が、そのまま項付きクラスに拡張されたわけではない。
自己ホストの source からの完全な辞書展開・依存型消去も、この経路とは区別する。

---

## 用語

| 語 | 意味 |
|---|---|
| クラス | 型（または型構成子）について、名前の付いたメソッドの署名と法則の組。`class Ord(A: Type) { … }` |
| インスタンス | クラスの、ある型の頭についての実装。`instance Ord(i64) { … }` |
| 制約 | `C(T)`。「`T` について `C` のインスタンスがある」。`where` に書く |
| 型の頭 | 型の外側のコンストラクタ。`List(Pair(i64, Text))` の頭は `List`。`i64` の頭は `i64` |
| 構造的な述語 | `PartialEq`・`DecEq`・`Hash`。インスタンスが型の構造から決まる組み込みのクラス |
| 利用者定義のクラス | `class` で宣言したクラス。std のクラス（`Ord`、`ToText`）もこちら |
| 高階のクラス | パラメータが型構成子のクラス。`Functor<F: (Shared) -> Shared>` |
| 型構成子の変数 | `<F: (k₁) -> k₂>` で宣言した、型を一つ受け取って型を返す変数 |
| 辞書の引数 | 展開で足される、メソッドごとの関数の引数。名前は `C::m@T` の形で、利用者は書けない |
| 解決 | 制約を満たすインスタンス（または `where` の仮定）を一つに決めること |
| 展開 | クラス・インスタンス・制約を、辞書の引数を足した普通の関数と呼び出しに書き換えること |
| 法則 | クラスに書く命題。`theorem trans<…>(…): …`。tauto でインスタンスが証明する |
| tote | `Tauto.eure` の単位（RB と同じ） |

---

## 構文

以下の `C(T)` の記法と型変数だけの制約は、単一型パラメータ向け Nib 経路を述べる。
型と項の列を持つ検査済み辞書経路では、前節の列全体と依存型の規則を使う。

### 制約 `where`

```nib
fn HashMap::get<K: Linear, V: Linear>(&m: HashMap(K, V), &k: K): Option(&V) where DecEq(K), Hash(K)
fn max<A: Shared>(a: A, b: A): A where Ord(A) { … }
theorem insert_sorted<A>(x: A, xs: List(A), h: Sorted(A, xs)): Sorted(A, insert(x, xs)) where Ord(A) { … }
```

- `where` は署名の末尾（結果の型と効果の行の後、本体の前）に一度だけ書ける。本体のない宣言（`extern` の関数、クラスのメソッドの署名）では行の終わり。
- 制約は `C(T)` を `,` で並べる。`C` はクラスの名前、`T` は **その宣言のジェネリクスで宣言した型変数か型構成子の変数**。`where Ord(List(A))`、`where Ord(i64)` は書けない（`"error: where constrains only generics of f"`）。
- 同じ制約を二度書くのはエラー（`"error: Ord(A) is written twice"`）。
- 制約の順序に意味はない。`tauto fmt` は書かれた順を保つ。
- `<K: Shared, Hash>` や `<K: shared + Hash>` の形は **入れない**。`<…>` の中の `,` はジェネリクスの区切りで、tauto では `<n: Nat>` の `:` の右は型を表すので、クラスの名前と紛れる。

### クラス

```nib
class Ord(A: Linear) {
  fn compare(&a: A, &b: A): Ordering
  theorem equal_iff<a: A, b: A>(): Iff(Ord::compare(a, b) = Equal, a = b)
  theorem swap<a: A, b: A>(): Iff(Ord::compare(a, b) = Less, Ord::compare(b, a) = Greater)
  theorem trans<a: A, b: A, c: A>(h1: Ord::compare(a, b) = Less, h2: Ord::compare(b, c) = Less): Ord::compare(a, c) = Less
}
```

- `class C(P: Type) { 項目… }` は単一型パラメータの場合。型と項の列は次節のとおり。`(A: Type)`、`(A: Shared)` のように種の上限を持てる（`Type` は既定の affine、OWN「型の種 kind(T)」）。高階なら `(F: (k₁) -> k₂)`（「高階のクラス」）。
- 項目は `fn` の署名（本体なし）と `theorem`（法則。「法則（tauto）」）。法則のための専用の語は持たず、トップレベルの定理と同じ `theorem` を使う。メソッドが一つもないクラスは書ける（法則だけのクラス）。
- メソッドの署名は普通の `fn` の署名と同じ。自分のジェネリクスを持てる（「メソッドのジェネリクス」）。効果の行を書ける（「効果と再開量」）。`where` は書けない。
- メソッドの署名は、クラスのパラメータを引数の型か結果の型に含むこと（`"error: Ord::m does not mention A"`）。
- クラスの名前は型・モジュールと同じ名前の空間に入る。型・モジュール・クラスで同じ名前は使えない（`"error: Ord is already a type"`）。名前の空間の規則は RB「名前空間」に従う。
- クラスの中のメソッドの参照は、本体の外と同じく `Ord::compare` と修飾する（書き方は一つ）。

### インスタンス

```nib
instance Ord(i64) {                       // std。組み込みの型なので法則は信頼（「組み込みの型と extern のインスタンス」）
  fn compare(&a: i64, &b: i64): Ordering {
    if a < b { Less } else if a == b { Equal } else { Greater }
  }
}

instance<A> Ord(List(A)) where Ord(A) {
  fn compare(&a: List(A), &b: List(A)): Ordering { … }
  …
}
```

- `instance [<ジェネリクス>] C(頭) [where …] { 項目… }`。
- 頭は次のどれか：引数のない型（`i64`、`Text`、`Point`）、型コンストラクタを **相異なるジェネリクスの型変数** に適用したもの（`List(A)`、`Pair(A, B)`）、相異なる二つの型変数の直積 `A × B`、高階のクラスなら型コンストラクタそのものか、末尾以外の引数を相異なる型変数に適用したもの（`List`、`Pair(A)`、「部分適用」）。`Pair(A, A)`、`List(i64)`、`A`、`A | B`、`@a T`、関数型は頭にならない（`"error: an instance head applies a type to distinct generics"`）。
- 直積 `A × B` の頭は、名前で書いた `Pair(A, B)` とは別の頭 `Prod` である。三つ以上の直積 `A × B × C` には、`A` を最初の要素、`B` を残りの直積 `B × C` として当たる。
- ジェネリクスはすべて頭に現れること。`where` はそのジェネリクスにだけかかる。
- クラスのすべてのメソッドを、署名のパラメータを頭で置き換えた署名で定義する。署名は書き写す（短さより明示性）。検査は「書いた署名がクラスの署名の置き換えと同値であること」（効果の行だけは 「効果と再開量」の通り小さくてよい）。
- 法則の項目は 「法則（tauto）」。
- インスタンスの中のメソッドの定義は、他の関数からは名前で呼べない。呼ぶのはいつも `C::m(…)`。

### extern のインスタンス

```nib
extern {
  fn regex_new(&pattern: Text): Regex ! {regex_error}
  instance ToText(Regex)
  instance PartialEq(Regex)
}
```

- `extern { … }` の中に `instance C(頭)` を本体なしで書ける。意味は「このインスタンスは外の実装が与える」で、`axiom` と同じく **信頼の対象**。`tauto check` は信頼した extern の一覧に出す。
- 構造的な述語（`PartialEq`、`DecEq`、`Hash`）は利用者がインスタンスを書けないが、**extern の不透明な型にだけは** `extern` の中で主張できる（「extern の不透明な型」）。
- 法則は証明されない。extern のインスタンスの法則は信頼の一覧に出る（「組み込みの型と extern のインスタンス」）。
- どの外の実装に対応するかは、extern の関数と同じく `Tauto.eure` の `rust` 節が決める（RB「中立な `extern` と `Tauto.eure` の `rust` 節」）。

### メソッドの呼び出し

```nib
Ord::compare(&x, &y)
ToText::to_text(&rows)
Functor::map(xs, &(x: i64) => x + 1)
```

- `C::m(引数…)` だけ。`compare(&x, &y)`、`x.compare(&y)` は書けない。`use` で修飾を省く仕組みは入れない（RB「名前空間」）。
- クラスのパラメータは、暗黙引数と同じく **引数と期待される型からの第一階のマッチング** で決まる（tauto の暗黙引数は、宣言のジェネリクスと帰納型のパラメータで、明示した引数（関数は最後）、次に期待される型との第一階のマッチングで決まる。ただし結果の型が明示した引数に依らないときは、期待される型とのマッチングを先に行う。引数の型が期待される型と簡約して初めて一致するとき（`walk(acc, Cons(a, t))` と `walk(dbl(acc), t)`）、引数から先に決めると別の値に決まってしまうからである。先に決めた値に引数が合わなければ、元の順で決め直す。精密化した項はすべての引数を書き出すので、カーネルは暗黙引数を見ない）。決まらなければエラー（`"error: the type of A in Ord::compare is not determined: annotate an argument"`）。
- メソッドの値を呼ばずに使う（`&Ord::compare` を `Vec::sort_by` に渡す）のは書ける。そのとき `A` は期待される関数型から決まる。

### キーワード

予約語の一覧は [`syntax.md`](syntax.md)「予約語」。

`class`、`instance`、`where` は予約語で、名前には使えない。予約語は綴りだけで決まり、先読みで語になる場合はない。

---

## 構造的な述語 `PartialEq`・`DecEq`・`Hash`

### 何か

三つとも組み込みのクラスで、**メソッドを持たず**、インスタンスは型の構造から自動で決まる。利用者は `instance PartialEq(…)` を書けない（`"error: PartialEq is structural and has no instances to write"`。extern の不透明な型を除く、「extern の不透明な型」）。`clone` と Drop を構造的・自動にしたのと同じ理由（OWN「Drop と clone」）：同じ型の値の比べ方が二通りあると、読み手がその場で確かめられない。

| 述語 | 何を許すか | 意味（tauto で法則になるもの） |
| `PartialEq(T)` | `a == b`、`a != b` | `==` は対称で推移的 |
| `DecEq(T)` | `PartialEq(T)` と同じこと。`HashMap` の鍵の条件の一つ | `(a == b) = true` は `Eq(T, a, b)` と同値（したがって反射的でもある） |
| `Hash(T)` | `HashMap` の鍵の条件の一つ | `a == b` なら組み込みのハッシュも等しい |

`DecEq` の `Dec` は **decidable（決定可能）** で、「命題の等しさ `Eq(T, a, b)` を、プログラムが `Bool` として計算できる」ことを言う。`Eq` はカーネルの prelude の命題の等しさ `Eq(A, x, y)` の名前なので使わない。

### 規則

```text
PartialEq(i32 … u64, Bool, Text, Buf, Decimal, Float, (), Never)       成り立つ
DecEq(i32 … u64, Bool, Text, Buf, (), Never)                            成り立つ
Hash(i32 … u64, Bool, Text, Buf, (), Never)                             成り立つ
DecEq(Float)、Hash(Float)                                               成り立たない（NaN が自分と等しくない）
DecEq(Decimal)、Hash(Decimal)                                           未決定（「未決定」の節）

P(D(T₁, …, Tₙ))  D は struct / enum、P は三つのどれか
   = D の各フィールドの型（Tᵢ を代入したもの）について P が成り立つ
     再帰的な型は、自分への出現を成り立つと仮定して判定する（最大不動点）
P(@a T) = P(T)
P(A | B) = P(A) ∧ P(B)
P(関数型)、P(Vec(A))、P(HashMap(K, V))、P(Info(T))                      成り立たない
P(型変数 A) = where に P(A) があるとき。DecEq(A) が where にあれば PartialEq(A) も成り立つ
P(extern の不透明な型 X) = extern に `instance P(X)` があるとき（「extern の不透明な型」）
DecEq(T) が成り立つなら PartialEq(T) も成り立つ（すべての T について。規則の形から従う）
```

- struct / enum の宣言に「`PartialEq` にしない」という印はない。構造から決まり、緩めることも締めることもしない。
- 種と同じく、`types.rs` の `structural(P, &Ty) -> bool` が判定する（OWN「型の種 kind(T)」の `kind_of` と同じ形の再帰）。

### `==` と `!=`

- `a == b` は `a` と `b` が同じ型 `T` を持ち、`PartialEq(T)` が成り立つときだけ型が付く。成り立たなければ `"error: == needs PartialEq((i64) -> i64)"`（型を `types.rs` の表示で出す）。型変数なら `"error: == needs PartialEq(A): add where PartialEq(A)"`。
- **被演算子は借用として読む。** `lin.rs` は `==` の被演算子を「値として使う」（OWN「束縛の使用」）に数えず、`&x` と同じ扱いにする。affine な値を比べても消費しない。借用の変数（`&x: A`）どうしも比べられる。
- 実行時の意味は `eval.rs` の `equal` のまま（構造的）。この節の規則は、型の付いた `==` で `equal` が `cannot compare …` に至らないことを保証する（「`==` の進行」の補題）。
- `Float` の `==` は IEEE 754 の比較（`NaN == NaN` は `false`）。`Float` を含む struct の `==` もフィールドごとにそれで比べる。
- `<`・`>`・`<=`・`>=` は数にだけ使え、クラスにしない。順序は `Ord`（「std にあるもの」）。

### extern の不透明な型

`extern { affine type Regex }`（extern の型、OWN「`extern`」）は構造が見えないので、三つの述語は成り立たない。extern の中で `instance PartialEq(Regex)`、`instance DecEq(Regex)`、`instance Hash(Regex)` と主張できる。これは信頼で、`tauto check` の一覧に出る。`DecEq` を主張するなら `PartialEq` も主張すること（`"error: DecEq(Regex) is claimed without PartialEq(Regex)"`）。Rust バックエンドはこの主張を Rust の型の境界として使うので、Rust 側に実装がなければ rustc が拒否する（「Rust バックエンド」）。

### std の鍵の制約

```nib
// std/prelude/Shared.taut
fn Map::get<K: Shared, V: Shared>(m: Map(K, V), k: K): Option(V) where DecEq(K)
fn Map::insert<K: Shared, V>(m: Map(K, V), k: K, v: V): Map(K, V) where DecEq(K)
// Map::find、Map::without も同じ

// std/prelude/Affine.taut
fn HashMap::new<K: Linear, V: Linear>(): HashMap(K, V) where DecEq(K), Hash(K)
fn HashMap::get<K: Linear, V: Linear>(&m: HashMap(K, V), &k: K): Option(&V) where DecEq(K), Hash(K)
fn HashMap::index<K: Linear, V: Linear>(&m: HashMap(K, V), &k: K): &V ! {missing} where DecEq(K), Hash(K)
fn HashMap::insert<K: Linear, V: Linear>(&mut m: HashMap(K, V), k: K, v: V): Option(V) where DecEq(K), Hash(K)
fn HashMap::into_vec<K: Linear, V: Linear>(m: HashMap(K, V)): Vec(Pair(K, V))
```

- `Map` の鍵が `PartialEq` でなく `DecEq` なのは、`Float` を鍵にすると `NaN` の鍵が取り出せなくなるため。
- 鍵の型の制限は `where DecEq(K), Hash(K)` だけ（OWN「affine の std（Rust と同じコストモデル）」の `HashMap` の項と同じ）。`eval.rs` の `HashMap` は構造的な鍵（`Value::Data`）を受け付けるので、実行系はこの制約に何も足さない。
- 構造的な述語には辞書の引数がない（「展開」の「規則」）ので、これらの関数の実行時の形に辞書の引数は現れない。

---

## 利用者定義のクラス

この節の `(クラス, 型の頭)` による規則は、単一型パラメータの場合である。
複数・項パラメータについては「型と項のパラメータ列」の選択パターンを用いる。

### 宣言の検査（順に）

1. クラス：「クラス」の形。メソッドの名前は一つのクラスの中で一意。法則の名前も一意で、メソッドの名前とぶつからない。
2. インスタンス：「インスタンス」の形。クラスのパラメータの境界（種、高階なら 「型構成子の変数」）に頭が収まること。境界を超えれば `"error: Ord takes types up to affine, and Handshake is linear"`。
3. **一意性**：プログラム全体（すべての tote を合わせたもの）で、一つの `(クラス, 型の頭のコンストラクタ)` にインスタンスは高々一つ。二つ目は `"error: Ord already has an instance for List (at a.nib:3:1)"`。頭の引数が違っても（`List(A)` と `List(i64)`）同じ頭なので二つ目はエラー（そもそも `List(i64)` は頭の形の規則で書けない）。
4. **書ける場所**：`pub(open)` でないクラスの instance は、クラスを宣言したファイルにだけ書ける（`"error: \`Size\` is a class the file \`lib\` declares without \`pub(open)\`: …"`、visibility.md「規則」）。std の `Ord` と `ToText` は `pub(open)` である。
5. **孤児なし**：インスタンスは、クラスを宣言した tote か、頭のコンストラクタを宣言した tote に置く。そうでなければ `"error: Ord(Text) must be in the tote of Ord or of Text"`。組み込みの型（`i64`、`Text`、`Buf` など）と std の型（`List`、`Option`、`Pair`、`Vec`、`HashMap`、`Map`）は std の tote が宣言したものとする。
6. メソッドの定義の署名がクラスの署名の置き換えと一致すること。本体は普通の関数として検査する（`where` の仮定は 「解決」で使える）。
7. 法則（「法則（tauto）」）。

一つのファイルだけを `tauto run` するとき（tote がないとき）は、そのファイルと std の二つの tote があるものとして 5 を判定する。

### 一意性の意味

インスタンスが型の頭ごとに一つなので、「この型の値をこのクラスでどう扱うか」は型だけで決まる。`ordmap` のような不変量を持つデータは、比べ方が呼び出しごとに変わらないことに頼れる（比べ方を引数で渡す形では、同じ写像に違う `cmp` を渡す誤りを検査できないが、この規則ではその誤りが起きない）。別の比べ方が要るときは、別の型で包む（`struct Desc { v: i64 }` に `instance Ord(Desc)`）か、関数を引数に取る `_by` の関数（`Vec::sort_by`）を使う。`Vec::sort` と `Vec::sort_by` は署名が違うので「書き方は一つ」に反しない（OWN「ω の std（shared）」の `fold` と `fold_once` と同じ）。

---

## 高階のクラス


### 型構成子の変数

```nib
class Functor(F: (Shared) -> Shared) {
  fn map<A: Shared, B: Shared>(x: F(A), &f: (A) -> B): F(B)
  theorem map_id<A: Shared>(x: F(A)): Functor::map(x, &(a: A) => a) = x
  theorem map_compose<A: Shared, B: Shared, C: Shared>(x: F(A), f: (A) -> B, g: (B) -> C):
    Functor::map(Functor::map(x, &f), &g) = Functor::map(x, &(a: A) => g(f(a)))
}

instance Functor(List) { … }
instance Functor(Option) { … }
instance<T: Shared> Functor(Result(T)) { … }       // 末尾の引数 E（エラーの側）を写す（「部分適用」）
```

- ジェネリクス `<F: (k₁) -> k₂>`。`k₁`、`k₂` は種（`copy`、`shared`、`affine`、`linear`）。意味は「種が `k₁` 以下の型 `X` について、`F(X)` の種は `k₂` 以下」。`<F: (Linear) -> Linear>` が最も緩い。
- 型構成子の変数は、関数・定理・クラス・インスタンスのジェネリクスに書ける。引数は一つだけ（`(k₁, k₂) -> k` は入れない）。
- 種の検査：`F` に型構成子 `H`（または部分適用 `H(T₁, …, Tₙ₋₁)`）を当てるとき、種 `k₁` の新しい型変数 `X` を作り、`kind(H(T₁, …, Tₙ₋₁, X)) ⊑ k₂` を OWN「型の種 kind(T)」で確かめる。
- tauto では、`<F: (Shared) -> Shared>` はカーネルの `F: (Type) -> Type` になる（`<A: Shared>` が `A: Type` になるのと同じ。種は Nib の層の検査だけが見る）。

### 部分適用

- 型構成子の位置（型構成子の変数の実引数、高階のクラスのインスタンスの頭）には、型コンストラクタそのもの（`List`）か、**末尾以外の引数** を与えたもの（`Pair(A)`、`Result(T)`）を書ける。残るのはいつも **末尾の引数**。
- `Result(T, E)` は値の型 `T` が先なので、`Functor(Result(T))` はエラーの側 `E` を写す。値の側を写したいときは、引数の順の違う型を std に置くか、`Result` 専用の関数を使う。順序を選べる記法（型の λ）は入れない。
- 型構成子の位置以外で引数の数が宣言と一致しない型（`let x: Pair(i64) := …`）はエラー（`"error: Pair takes 2 arguments"`）。
- 展開とカーネルでは、`Pair(A)` は λ `(B: Type) => Pair(A, B)` になる（カーネルが部分適用を受け取る必要はない）。

### 適用のマッチング

`F(X)`（`F` が推論中の型構成子の変数）と型を合わせる規則は次の一つだけ：

```text
F(X)  ~  H(U₁, …, Uₙ)      （n ≥ 1）
  ⇒  F := H(U₁, …, Uₙ₋₁)、 X ~ Uₙ
F(X)  ~  引数のない型、関数型、union、タグ付きの型
  ⇒  失敗（"error: i64 is not an application of a type constructor"）
```

- **構造的・第一階**。`F := (Y) => List(i64)`（定数の λ）のような解は考えない。解はいつも一つで、後戻りはない。
- `types.rs`（Nib の層）と `check/implicit.rs`（tauto の暗黙引数）の両方に同じ規則を入れる。カーネルは `F` が決まった後の項しか見ない（展開した項は 「部分適用」の λ を含むので、カーネルの β で `F(X)` が `H(…, X)` になる）。
- タグ：`@a List(i64)` に対しては、タグを外した型と合わせる（タグは値を変えないので、インスタンスはタグの内側の型のもの）。

### メソッドのジェネリクス

- クラスのメソッドは自分のジェネリクス（型変数、型構成子の変数、行変数）を持てる。`Functor::map` の `A`、`B`。呼び出しのたびに引数から決まる。
- メソッドのジェネリクスに `where` は書けない（クラスの `where` もない）。制約の要るメソッドは、クラスの外の関数として書く。
- 行変数：メソッドの行変数は呼び出しの引数から決まるので許す（`fn traverse<A, B, !e>(x: F(A), &f: (A) -> B ! e): F(B) ! e`）。ただし法則を持つクラスのメソッドは行を持てない（「法則を持つクラスのメソッドの条件」）。
- このとき辞書の引数は **多相な関数** になる（「多相な辞書の引数」）。

カーネルで検査した辞書の経路は、純粋なメソッドの型・項パラメータ列を扱う。
メソッド固有の行変数、所有権の種の制約、借用引数、`where` はこの経路では扱わない。
effect を持つメソッドと、法則との境界も変わらない。
この辞書を要求するジェネリック関数を、未検査の実行コードから直接呼ぶことはできない。
カーネルが検査する関数の中で型・項引数と辞書を決め、実行コードには依存する制約を
要求しない入口を渡す。未検査の呼び出しで省略された項ジェネリクスも推論しない。

### Rust への写像

Rust に高階の trait はないので、型構成子の変数を持つ関数は **型構成子ごとに単相化** する（「Rust バックエンド」の「高階のクラス」）。

---

## 解決

### 規則

制約 `C(T)` を、その場所の **仮定**（囲んでいる宣言の `where`、インスタンスの `where`）と **インスタンス** から次のどちらか一つで満たす。

```text
(仮定)  T を正規形（タグを外し、型の別名を開いたもの）にしたものが型変数・型構成子の変数 V で、
        C(V) が仮定にある                      ⇒ その仮定
(構造)  C が構造的な述語                        ⇒ 「構造的な述語 `PartialEq`・`DecEq`・`Hash`」の「規則」で判定（V については仮定）
(インスタンス) T の頭が H、C の (C, H) のインスタンス instance<X…> C(H(X…)) where D₁(Xᵢ), …
        があり、頭のマッチングで X… := U…       ⇒ そのインスタンスと、各 Dⱼ(Uᵢ) を同じ規則で再帰的に解決したもの
どれもなければ                                  ⇒ "error: no instance Ord((i64) -> i64)"
```

- `T` が型変数で仮定がなければ `"error: Ord::compare needs Ord(A): add where Ord(A)"`。
- `T` がまだ推論中の変数なら、型の検査の終わりまで待つ（`types.rs` が数の型を既定の `i64` に決めるのと同じ時点）。そのときも決まらなければ `"error: the type in Ord(?) is not determined"`。**推論中の変数をインスタンスから決めることはしない**（解決は型を作らない）。
- 子の制約 `Dⱼ(Uᵢ)` の `Uᵢ` は `T` の真の部分項なので、解決は型の大きさで必ず止まる。数えるものはない。
- 選び方は一つしかない（一意性、「宣言の検査（順に）」）ので、仮定とインスタンスの両方が当てはまることはない（`T` が型変数なら仮定、頭があればインスタンス）。

### 解決の結果

解決は制約ごとに **証拠** を返す。証拠は次の木：

```text
Ev ::= Assume(C, V)                         where の仮定
     | Inst(C, H, [型…], [Ev…])            インスタンスと、その where の証拠
     | Structural(C, T)                     構造的な述語（実行時の値を持たない）
```

`TypeReport` に、各メソッドの呼び出しと各制約付き関数の呼び出しの位置ごとに証拠を残す。展開（「展開」）と Rust バックエンド（「Rust バックエンド」）はこれだけを見る。

---

## 展開

### 規則

| 書いたもの | 展開後 |
|---|---|
| `class C(P: Type) { fn m(…): R ! ρ … }` | 何も出さない（署名だけを覚える） |
| 制約 `C(T)` が `where` にある宣言 | `C` のメソッド `m₁ … mₖ` ごとに引数 `C::mᵢ@T: S` を、宣言の明示の引数の **後ろ** に、`where` の順・メソッドの宣言の順で足す。`S` はメソッドの署名の `P` を `T` で置き換えた関数型 |
| 構造的な述語の制約 | 何も足さない |
| `instance<X…> C(H(X…)) where D(Xᵢ)… { fn m(…) { body } }` | メソッドごとに最上位の関数 `fn C::m@H<X…>(元の引数…, Dの辞書の引数…): … { body }` |
| `C::m(args)` で証拠が `Assume(C, V)` | `C::m@V(args)`（辞書の引数を呼ぶ） |
| `C::m(args)` で証拠が `Inst(C, H, [U…], [e…])` | `C::m@H(args, ⟦e…⟧)` |
| 制約付きの関数 `f` の呼び出しで、制約の証拠が `e…` | `f(args, ⟦e…⟧)` |
| 証拠 `⟦Assume(C, V)⟧`（メソッド `m`） | 辞書の引数 `C::m@V` |
| 証拠 `⟦Inst(C, H, [U…], [e…])⟧`（メソッド `m`） | `e…` が空なら関数名 `C::m@H`。でなければ閉包 `(引数…) => C::m@H(引数…, ⟦e…⟧)` |

- `@` を含む名前は利用者が書けない（字句で拒否される）ので、展開が作る名前はぶつからない。
- 法則（「法則（tauto）」）は、tauto の展開でだけ証明の引数として足される。Nib の層（`types.rs`、`rows.rs`、`lin.rs`、`eval.rs`）の展開には出ない。

### 例

```nib
// 書いたもの
fn max<A: Shared>(a: A, b: A): A where Ord(A) {
  match Ord::compare(&a, &b) {
    Less => b
    Equal => a
    Greater => a
  }
}
max(Cons(1, Nil), Nil)

// 展開後（tauto expand で見える。法則の引数は除いて示す）
fn Ord::compare@i64(&a: i64, &b: i64): Ordering { … }
fn Ord::compare@List<A>(&a: List(A), &b: List(A), Ord::compare@A: (&a: A, &b: A) -> Ordering): Ordering {
  … Ord::compare@A(&x, &y) … Ord::compare@List(&xs, &ys, Ord::compare@A) …
}
fn max<A: Shared>(a: A, b: A, Ord::compare@A: (&a: A, &b: A) -> Ordering): A {
  match Ord::compare@A(&a, &b) { … }
}
max(Cons(1, Nil), Nil, (&x: List(i64), &y: List(i64)) => Ord::compare@List(&x, &y, Ord::compare@i64))
```

### 多相な辞書の引数

メソッドが自分のジェネリクスを持つと、辞書の引数の型は多相になる：

```nib
fn double_all<F: (Shared) -> Shared>(x: F(i64)): F(i64) where Functor(F) {
  Functor::map(x, &(n: i64) => n * 2)
}
// 展開後
fn double_all<F: (Shared) -> Shared>(x: F(i64), Functor::map@F: <A: Shared, B: Shared>(x: F(A), &f: (A) -> B) -> F(B)): F(i64) {
  Functor::map@F(x, &(n: i64) => n * 2)
}
```

- `<A, B>(…) -> …` の形の型（多相な関数型）は **展開だけが作る**。利用者は書けない（構文にない）。
- `types.rs` は、多相な関数型の引数について次だけを許す：**呼ぶ**（呼び出しのたびに新しい変数で具体化する）、**そのまま別の呼び出しの多相な引数の位置に渡す**、**閉包に捕まえる**（捕まえた変数も同じ型）。値として別の束縛に入れる、構造体に入れる、結果として返すことはない（展開がそういう項を作らない。作れば展開の誤りとして型エラー）。
- 多相な引数の位置に渡す実引数は、インスタンスのメソッドの関数名か、それを辞書で包んだ閉包（「展開」の「規則」の最後の行）だけ。閉包のときは、閉包の引数の型にメソッドのジェネリクスを持たせて検査する（閉包が多相になる）。
- カーネルでは普通の Π（`Functor::map@F: Π (A B: Type). F A → (A → B) → F B`）で、何も足さない。
- `rows.rs`：多相な引数の呼び出しの行は、メソッドの署名の行を具体化したもの。
- `lin.rs`：辞書の引数は shared。

### 辞書の引数の種

- 辞書の引数は **shared な関数の値**（借用 `&f` ではない）。インスタンスのメソッドは最上位の関数で、辞書で包んだ閉包も shared な辞書だけを捕まえるので、shared に収まる。
- したがって、制約付きの関数の中で作った閉包が辞書を捕まえても借用閉包にはならず、返せる（`fn sorter<A: Shared>(): (List(A)) -> List(A) where Ord(A) { (xs: List(A)) => sort(xs) }` は書ける）。
- CFL（OWN「制御フロー線形性（CFL）の規則」）の検査で、辞書の引数は複製可として扱う。

### どこで展開するか

展開のパス（`crates/tauto-nibcheck/src/types/classes.rs`、`types/expand.rs`）が、宣言の検査（「宣言の検査（順に）」）、解決（「解決」）、展開（「展開」の「規則」）をする。順序は：

```text
構文解析 → surface → classes::check_declarations → types.rs（解決の結果を TypeReport に）
         → classes::expand → 展開後のプログラムを types.rs・rows.rs・lin.rs でもう一度検査 → eval / カーネル
```

- 型の検査を二度走らせるのは、展開の誤りを、クラスを知らない検査器が拒否できるようにするため（健全性は書き味に優先する）。二度目で失敗したら、それは展開か解決の誤りで、利用者のエラーではない（`"internal: the expanded program does not check: …"`）。受け入れ試験で一度も出ないこと。
- `tauto check` のカーネルが受け取るのは展開後の項だけ。カーネルは `class` も `instance` も知らない。

---

## 法則（tauto）


### クラスの法則

```nib
theorem name<ジェネリクス>(仮定…): 命題
```

- クラスの中に書く。命題は tauto の命題（`Eq`、`Iff`、`∀` など）。クラスのパラメータとメソッド（`Ord::compare(a, b)`）を使える。
- 命題の中では借用の印 `&` を書かない。命題の中の出現は使用に数えず（OWN「型・命題・証明との関係（tauto）」）、借用の引数を取るメソッドも値を渡して書く。展開では、`&x` の引数は値の引数として扱われる（カーネルは借用を知らない）。
- Nib の層は クラスとインスタンスの `theorem` を読み飛ばす（Nib に命題はない）。

### 法則を持つクラスのメソッドの条件

- メソッドの行は空でなければならない（`! {}`、行変数もなし）。効果を持つ関数（ブロック、`var`、`perform`、`handle` を使うもの）はカーネルが読み飛ばし、証明の対象にならないので、その法則は述べられない。違反は `"error: Functor::traverse performs effects, so Functor cannot have laws"`。
- 法則のないクラスのメソッドは効果を持てる（「効果と再開量」）。
- 法則のないクラスのうち、メソッドが効果を持つものと、パラメータが型構成子（`F: (Shared) -> Shared` のように種が `Type` でないもの）のものは、証明の言語のクラスではなくプログラムのクラスとして、インスタンスと、そのクラスを `where` に持つ関数とともに書いたとおりに実行する。Nib で書けるクラスは tauto でも失敗させず、Nib と同じ意味で動かす。

### インスタンスの証明

```nib
instance Ord(Point) {
  fn compare(&a: Point, &b: Point): Ordering { … }
  theorem equal_iff<a: Point, b: Point>(): Iff(Ord::compare(a, b) = Equal, a = b) {
    …証明の項…
  }
  theorem swap<a: Point, b: Point>(): … { … }
  theorem trans<a: Point, b: Point, c: Point>(h1: …, h2: …): … { … }
}
```

- 法則ごとに `theorem` を書き、命題はクラスの命題のパラメータを頭で置き換えたものを **書き写す**（読み手がその場で確かめられるように）。検査は「書いた命題がクラスの命題の置き換えと convertible」。
- 本体は証明の項で、定理と同じくカーネルが検査する。インスタンスの `where` の制約の法則を使える（`Ord::trans` を `A` について）。
- インスタンスのメソッドは、カーネルの対象でなければならない（純粋で、`match` による構造的な再帰だけ）。そうでなければ命題がメソッドを開けないので証明できず、「証明のないインスタンス」の incomplete になる。

### 証明のないインスタンス

- 法則の `theorem` の項目が足りないインスタンスは **incomplete**（穴 `?h` と同じ `Verdict::Incomplete`）。
  - `tauto run`、`types.rs`・`rows.rs`・`lin.rs` は受理する（Nib のプログラムとしては正しい。Nib に証明はない）。
  - `tauto check` はそのインスタンスと、その法則を使う宣言を incomplete と報告する（終了コード 3）。独立カーネル（`check/core.rs`）には渡らない。
  - `tauto goals` は足りない法則を穴として出す（名前は `law:Ord(Point)::trans`）。`tauto fill` で埋められる。
  - `tauto lint` は `std/` と `meta/` で証明のないインスタンスを拒否する。
- `sorry` 相当の「証明したことにする」書き方は入れない（書きかけの証明は名前付きの穴 `?h` で表し、穴を含む宣言は受理されない）。

### 組み込みの型と extern のインスタンス

- 組み込みの型（`i64`、`Text`、`Buf` など）はカーネルの帰納型ではないので、それについての法則はカーネルで証明できない。std のこれらのインスタンス（`Ord(i64)`、`Ord(Text)`、`ToText(i64)` など）の法則は、`extern` のインスタンス（「extern のインスタンス」）と同じく **信頼** し、`tauto check` の信頼の一覧に出す。`std/` と `meta/` の「公理を使わない」検査は、これらを使う証明を公理を使うものとして数える。
- これは std だけに許す（孤児の規則で、組み込みの型へのインスタンスは std のクラスなら std にしか置けない）。利用者のクラスの組み込みの型へのインスタンスは 「証明のないインスタンス」の通り incomplete になる（扱いは「未決定」の節）。

### 構造的な述語の法則

- `DecEq` と `PartialEq` の法則は、検査済みの `inductive`（カーネルの帰納型）が **一覧に書いたときだけ** 生成する（`inductive T(…): Type => fn T::beq, theorem T::beq_refl, theorem T::beq_sound, theorem T::deq { … }`。四つ全部を書く。`macro.md`「作る宣言の一覧」）。書いた型に作れなければ、理由つきのエラー（同名の宣言がすでにある場合も、黙って飛ばさない）。生成するのは：`I::deq<a: I, b: I>(): Iff(Eq(Bool, a == b, true), Eq(I, a, b))`。`==` は展開で、生成した決定手続き `I::beq(a, b)`（eliminator で定義し、フィールドごとに比べる）になる。どちらもカーネルが検査し、規則は足さない（添字つきの族の `match` が不可能な腕を除くのに使う no-confusion `I::nc` の生成と同じ作り）。
- フィールドに `DecEq` でない型（関数型、`Prop` の証明など）がある帰納型には生成しない（`DecEq` が成り立たない）。
- Nib の `struct` / `enum` には法則を生成しない。`inductive struct` / `inductive enum` と書いたものは同じ形の帰納族として証明にも現れる（`program-data.md`）が、決定可能な等しさは `inductive` に一覧を書いたときだけ作る。例外は prelude の `Option`・`List`・`Pair`・`Ordering`（`std/prelude/Std.taut`）で、証明はこれらを帰納族として読み、四つの宣言を生成する。`struct` の構成子は `S { f: e, … }` と書き、`S { f: p, … }` で照合する。

### 証明で法則を使う

```nib
theorem insert_sorted<A>(x: A, xs: List(A), h: Sorted(A, xs)): Sorted(A, insert(x, xs)) where Ord(A) {
  … Ord::trans(h1, h2) …
}
```

- `C::law(…)` で法則を呼ぶ。法則のジェネリクスは暗黙引数（「メソッドの呼び出し」と同じ）。
- 証明の側（`.taut`）では、クラスは **カーネルがすでに持つ record** に読まれる（`check/classes.rs`。カーネルに規則は足さない）：
  - `class C(A: Type)` は、メソッドの record `inductive C(A)`（構成子 `C::Mk`）と、法則の record `inductive C::laws(A, inst@C: C(A))`（構成子 `C::laws::Mk`。法則の命題はメソッドを `C::m(…)` で使える）。射影 `C::m`、`C::l` は record を第一引数に取る関数・定理。法則だけ別の record にするのは、法則の足りないインスタンスでもメソッドの record は完全で、`C::m(…)` が簡約できるため。
  - `instance<G> C(H(G)) where D(G)` は、メソッドごとの関数 `C::m@H`、法則ごとの定理 `C::l@H`（再帰はふつうの構造再帰）、それらを束ねる `C::inst@H`（メソッドの record）と `C::laws@H`（法則の record）。足りない法則は穴 `?law:C(H)::l` で、`C::laws@H` だけが incomplete になる（「証明のないインスタンス」）。
  - `where C(T)` は、ジェネリクスの後ろの引数 `inst@C0: C(T)`。定理の `where` にはさらに、クラスが法則を持つなら `inst@C0@laws: C::laws(T, inst@C0)` が付く。関数（`fn`）の `where` は record だけ。
- どの record かを、書き手は渡さない（書き方は一つ）。`C::m(…)`・`C::l(…)` の呼び出しで、`check/implicit.rs` が（1）文脈の `inst@…` のうち型の合うもの、（2）なければ型の頭の構成子の instance（`where` があれば子の record を再帰して）、を探して書き出す。見つからなければ `no instance of C(T)`。カーネルと独立カーネルには書き出された項だけが渡る。
- インスタンスのメソッドの再帰は、`C::m(…)` と書いたものが、その型への instance の `C::m@H` の再帰（構造再帰）として読まれる（行き先の引数が、`match` した値の再帰的なフィールドであるもの）。インスタンスの法則の再帰も同じで、法則自身のジェネリクスを書く（`Ord::refl(xs)`）。

---

## 所有権・効果との関係

### 種と所有権

- クラスのパラメータは種の上限を持つ（「クラス」）。メソッドの引数は普通の関数と同じ所有権の規則（OWN「使用の規則」）で、借用で受ける（`&a: A`）なら affine・linear の型にもインスタンスを書ける。
- 辞書の引数は shared（「辞書の引数の種」）。
- `clone` と Drop は構造的・自動のまま、クラスにしない（OWN「Drop と clone」）。

### 効果と再開量

- メソッドの行はクラスの宣言で決まる。インスタンスのメソッドの行は、クラスの行に含まれればよい（関数の部分型と同じ、[`nib.md`](nib.md)「型の関係」の部分型）。呼び出しの行はクラスの行で、**どのインスタンスが選ばれても変わらない**。
- メソッドのジェネリクスの行変数（「メソッドのジェネリクス」）は呼び出しの引数から決まる。インスタンスによって行が変わる形（クラスのパラメータに行変数を持たせる）は入れない。
- 再開量はメソッドの行の効果の宣言のとおり。辞書の引数は shared なので、`ω` の効果を跨いでよい（OWN「制御フロー線形性（CFL）の規則」）。
- 法則を持つクラスのメソッドは行を持たない（「法則を持つクラスのメソッドの条件」）。

### `show`

`show` はホストの観測の操作のままで、クラスにしない。`ToText`（「std にあるもの」）は利用者が文字列を作るためのクラスで、`show` の表示は変えない。

---

## Rust バックエンド

型クラスから生成する Rust です。

### 構造的な述語

| tauto | 生成する Rust |
|---|---|
| `PartialEq(T)` が成り立つ struct / enum | `#[derive(PartialEq)]`（RB「struct と enum」の derive の一つ） |
| `DecEq(T)` が成り立つ struct / enum | `#[derive(PartialEq, Eq)]` |
| `Hash(T)` が成り立つ struct / enum | `#[derive(Hash)]` |
| `where PartialEq(A)` | `A: PartialEq`（RB「借用、lifetime、型変数」の型変数の境界の一つ） |
| `where DecEq(A)` | `A: PartialEq + Eq` |
| `where Hash(A)` | `A: Hash` |
| extern の `instance DecEq(Regex)` | 何も生成しない。境界として使い、Rust の型に実装がなければ rustc が拒否する |
| `a == b` | `a == b`（被演算子は Rust でも参照で比べられる） |

`Float` の `==` は Rust の `f64` の `==`。

### 高階でないクラス

| tauto | 生成する Rust |
|---|---|
| `class Ord(A: Type) { fn compare(&a: A, &b: A): Ordering }` | 生成したクレートの中に `pub trait Ord_ { fn compare(a: &Self, b: &Self) -> Ordering; }`（名前は RB「名前空間」の規則で衝突を避ける） |
| `instance<A> Ord(List(A)) where Ord(A)` | `impl<A: Ord_> Ord_ for List<A> { … }` |
| `where Ord(A)` | `A: Ord_` |
| `Ord::compare(&x, &y)` | `<T as Ord_>::compare(&x, &y)` |
| メソッドのジェネリクス | trait のメソッドのジェネリクス |
| メソッドの層 | メソッドの実体の層は RB「層の決定と単相化」のとおり。trait のメソッドは S 層なら普通の `fn`、それ以外は RB の層ごとの呼び出し規約の形 |

- trait を `tauto-rt` でなく生成したクレートに置くのは、RB「`show`、実行時エラー、位置」の `Show` と同じ理由（Rust の孤児規則で、extern の型にも実装できるように）。tauto の一意性と孤児の規則は Rust の規則より強いので、写した先で衝突しない。
- **NIR は展開前の形を持つ**：制約、メソッドの呼び出し、解決の証拠（「解決の結果」）。辞書の引数（「展開」）は NIR に入れない。eval とカーネルは展開後を、RB は trait を使うので、両者の一致は RB の差分試験（eval と生成コードの `show` の列）で確かめる。

### 高階のクラス

- Rust には型構成子の変数がないので、**型構成子の変数を持つ関数は型構成子ごとに単相化** する。メソッド固有のジェネリクスを持つクラスの辞書（展開が作る多相な関数）を受け取る関数も同じで、辞書ごとに単相化する。vm、Rust、JavaScript のバックエンドは同じ NIR から生成するので、三つとも同じ扱いになる。
- 単相化は NIR に下ろす前、展開と型検査の後に行う。呼び出しごとに、検査済みの具体化が与える型構成子（部分適用を含む）と、展開が足した辞書の引数（インスタンスの関数）を鍵にして関数を写す。写しでは、型構成子の変数をその型構成子として書き、辞書の型が触れるクラスの引数もその型にし、辞書の引数をインスタンスの関数に置き換えて、呼び出しからは辞書の引数を外す。写しの中の呼び出しも同じように写す。それ以外のジェネリクスは写しのジェネリクスのまま残る。写した後のプログラムはもう一度型検査し、通ったときだけ下ろす。
- 高階のクラスのメソッドの呼び出しは、単相化した後は具体的な型構成子のインスタンスのメソッドの直接の呼び出しになる（trait は作らない）。
- 単相化できない形は `Unsupported`（「ジェネリクスをもつクラスメソッド、または型コンストラクタ変数」）になる。関数を呼ばずに値として使うもの、呼び出しの位置で型構成子がまだ変数のもの（その関数を単相化しない関数から呼ぶもの）、型構成子の変数について多相な再帰（`fn f<F>(…) { … f<Compose(F)>(…) … }` のように、再帰で型構成子が大きくなる形。写しの数に上限を置いて止める）。tauto の型検査は受理する（eval では動く）。

### `tauto bind`

RB「設定 `bind/<crate>.config.eure`」の `traits = […]` の写像は次のとおり：

| Rust の trait の実装 | `bind/<crate>.taut` |
|---|---|
| `PartialEq` | `extern { instance PartialEq(S) }` |
| `PartialEq` + `Eq` | `extern { instance PartialEq(S)  instance DecEq(S) }` |
| `Hash` | `extern { instance Hash(S) }` |
| `Ord`（Rust の） | `extern { instance Ord(S) }` |
| `Display` | `extern { instance ToText(S) }` |
| `Clone` | `fn clone(&s: S): S`（clone はクラスにしない） |
| `Iterator<Item = T>` など、std に対応するクラスがない trait | 具体的な関数（RB「写像の規則」） |

---

## std にあるもの

`std/prelude/` に置く（`Std`・`Text`・`Num` は Nib のプログラムがすべて見る。ほかは `import std::prelude::Os` のように import して見る。`visibility.md`「prelude」）。

```nib
// std/prelude/Std.taut
enum Ordering {
  Less
  Equal
  Greater
}

// std/prelude/Ord.taut（Nib のプログラムと証明の両方が読む）
class Ord(A: Linear) {
  fn compare(&a: A, &b: A): Ordering
  theorem equal_iff<a: A, b: A>(): Iff(Ord::compare(a, b) = Equal, a = b)
  theorem swap<a: A, b: A>(): Iff(Ord::compare(a, b) = Less, Ord::compare(b, a) = Greater)
  theorem trans<a: A, b: A, c: A>(h1: Ord::compare(a, b) = Less, h2: Ord::compare(b, c) = Less): Ord::compare(a, c) = Less
}

instance<A> Ord(List(A)) where Ord(A) { … }       // 辞書式。法則の証明つき
instance<A> Ord(Option(A)) where Ord(A) { … }     // None < Some。法則の証明つき
instance<A, B> Ord(Pair(A, B)) where Ord(A), Ord(B) { … }   // 法則の証明つき

// std/prelude/Classes.taut
class ToText(A: Linear) {
  fn to_text(&a: A): Text
}

instance Ord(i64) { … }   instance Ord(i32) { … }   instance Ord(u8) { … }   instance Ord(u32) { … }   instance Ord(u64) { … }
instance Ord(Bool) { … }  instance Ord(Text) { … }  instance Ord(()) { … }

instance ToText(i64) { … }  …（整数型、Bool、Text、()）
instance<A> ToText(List(A)) where ToText(A) { … }      // "[1, 2]"
instance<A> ToText(Option(A)) where ToText(A) { … }    // "None" / "Some(1)"
instance<A, B> ToText(Pair(A, B)) where ToText(A), ToText(B) { … }   // "(1, a)"

fn Vec::sort<A: Linear>(&mut v: Vec(A)): () where Ord(A)
fn List::max<A: Shared>(xs: List(A)): Option(A) where Ord(A)
fn List::min<A: Shared>(xs: List(A)): Option(A) where Ord(A)
fn join<A>(xs: List(A), sep: Text): Text where ToText(A)
```

- `Ord(Text)` は UTF-8 のバイト列の辞書式（Rust の `str` の `Ord` と同じ）。[`self-host.md`](self-host.md) の `Text::compare` と同じ結果であること。
- `Ord(Float)` は置かない（全順序でない）。
- `Ord` は一度だけ、`std/prelude/Ord.taut` で宣言する。Nib の層はこのファイルの `theorem` を読み飛ばし、カーネルはこのファイルをすべて検査する（`check.rs` の `kernel_prelude`。prelude の宣言はどれも両方のカーネルが受理し、商の公理 `Quot::sound` のほかに公理も穴も持たないこと）。だから同じ `compare` を、プログラムが実行し、証明が開く。
- `Ord` のインスタンスは std のものも法則を持つ。`List`・`Option`・`Pair` のものは `std/prelude/Ord.taut` に法則の証明とともに置き、その補題（`ord_then`、`ord_equal_eq` など）も同じファイルに置く。組み込みの型のもの（`std/prelude/Classes.taut`）は法則を書かず、信頼する（「組み込みの型と extern のインスタンス」）。カーネルはこれらの型を知らないので、証明には現れない。
- `List` と `Pair` の `compare` は `ord_then(前の比較, 後の比較)` と書く（法則の証明はこの形を開く）。Nib は引数を先に評価するので、前が `Equal` でなくても後を比べる。
- 証明の側だけの型のインスタンスは `std/` に置く：`Ord(Nat)` は `std/Ord.taut`。extraction は `Nat` を `nat` に写すので、これを `Ord(nat)` に写す。
- `Functor` は std に置かない（「未決定」）。試験の中で宣言する。
- `Map` を `Ord` を使う平衡木に替えるかは、この文書の範囲外（[`self-host.md`](self-host.md) の `ordmap` と合わせて別に決める）。

---

## Lean

### `==` の進行

Nib の Lean のモデル（`lean/Proto/Nib/`）に `==` を入れるとき（入っていなければ、その時点で）、型の述語 `PEq : Ty → Prop`（「構造的な述語 `PartialEq`・`DecEq`・`Hash`」の「規則」の `PartialEq` の規則）を定義し、`==` の型付けの規則の前提にする。示すこと：

- **補題 eq_progress**：`PEq T` で、`v₁ v₂ : T` が値なら、`equal v₁ v₂` は `cannot compare` の実行時エラーにならない（`Bool` を返す）。
- progress の定理（`Safety.lean`）の `==` の場合をこの補題で閉じる。

### 展開は信頼の外

解決と展開は精密化で、**信頼の核の外** にある。展開後のプログラムを、クラスを知らない検査器とカーネルが検査し直すので、Lean の証明義務は増えない。ただし多相な辞書の引数（「多相な辞書の引数」）は Nib の型検査の新しい形なので、Nib のモデルに入れるなら、`HasType` に「多相な関数型の変数を呼ぶ」規則を足し、preservation を延ばす（必須ではない：tauto ではカーネルが Π として検査する）。

### 生成した `I::deq`

生成した `I::beq` と `I::deq` はカーネルが検査するので、Lean の証明は要らない（`I::nc` と同じ）。

---

## 未決定

1. `DecEq(Decimal)`・`Hash(Decimal)`：`Decimal` の表現（`ownership.md`「未決定」）が正規化されていれば成り立つ。表現を決めるときに決める。
2. 利用者のクラスの、組み込みの型（`i64` など）へのインスタンスの法則：組み込みの型の算術を述べる補題がないので証明できず、incomplete のまま残る。組み込みの型の算術についての信頼する補題の集まり（prelude）を作るか。必要になってから決める。
3. std に `Functor` を置くか：self-host か std の中で使い道が出てから決める。
4. `Map`（`Shared.taut`）を `Ord` を使う平衡木に替えるか：[`self-host.md`](self-host.md) の `ordmap` と合わせて決める。
5. マクロとの関係：構文マクロがインスタンスを生成すること、型付きマクロが解決済みの項（証拠付き）を受け取ることを、[`macro.md`](macro.md) の設計と合わせる。
