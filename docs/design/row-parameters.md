# データ型の行パラメータ

`struct` と `enum` のパラメータは、`!` を付けて宣言すると行パラメータになる。
行変数は宣言の `!` だけで決まり、使い方からは推論しない。`!` なしで宣言した名前を行に書く（`e`）とエラーで、
宣言のない名前も同じ。書き方は関数の行変数と同じで、`D(e)` と使う。

```
struct Handlers(!e) { on_key: (k: i64) -> i64 ! e }

fn dispatch<!e>(&h: Handlers(e), k: i64): i64 ! e { (h.on_key)(k) }
```

別のデータ型の行パラメータの位置に渡すだけのとき（`Answer(e)`）も、
渡す側のパラメータは `!` を付けて宣言する。

```
struct Answer(!e) { run: () -> Text ! e }
struct App(!e) { answers: List(Answer(e)) }
```

`App` の `e` は `Answer` の行にしか届かないので行パラメータで、`App(e)` は `e` の
値を持たない。`App(e)` の種は `e` に左右されず、`ω` で再開する `e` を跨いで生きて
いてもよい。行パラメータの上限は `(!e: <=1)` と書く。

効果の行の検査は、行パラメータを型の引数と同じく代入する。行の一致は
定義的同値で比べる（`semantics.md`）。

## 行を引数に書く

（関数の行の書き方は [`syntax.md`](syntax.md)「effect の行」。）

行パラメータには、行変数のほかに行そのものを渡せる。書き方は関数の行と同じで、
`!` の後ろに集合の式を書く（`!{a, b} ∪ e`、`!e`、`!{}`）。

```
struct Grant(!e) { gives: List(Text), run: () -> i64 ! e }

fn give_pos<!e>(g: Grant(!{pos} ∪ e)): Grant(e) {
  let r := g.run
  Grant {
    gives: Cons("pos", g.gives),
    run: () => handle { r() } with {
      pos(), k => k(10)
      return v => v
    }
  }
}

fn done(g: Grant(!{})): i64 {
  let r := g.run
  r()
}
```

`give_pos` は行から `pos` を取り除くただ一つの道で、取り除くときに `gives` へ
書き足す。`done` は空の行しか受け取らないので、`done` に届いた `Grant` の
`gives` には、行にあったどの効果も入っている。書き忘れは行の検査が
`a function value may perform vel but its type permits {}` と拒否する。
効果の一覧を値として取り出す反映（リフレクション）も、行の素性の制約も足さず、
既にある行の検査だけで、手で書いた一覧と行の食い違いをなくせる。

- 行の検査は、引数の行を関数の行と同じく扱う。`Grant(!{pos} ∪ e)` に
  `Grant(!{pos, vel})` を渡すと、`e` は書かれた効果を除いた `{vel}` になる。
- 型検査にとって行の引数は引数でなく、`()` と読む。行パラメータの位置には
  行（`!{…}`）か名前（行変数）だけが書け、行パラメータでない位置に行は書けない。
  二つの行が同じかは行の検査だけが決める。
- カーネルは行を見ない。行の引数は何も信頼の核に足さない。

## 呼び出しでの具体化

関数の行変数は、呼び出しのたびに型変数と同じく新しく具体化する。効果が行を添字に
とる（`effect cur_ui<!e>(): Tree(e)`、行は `cur_ui(e)`）ときも同じで、`e` が何かは
呼び出しごとに決まる。新しい構文は要らない。

```
fn current<!e>(): Tree(e) ! {cur_ui(e)} { perform cur_ui() }
fn on<!e>(h: () -> Unit ! e): Unit ! {cur_ui(e)} { let t := current(); (t.add)(h) }
fn comp2(): Unit ! {cur_ui(!{ctx(Text)}), ctx(Text)} {
  on(() => { let s: Text := perform ctx(); #() })
}
```

`comp2` の `on` は、`e` を引数の型にも結果の型にも持たない。`on` の行 `{cur_ui(e)}` が
`comp2` の行の `cur_ui(!{ctx(Text)})` に収まることから `e = !{ctx(Text)}` が決まる。
添字は次の順で決める。先に決まったものを採り、どれも決めないときは、これまでと同じく
`which is not known here` を報告して、型注釈か明示した instance を書かせる。

1. 型。引数の型（`root: Tree(!{})` から `Tree(e)` の `e`）、結果の型、`perform` と
   arm が返す値の型。
2. 呼び出しを囲む行。呼び出しの宣言の行が書く effect（`on` の `cur_ui(e)`）の
   instance を、囲む関数の行から選ぶ。function 引数の lambda の中では、その引数を
   受け取る parameter の関数型が書く行（呼び先が添字を持つなら具体化済みの行）が囲む行になる。
   record リテラルの field の lambda は、その field の宣言型が書く行が囲む行になる。型注釈つきの `let` に束縛した lambda は注釈の行、関数が返す lambda は結果型が書く行が囲む行になる。
   呼び先の parameter が行を書かないときは、lambda には囲む行がない（呼び出し側の行は使わない）。`perform` も同じで、型が
   決めない添字は囲む行の同じ effect の instance から決まる。
3. 引数。引数が関数の parameter なら、その parameter の型が書く行から
   （`with_ui(child, body)` の `body`）。

囲む行に同じ effect の instance が二つ以上あるとき（`cur_ui(!{a})` と
`cur_ui(!{b})`）は、どちらとも決められないので曖昧として報告する。囲む行から
**行そのもの**（`∪ e` の残り）を埋めることはしない。決めるのは、呼び出しの行が
instance として名指す添字だけである。

決めた添字は行検査が検証する。添字の取り違えは、展開した後の行検査が拒否する。

## Backend

行パラメータは生成コードに表現を持たない。生成するデータ型からは除かれる。

関数の行変数がどの callback 引数にも直接現れないとき（行パラメータを持つ
レコードで渡すとき）、その行変数は関数自身の行に書かれていなければならない。
backend は各呼出しが具体化した関数の行から、その行変数の段（tier）を決める。

JavaScript backend はレコードを扱う関数を継続形式で走らせるので、どの段でも同じ
コードで動く。Rust backend はレコードの関数フィールドに一つの段しか与えないので、
レコードで運ばれた行変数を中断する段に具体化する呼出しを拒否する。
引数に書いた行についても、Rust backend は中断する効果を名指す行と、レコード
だけが運ぶ（関数自身の行に書かれていない）行変数を拒否する。JavaScript backend と
インタプリタはどちらも動かす。

## 未決定

`semantics.md`「What has `Div`」の規則 4 は宣言時に検査する。行引数に `D` を扱う
効果を代入する場合に使用時の検査が要るかは、`Proto/Nib/Div.lean` で確かめる。
