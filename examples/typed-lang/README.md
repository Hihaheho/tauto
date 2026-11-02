# 型付きの式言語: 文法と型付け規則を書き、安全性を証明する

数・真偽値・`+`・`==`・`if` を持つ小さな式言語の例です。人が書くものは三つだけです。

1. **文法**（`src/syntax.taut` の `inductive_syntax!`）。読む関数 `tl::parse` と、証明から見える木 `tl::Expr::I` が作られます。
2. **型付け規則**（`src/core.taut` の `HasTy`）。`@mode!` が規則から検査器 `check` を作ります。成功には導出と出力型の一意性、拒否にはどんな型でも型付けできないことの反証が付きます。
3. **型安全性の証明**（`proof/safety.taut`）。手で書くのはここだけです。

```
text --tl::parse--> tl::Expr --to_i--> tl::Expr::I --lower_expr--> Term --check_ty--> Option(Ty)
 (証明なし)         (証明なし)          (inductive)     (全域な関数)          (mode! が作る)
                                                                     Term --eval--> Option(Val)
```

## 証明していること（公理なし）

- `check_sound` / `check_complete`: `check_ty(t) = Some(ty)` と `HasTy(t, ty)` は同値です。
- `typing_unique`: 型付けは一意です。
- `eval_safe`: `HasTy(t, ty)` なら、評価は必ず成功し、返る値は `ty` の型を持ちます（保存と進行）。
- `eval_never_stuck`: 型の付いた式の評価は `None` にならない。
- `run_term_safe`, `run_tree_safe`: 検査を通した実行（木からの実行を含む）も同じ性質を持つ。
- `proof/examples.taut`: 具体例と、拒否される式。`add_bool_untypable` は拒否が「型付けが存在しない」証明になることを示します。

```sh
tauto check --tote examples/typed-lang --fresh
tauto run --backend eval --tote examples/typed-lang
```

1 行ずつ式を入力する REPL です。空行は読み飛ばし、`:quit` または入力の終端で終了します。型エラーや構文エラーの後も次の式を入力できます。

```text
typed-lang REPL (:quit to exit)
> 1 + 2 + 3
6 : Nat
> if 1 + 1 == 2 then 10 else 20
10 : Nat
> (1 == 1) == true
rejected by the type checker
> 1 + true
rejected by the type checker
> if 1 then 2 else 3
rejected by the type checker
> if true then 1 else false
rejected by the type checker
> 1 + * 2
syntax error: macro.syntax_error: in tl: expected Num or KwTrue or KwFalse or LParen, found Error
> 2 + 3
5 : Nat
> :quit
```

## 保証されないこと

文字列から木を作る `tl::parse` と `tl::Expr::to_i` は証明の対象外です（`examples/calc` と同じ）。
`lower_expr` は全域な関数ですが、「文字列が表す式」との対応は証明していません。
評価器は Nat を数学の自然数として扱い、実行時の数値表現の上限は扱いません。

`import` の順は、`core.taut`（`@mode!`）を `syntax.taut`（`inductive_syntax!`）より先に書いてください。
