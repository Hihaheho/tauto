# Macro expansion (`tauto-macro`). The error code (`macro.unknown`) is
# written before the message, outside it.

# An error with its code before it: `macro.unknown: …`.
macro-coded = { $code }: { $message }
macro-reserved = { $name } は読み込みが処理する `{ $name }!` である。マクロはこの名前を取れない
macro-duplicate = マクロ { $name } が二度宣言されている
macro-dollar-outside-quote = $ は quote の中にだけ書く
macro-kind-statements = このマクロは文を作るが、文を書く場所で呼ばれていない
macro-replace-word = `{ $kind } { $name }` の前に `{ $word }` がある。宣言を変える属性は先頭に `replace` と書く
macro-the-declaration = その宣言
macro-replace-other = `replace { $kind } { $name }` は属性が前に書かれていない宣言を指している。属性は { $decl } の前にある
macro-generates-attribute-kinds = 属性マクロが作るのは fn、theorem、def、inductive、struct、enum の宣言だけである
macro-replace-not-made = 属性は `replace { $kind } { $name }` と言うが、マクロはそれを作らなかった
macro-replace-unsaid = マクロは与えられた宣言 `{ $kind } { $name }` を作っている。宣言を変える属性は `=> replace { $kind } { $name }` と書く
macro-attribute-list-mismatch = 属性の一覧がマクロの作ったものと合わない
macro-call-list-mismatch = 呼び出しが作るものの一覧が実際に作ったものと合わない

# The function of a macro.
macro-function-undefined = マクロ { $name } の関数 `{ $function }` はこのファイルより前に定義されていない
macro-function-left-out = マクロ { $name } の関数 `{ $function }` はこのファイルより前に定義されていない。検査を通らない ({ $why })
macro-function-not-fn = `{ $function }` は関数ではない
macro-function-arity = マクロの関数は syntax の木 (属性マクロでは、さらに前に書かれた SynStmt) を取るが、`{ $function }` は { $count } 個を取る
macro-function-not-start = `{ $function }` は { $ty } を取るが、これは syntax の開始記号の木ではない
macro-function-not-tree = `{ $function }` は { $ty } を取るが、これは syntax の木ではない
macro-function-result = `{ $function }` は { $ty } を作る。マクロが作るのは SynExpr か List(SynStmt) である
macro-unchecked-effect = `{ $function }` は追跡できないエフェクトを行う ({ $effect })
macro-row-effect = マクロの関数が行えるのは macro_error、macro_warn、elab、Div だが、`{ $function }` は { $effect } を行う
macro-row-reached = `{ $function }` は { $path } に到達するが、その row は検査を通らない: { $why }

# Why a function was left out of the library a macro runs in.
macro-left-out-inductive-ctor = { $why }。`{ $name }` は `inductive` の構築子だが、マクロの関数は実行コードであり、`inductive` ではなく `enum` の構築子 (`List` の `Nil`/`Cons`、`Option` の `None`/`Some`) を使う
macro-left-out-means = `{ $short }` は `{ $name }` である
macro-left-out-builtin = { $why }。このファイルでは { $means }。マクロの関数が使う組み込みではない。組み込みには { $builtins } と書くこと
macro-left-out-because = { $why }。`{ $name }` が検査を通らないためである: { $reason }

# A call.
macro-include-text = `{ $name }!` はファイルに書かれた場所で読み込まれる。マクロはこれを作れず、ファイルなしで読むテキストはこれを含めない
macro-unknown = `{ $name }` という名前のマクロはない
macro-same-file = マクロ { $name } はこのファイルで宣言されている。マクロは宣言したファイルより後のファイルで使う
macro-depth-exceeded = マクロの展開が { $depth } 段より深くなった ({ $chain })
macro-library = このファイルより前のファイルにエラーがあるため、マクロは実行されない ({ $problem })
macro-kind-attribute = マクロ { $name } は属性マクロである。宣言の前の行に `@{ $name }!(…)` と書く
macro-kind-not-attribute = マクロ { $name } は属性マクロではないが、属性として書かれている
macro-kind-attribute-stmts = マクロ { $name } は属性マクロであり、List(SynStmt) を作る
macro-argument-tactic = マクロ { $name } はタクティクである。`by { $name }!(…): G {"{"} … {"}"}` と呼ぶ
macro-argument-expr = マクロ { $name } が取るのは式であり、syntax リテラルではない
macro-argument-literal = マクロ { $name } は syntax リテラルを取る
macro-input-too-large = テキストが { $bytes } バイトを超えている
macro-syntax-mismatch = マクロ { $name } が読むのは { $syntax } だが、リテラルは { $literal } である
macro-expand-exceeded = マクロ { $name } が { $count } 個を超える式の展開を求めた
macro-file-budget = このファイルのマクロが { $steps } ステップを超えた
macro-output-too-large = マクロ { $name } が { $nodes } 個を超えるノードを作った
macro-proved-untyped = Proved は証明の中の型付きマクロのためのものである
macro-forbidden-output = マクロは { $what } を作れない。手で書くこと
macro-forbidden-axiom = axiom
macro-forbidden-extern = extern
macro-forbidden-import = import
macro-forbidden-syntax = syntax
macro-forbidden-macro = マクロ
macro-syn-expand = Syn::expand: { $message }
macro-budget = マクロ { $name } が { $steps } ステップを超えた
macro-memory = マクロ { $name } が { $values } 個を超える値を作った
macro-not-allowed = マクロ { $name } が { $builtin } を呼んだ。マクロはこれを呼べない
macro-runtime = マクロ { $name }: { $message }

# Typed macros.
macro-nested-typed = 型付きマクロの呼び出しは別の呼び出しの引数の中に書かない
macro-fragment = 型付きマクロは実行コードか証明の中で動く。inductive family には対応していない
macro-output-not-check = マクロが作ったものが検査を通らない: { $message }
macro-signature-changed = マクロの後で `{ $name }` のエフェクトが変わった
macro-ownership-rejected = マクロが作ったものが所有権を破る: { $message }
macro-code-no-goal = 式にマクロへ示す型がない ({ $message })
macro-code-no-type = `{ $name }` に型がない
macro-proof-rejected = マクロが作った証明が却下された: { $message }
macro-proof-incomplete = マクロが作った証明が完全でない
macro-dependent-use = 出力は呼び出しと同じ型を持つが定義的に等しくなく、下の型がその等しさに依存している ({ $message })
macro-output-rejected = マクロが作ったものが受け入れられない: { $message }
macro-output-rejected-plain = マクロが作ったものが受け入れられない
macro-proved-shape = Proved には項と証明がある
macro-proved-where = Proved は関数か定理のためのものである
macro-proof-no-type = 式に型がない
macro-proof-type-unwritable = 式の型をカーネル向けに書けない
macro-type-changed = マクロが式の型を { $before } から { $after } に変えた
macro-row-grew = マクロが式にエフェクト { $effect } を加えた

# `elab_*`.
macro-elab-more-arguments = { $op } にはもっと引数が要る
macro-elab-check-kernel = Elab::check はカーネルの断片のためのものである
macro-elab-unknown-op = { $op } は検査器の操作ではない

# Steps of a proof.
macro-step-mutual = step は `mutual` ブロックの中に書かない
macro-step-fragment = step は定理、`def`、カーネルの言語の関数の中に書く
macro-step-nested = tactic の出力に step は書けない（腕ごとに穴を一つ持つ項を作る）
macro-step-typed-argument = 型付きマクロの引数の中の step を展開した後、引数が見つからない
macro-step-library = このファイルより前のファイルにエラーがあるため、タクティクは実行されない ({ $problem })
macro-step-context = step を除いた宣言が検査を通らない: { $message }
macro-step-no-goal = step の場所にゴールがない
macro-step-before-mismatch = 書かれたゴールがここのゴールではない: ここは `{ $here }`、書かれたのは `{ $written }` ({ $why })
macro-step-holes = step のアームは { $arms } 個だが、タクティクが残した穴は [{ $holes }] である。`?arm1` … `?arm{ $arms }` をそれぞれ一度ずつ残すこと
macro-step-output-rejected = タクティクが作ったものが受け入れられない: { $message }
macro-step-hole-no-goal = タクティクが残した穴 `?arm{ $k }` にゴールがない
macro-step-arms =
    タクティクは { $count } 個のゴールを残す。step のアームは次の通り:
    { $arms }
macro-step-binders-mismatch = アーム { $k }: タクティクが加えるのは [{ $added }] だが、アームは [{ $written }] と書いている
macro-step-binder-type = アーム { $k }: `{ $name }` は `{ $ty }` だが、アームは `{ $written }` と書いている ({ $why })
macro-step-goal-mismatch = アーム { $k }: タクティクが残すのは `{ $left }` だが、アームは `{ $written }` と書いている ({ $why })
macro-step-not-checked = 検査されていない
macro-step-not-tactic = マクロ { $name } はタクティクではない。その関数は ProofStep を取って SynExpr を作るものではない
macro-step-write-before = step の始まりのゴールを書くこと: `by t!(…): G {"{"} … {"}"}`
macro-step-arm-before = アームのゴールはそれを証明する step のゴールである。`: …` は書かない

# A text that is not of a syntax (`macro.syntax_error`).

macro-syntax-not-a-token = { $syntax } の中: この文字列は構文のトークンではない
macro-syntax-expected-found = { $syntax } の中: { $expected } が来るはずだが、{ $found } がある
macro-syntax-expected-end = { $syntax } の中: { $expected } が来るはずだが、テキストが終わった
macro-syntax-limit = { $syntax } の中: { $detail }
macro-syntax-schema = { $detail }
macro-syntax-tables = { $syntax } の中: 表が読めない: { $detail }
macro-syntax-embedded = 埋め込んだ式の中: { $detail }
macro-syntax-terminal = { $name }
macro-syntax-or = { $first } か { $rest }
macro-syntax-something-else = 別のもの
