# The messages of reading a program (tauto-surface): syntax declarations,
# modules, visibility, effect sets and quotes. `macro.…` codes stay as they are.

surface-tables-missing = この syntax の表がない (文法 { $grammar }…)。`tauto syntax gen` を実行すること
surface-tables-of-another-grammar = { $path } は別の文法の表である。`tauto syntax gen` を実行すること
surface-tables-out-of-date = { $path } は古い表の生成器で作られている。`tauto syntax gen --force` を実行すること
surface-grammar-not-par = syntax { $name } の文法は par という名前のブロックで書く
surface-syntax-declared-twice = syntax { $name } が二度宣言されている
surface-inductive-syntax-ctor-taken = `{ $ty }::{ $ctor }` は `{ $ty }` の構成子であり、`inductive_syntax!` は `{ $ty }::I` と `{ $ty }::to_i` を作る。文法の規則に別の名前を付けること
surface-inductive-syntax-hole-place = `{ $ty }` で穴 (`TautoExpr`) が選択肢そのものになっていない。`inductive_syntax!` の穴は、それを選択肢とする非終端記号の代わりである
surface-syntax-start-tables = `{ $name }` の開始記号 `{ $start }` の表が別の記号のものになっている。`tauto syntax gen --force` を実行すること
surface-syntax-error = syntax { $name }: { $error }
surface-syntax-generates-mismatch = syntax { $name }: 作るものの一覧が実際に作ったものと合わない
surface-made-not-listed = { $before }。作ったが一覧にない: { $items }
surface-listed-not-made = { $before }。一覧にあるが作っていない: { $items }
surface-syntax-with-role = syntax { $name }: `with` が登録するのは `fmt` と `tokens` であり、`{ $role }` ではない
surface-syntax-registered-twice = syntax { $name }: `{ $role }` が二度登録されている
surface-not-a-syntax = `{ $name }` は syntax ではない
surface-literal-needs-name = syntax リテラルには name`…` のように syntax の名前が要る。テキストには plaintext`…` と書くこと
surface-effect-set-generic = エフェクト集合 { $name } に型パラメータがある。エフェクト集合はまだ型パラメータを取らない
surface-effect-set-names-itself = エフェクト集合 { $name } が自分自身を含む: { $path } -> { $name }
surface-module-collides-with-class = module { $module } が class { $name } と衝突する
surface-module-declared-twice = module { $name } が二度宣言されている
surface-dot-names-a-declaration = `.` はフィールドの取り出しだけに使う。宣言の名前は `::` で書く：`{ $name }`
surface-name-of-a-module = { $name } は module の名前である。`{ $name }.f` がフィールドか修飾名か区別できないので、局所変数には別の名前を付ける
surface-name-shadowed = { $name } がここでは複数の宣言を指す：{ $names }。意図する宣言を module の道筋（`M::{ $name }`）で書くこと
surface-name-shadows-outer = { $name } がここでは { $inner } と module の外の宣言の両方を指す。module の宣言は `{ $inner }` と書き、外の宣言を使うときは module の宣言を改名すること
surface-name-outer-not-imported = { $name } は module の宣言 { $inner } として読む。module の外に同じ名前の宣言がプログラムにあるが、このファイルはそのファイルを import していない。外の宣言のつもりなら、そのファイルを import して module の宣言を改名すること。{ $inner } のつもりなら `{ $inner }` と書くこと
surface-block-indent = macro.block_indent: この行の字下げは { $lead }、閉じフェンスは { $indent } である
surface-extern-rust-path = extern {"{"} … {"}"} と書くこと。rust のパスは Tauto.eure に書く
surface-extern-mix-required-replaceable = 一つの `extern` ブロックに、必須のホスト署名と、置換可能な Tauto 本体や `struct`/`enum` を混在させないこと
surface-ctor-type-name = コンストラクタ `{ $name }` が型の名前を持っている。型とコンストラクタは一つの名前空間を共有するので、別の名前にする (`Mk{ $name }` など)
surface-extern-inductive-data = `{ $name }` を `extern` の中で `inductive` にはできない。通常の `struct` か `enum` と書くこと
surface-extern-open-replaceable = 置換可能な `extern` の `{ $name }` を `pub(open)` にはできない。表現はブロックの中に閉じる
surface-extern-repr-sealed = `{ $name }` は置換可能な extern の型である。その `extern` ブロック内の関数だけが、構築・射影・更新・パターンマッチできる
surface-extern-partial-bindings = 置換可能な extern ブロック `{ $block }` のホストバインディングが一部だけである。メンバーをすべてバインドするか、どれもバインドしないこと
surface-extern-mixed-backends = 置換可能な extern ブロック `{ $block }` で、同じ表現に JavaScript と Rust/Wasm のバインディングを混在させないこと
surface-class-method-body = class のメソッドは署名だけである。本体は `class` ではなく `instance` に書くこと
surface-expected-one-expression = 式が一つであるべきだ
surface-pub-before-statement = { $what }: `pub` と `pub(open)` は `fn`、`theorem`、`axiom`、`def`、`inductive`、`struct`、`enum`、`effect`、`class` の前に書く。`syntax`、`macro` などの文はどのファイルからも見える
surface-the-file = ファイル `{ $file }`
surface-the-prelude = prelude
surface-names-and = { $before } と { $name }
surface-ambiguous = `{ $name }` は曖昧である: { $names } として宣言されている。完全な名前を書くこと
surface-ambiguous-prelude = `{ $name }` は曖昧である: { $names } として宣言されている。完全な名前を書くか、意図した宣言のあるファイルを import すること
surface-ambiguous-imported-prelude = `{ $name }` は曖昧である: { $names } として宣言されていて、このファイルはどちらも import している。完全な名前を書くか、`import { $module } {"{"} … {"}"}` のように、そのファイルから使うものだけを `import { $module }` の後に並べること
surface-ambiguous-constructor = `{ $name }` は曖昧である: 複数の型のコンストラクタ（{ $names }）で、ここで期待される型からはどれか決まらない。型を付けて `T::{ $name }` と書くこと
surface-ambiguous-language-type = `{ $name }` は曖昧である: { $names } として宣言されている。型には `std::prelude::{ $name }` と書き、もう一方は `T::{ $name }` のように型を付けて書くこと
surface-not-imported = `{ $name }` は `{ $module }` で宣言されているが、このファイルはそれを import していない（ほかのファイルや依存が import したものは、このファイルには届かない）。このファイルに `import { $spelling }` を書くこと
surface-ctor-in-std = `{ $name }` は定義されていない。標準ライブラリにある: `import { $spelling }`
surface-ctor-not-imported = `{ $name }` は `{ $module }` で宣言されているが、このファイルはそれを import していない（ほかのファイルや依存が import したものは、このファイルには届かない）。このファイルに `import { $spelling }` を書くこと
surface-private = `{ $name }` は { $file } で private である。別のファイルから使うには、そこで宣言の前に `pub` を書くこと
surface-private-std = `{ $name }` は標準ライブラリで `pub` ではないため、ライブラリ自身のファイルからしか使えません
surface-sealed-constructor = `{ $name }` は `{ $ty }` のコンストラクタであり、{ $file } はこの型を `pub(open)` なしで宣言している: そのファイルの外では型は抽象的である。公開されている関数を使うこと
surface-sealed-field = `{ $field }` は `{ $ty }` のフィールドであり、{ $file } はこの型を `pub(open)` なしで宣言している: そのファイルの外では型は抽象的である。公開されている関数を使うこと
surface-sealed-perform = `{ $name }` は `pub(handle)` で宣言されているため、宣言スコープ内でのみ perform できる
surface-sealed-effect = `{ $name }` は { $file } が `pub(open)` なしで宣言したエフェクトである: それを処理できるのはそのファイルだけだ。ここでは perform し、答えはそのファイルのハンドラに任せること
surface-sealed-class = `{ $name }` は { $file } が `pub(open)` なしで宣言したクラスである: その instance を書けるのはそのファイルだけだ。そのファイルが書いた instance を使うか、そこで `pub(open)` にすること
surface-private-class-bound = `{ $function }` は `pub` だが、その `where` が、このファイルが `pub` なしで宣言したクラス `{ $name }` を書いている: ほかのファイルはこれを満たせない。クラスに `pub` を付けるか、関数を private にすること
surface-sealed-extern = `{ $name }` は tote { $tote } の extern であり、呼べるのは { $tote } だけだ。{ $tote } がそれを包んで書く関数を呼ぶこと
surface-not-a-constructor-of = `{ $name }` は照合する値の型 `{ $ty }` のコンストラクタではない。{ $names } として宣言されている
surface-quote-spread-expr = `{ $name }` はリストの値を展開するもので、リストが来る場所 (呼び出しの引数、λ のパラメータ、コンストラクタのパターンの引数、文) にだけ書ける
surface-quote-spread-pattern = `{ $name }` はリストの値を展開するもので、リストが来る場所 (コンストラクタのパターンの引数) にだけ書ける
surface-quote-splice-outside = $ は quote の中にだけ書ける
surface-quote-in-quote = quote の中に quote は書けない
surface-quote-syntax-literal = quote の中に syntax リテラルは書けない。マクロを呼ぶこと
surface-quote-row = quote の中にエフェクト行の引数は書けない
surface-quote-ascribe = quote の中にはまだ型注釈 `(e: T)` を書けない
surface-quote-other = quote の中にはまだ { $what } を書けない
surface-quote-field-assign = マクロはまだフィールドへの代入 (`x.f := v`) を取れない
surface-quote-deref-assign = マクロはまだ借用の指す先への書き込み (`*x := v`) を取れない
surface-quote-statement = この文は quote の中に書けない
surface-quote-pattern = パターン { $what } は quote の中に書けない
surface-scope-extrusion = macro.scope_extrusion: アトム { $atom } が、それを開いた束縛子の外で使われている
surface-bare-kind = 種別 `{ $kind }` は `{ $written }` と書く
surface-old-effect-operation = effect の操作は `effect ask(question: Text): i64` と、引数を括弧に、結果の型を `:` の後ろに書く
surface-row-variables = 行に書ける行変数は高々一つ
surface-row-repeats-effect = 集合のリテラルに effect `{ $name }` が二度書かれている
surface-row-variable-in-literal = `{ $name }` は行変数で、effect ではありません: 波括弧の外に書いてください。例: `{"{"}trace{"}"} ∪ { $name }`
surface-raw-underscore = `r#_` は名前ではない：`_` は生の名前として書けない
surface-underscore-not-name = `_` は名前ではない。名前を書き、意図的に未使用なら `^name` と印を付ける
surface-unused-marker-wild = `^_` は書けない：`_` は名前ではない。本物の名前で `^name` と書く
surface-unused-marker-pub = `pub` 宣言に `^` は書けない。未使用表明はこのファイルで検証できる束縛向けである
surface-unused-marker-not-binding = `^` は束縛名にだけ書く。パターンのコンストラクタ名やフィールド名には付けない（`Some(^x)`、`Point {"{"} x: ^y {"}"}`）
surface-unused-marker-record-type = `^` は struct が宣言するフィールドにだけ書く。レコード型のメンバーには付けない
surface-syntax-macro-shape = `{ $macro }` は名前と文法のブロックを取り、関数を登録するときは `with(fmt: f, tokens: g)` を取る
surface-import-not-listed = `{ $name }` は `import { $spelling }` から来るが、その一覧に書かれていない。一覧に `{ $item }` を書くこと（`tauto lint --fix` が一覧を書く）
surface-import-listed-unused = `{ $name }` は `import { $spelling }` の一覧にあるが、このファイルは使っていない。一覧から除くこと（`tauto lint --fix` が一覧を書く）
surface-import-listed-unknown = `{ $name }` は `import { $spelling }` の一覧にあるが、import したファイルは他のファイルに見える `{ $name }` を宣言していない
surface-import-misplaced = `import` はファイルの最上位か、そこに書いた `fn`・`macro fn`・`theorem`・`def` の本体の先頭（本体のほかの文より前）にだけ書ける

surface-break-outside-loop = `break` は `loop`・`while`・`for` の中にだけ書ける
surface-continue-outside-loop = `continue` は `loop`・`while`・`for` の中にだけ書ける
surface-break-value = `break` は値を取らない（ループの値は `()`）。結果は前もって `var` に入れる
surface-return-in-for = `for` の中に `return` は書けない。ループを抜けるには `break` を使い、関数の残りは `for` の後に書く
surface-pair-written = `Pair` は名前で書かない。直積は `A × B` と `#(a, b)` で書き、`#(…)`・成員の型・`.fst` と `.snd` で取り出す
surface-coerce-twice = struct が持てる `coerce` のフィールドは一つだけ
surface-coerce-not-in-struct = `coerce` は `struct` のフィールドの前に書く。`enum` のコンストラクタやレコード型のフィールドには書けない
surface-coerce-level = `coerce({ $word })` という段階はない：`coerce`、`coerce(mut)`、`coerce(owned)` のどれかを書く
surface-row-hole-place = `!?`（まだ書いていない行）は本体を持つ `fn` の結果の後にだけ書ける。型・`effect`・`extern`・クラスの中には書けない
surface-unused-effect-marker-place = `^` で未使用のエフェクトを印すのは関数の書いた行だけで、関数型・行引数・エフェクト集合には書けない

surface-single-superclass = クラスが宣言できる親クラスは一つです
surface-superclass-argument = 親クラスの引数は子クラスの唯一の型パラメータでなければなりません
surface-unknown-superclass = 親クラス `{ $name }` が見つかりません
surface-superclass-kind = 親クラス `{ $name }` はパラメータの種とクラスの形式が子クラスと同じでなければなりません
surface-superclass-cycle = `{ $name }` の親クラスに循環があります

surface-module-duplicate = モジュール `{ $name }` は既に宣言されている

surface-module-unknown = ローカルモジュール `{ $name }` が見つからない

surface-module-export = `{ $name }` はモジュールの公開メンバーではない

surface-module-member-private = `{ $name }` はモジュール内に限り参照できる

surface-module-sealed-handle = `{ $name }` は宣言したモジュール内でのみ handle できる

surface-module-export-duplicate = `{ $name }` は複数回再公開されている
