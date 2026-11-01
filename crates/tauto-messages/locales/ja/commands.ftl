# プロジェクトのトートが与えるコマンド（`tauto NAME`）のメッセージ。

# 名前の並びをつなぐ語。
commands-and = {"、"}
commands-trust-wrong-tote = `Tauto.eure` の `trust.commands.{ $name }` はトート { $tote } を指すが、そのトートはコマンド { $name } を与えない{ $givers }
commands-givers = （与えるのは { $totes }）
commands-ambiguous =
    トート { $totes } がそれぞれコマンド { $name } を与えている。`Tauto.eure` でひとつを選ぶ:
    {"  "}{ $snippet }
commands-unread-dependencies =
    コマンド { $name } がない。次の依存を読めなかった:
    {"  "}{ $unread }
commands-bad-trust = `Tauto.eure` の `trust.commands.{ $name }`: { $error }
commands-denied = { $tote } のコマンド { $name } は実行に { $kinds } を必要とするが、ホストは既定でこれを拒否する
commands-denied-add = { $file } の `trust.commands.{ $name }` に、使ってよいものだけを挙げて加える:
commands-denied-grant = { $file } で、使ってよいものだけを挙げて許可する:
commands-help-head = { $path } のプロジェクトのコマンド:
commands-help-not-read = {"  "}未読: { $item }
commands-state-built-in = 実行されない: tauto に同名の組み込みコマンドがある
commands-state-granted = 許可 { $kinds }
commands-state-granted-nothing = 許可なし
commands-state-other-tote = 実行されない: 別のトートの同名コマンドが実行される
commands-state-ambiguous = 実行されない: 複数のトートが与えている。`trust.commands` でひとつを選ぶ
commands-given-built-in = （実行されない: tauto に同名の組み込みコマンドがある）
