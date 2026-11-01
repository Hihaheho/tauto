# `tauto index` と、`add`・`update`・`lock` が通るゲートのメッセージ。

index-help =
    使い方: tauto index sync [--tote DIR]
    { "        " }tauto index status [--tote DIR]
    { "        " }tauto index check [NAME…] [--tote DIR]
    { "        " }tauto index new DIR [--name NAME]
    { "        " }tauto index observe (NAME [--locked] | --project ID --git URL [--branch NAME | --tag NAME]) [--index ALIAS] [--tote DIR]
    { "        " }tauto index decide (NAME | --project ID) (accept | reject) --reason TEXT [--rev REV] [--index ALIAS] [--tote DIR]
    { "        " }tauto index withdraw (NAME | --project ID) --reason TEXT [--rev REV] [--index ALIAS] [--tote DIR]
    { "        " }tauto index publish [--valid-for SECONDS] [--index ALIAS] [--tote DIR]

    { "  " }sync     Trust.eure が挙げる各インデックスを取得し、履歴を検査して、
    { "           " }新しいものを取り込む。インデックスが出すべきでなかったバッチや、
    { "           " }取り込み済みの部分の下で書き換えられた履歴があれば、
    { "           " }そのインデックスはここで以後ずっと止まる。
    { "  " }status   採用に何が要るか（ユーザーのポリシー込み）と、このマシンが
    { "           " }各インデックスについて持っているもの：どこまで取り込んだか、
    { "           " }ピン、最後に origin を確かめた時刻、止まっているかどうか。
    { "  " }check    Git 依存（または NAME）のロックされたコミットを、いま
    { "           " }Trust.eure のもとで採用できるか、できないならその理由。
    { "           " }先に `sync` を実行すること。

    { "  " }自分のインデックスを持つ（Trust.eure の local-owned なインデックス）:
    { "  " }new       空のディレクトリ DIR にインデックスを始め、Trust.eure に書く
    { "            " }項目を表示する。
    { "  " }observe   Git 依存 NAME の最新のコミット（--locked ならロックされたコミット）、
    { "            " }またはまだ依存でないプロジェクトのブランチかタグの最新のコミットと、
    { "            " }そのソースツリーを、書きかけのバッチに記録する。
    { "  " }decide    リビジョン（REV、なければ最後に observe したもの）を accept または reject する。
    { "  " }withdraw  リビジョンを以後ずっと取り消す。
    { "  " }publish   書きかけのバッチ（なければ、インデックスを有効に保つ空のバッチ）を
    { "            " }--valid-for 秒のあいだ有効なものとしてコミットする。指定がなければ 1 日。

    Trust.eure はプロジェクトの Tauto.eure の隣に置く。これがあると、add・update・lock は
    Git 依存の新しいコミットを、挙げられたインデックスが許すときにだけ採用し、
    どの Git 依存も自分の `project` を書かなければならない。取り込んだものは
    $TAUTO_INDEX_STATE（なければ ~/.local/state/tauto/index）に保存される。

    ユーザーのポリシー $TAUTO_USER_TRUST（なければ ~/.config/tauto/trust.eure）は、
    どのプロジェクトの Trust.eure にも上乗せされる：observer と年齢の証人を増やし、
    待ち時間を延ばし、上限を縮める。これがなければ安全な既定が適用される：
    Trust.eure の待ち時間にかかわらず、リビジョンは observe されてから 14 日後にだけ採用される。
    ユーザーのポリシーに `min_age_seconds = 0` と書けば、Trust.eure のとおりにだけ待つ。
index-takes-no-argument = { $command } は引数をとらない
index-unknown-command = 未知のコマンド index { $command }
index-command-error = tauto index { $command }: { $error }
index-usage-error = tauto index: { $error }
index-tote-needs-dir = --tote にはディレクトリが必要である
index-user-default = 安全な既定
index-user-default-no-file = 安全な既定（{ $path } がないため）
index-file-error = { $path }: { $error }
index-strengthen-error = { $path }（{ $user } を加えたもの）: { $error }
index-trusts-no-index = { $dir } に { $file } がない。信頼するインデックスはない
index-no-policy = { $dir } に { $file } がない
index-syncing = インデックス { $alias } を同期している
index-syncing-from = インデックス { $alias } を同期している（{ $url } { $reference }）
index-sync-nothing-new = 新しいものはない
index-sync-new-batches = 新しいバッチ { $n } 個
index-stopped = 停止: { $why }
index-sync-failed = インデックス { $alias }: { $line }
index-requires = observer: { $observers }、年齢の証人: { $witnesses }、待ち時間: { $wait }、チェックポイントの有効期間: { $lifetime }、origin の確認: { $check } 以内
index-status-user = ユーザーのポリシー: { $policy }
index-status-every = すべてのプロジェクト: { $requires }
index-status-project = プロジェクト sha256:{ $project }…: { $requires }
index-status-not-taken = 取り込まれていない。`tauto index sync` を実行すること
index-status-taken = 取り込み済み: { $rev } まで
index-status-pinned = ピン: { $rev }
index-status-checked-ago = origin の確認: { $ago } 前、{ $rev }
index-status-checked-future = origin の確認: { $time }（現在より後）
index-status-checked-never = origin の確認: なし
index-may-adopt = 採用できる
index-may-not-adopt = 採用できない:
index-not-locked = { $name } はロックされた Git 依存ではない
index-needs-project = { $name }: { $file } のもとでは、どの Git 依存も自分の project を書かなければならない（`project = "sha256:…"`）
index-not-allowed = インデックスが許していない
index-wait-from = （{ $wait } の待ち時間は { $user } によるもの。{ $file } の待ち時間は { $own }）
