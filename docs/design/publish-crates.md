# Rust crate の公開計画

`tauto publish-crates` は既存の Cargo workspace の公開を、計画・検査・送信に分ける。
Tauto から Rust crate を生成する操作ではない。マニフェストのバージョンをそのまま
使い、変更・コミット・タグ・Git の push・公開済みバージョンの yank は行わない。
複数 package を扱う package・publish 機能を備えた Cargo を必要とし、対応しない
Cargo の失敗を独自の依存解決や送信処理に置き換えない。

## 計画

`plan` は `--manifest-path`、`--registry`、`--out` と、`--workspace` または
`-p` による明示的な package 選択を必要とする。公開先の暗黙の既定値は使わない。
`publish = false` の package は workspace 選択から除外され、個別選択なら拒否される。
マニフェストの公開先制限と選択された registry が一致しなければ拒否する。

計画ファイルと隣接する release ディレクトリは、ソース workspace の外に保存する。
既存の計画や release ディレクトリは上書きしない。Unix では release directory を
所有者のみアクセス可能にし、計画と状態ファイルも所有者のみ読み書き可能にする。計画には固定バージョン、対象と
除外理由、package のファイル一覧、ソースのハッシュ、Cargo の実行ファイル・設定・
関連環境の識別情報を保存する。認証トークンは保存しない。

ソースは専用 snapshot にコピーする。Git 管理下では tracked ファイルだけを扱い、
未コミットの変更と未追跡ファイルを拒否する。snapshot のファイル走査は ignored
ファイルを読み取らない。ただし Cargo の初期 metadata 読み込みは ignored 設定を
解釈する場合があり、その設定が snapshot に含まれなければ計画を拒否する。
Git のないディレクトリでは通常ファイルを対象とする。どちらも symlink・特殊ファイル・
既知の認証情報らしいパスを拒否する。これは秘密検出器ではないため、公開対象の
ファイル一覧は利用者が確認する。Git の管理情報はコピーせず、package の
`.cargo_vcs_info.json` も含めない。それ以外の package ファイル一覧は元ソースと
snapshot で一致しなければならない。

workspace の外を指す path 依存、および workspace 外の祖先ディレクトリの
Cargo 設定は拒否する。workspace 内と Cargo home の設定は利用できる。
設定の include と quoted・escaped key は保守的に拒否する。設定の key 左辺や table
header に quote・backslash・`include` を認めない subset を扱い、multiline string 等の
誤検出も自動的に通過させない。外部設定の変更を追跡できないまま送信しないためである。
Git ignored な workspace 設定が snapshot から欠落する場合も拒否する。
設定・環境・ソースの変更後は、別の計画を作り直して確認する。

`plan` は Cargo を offline・locked で呼び、依存取得も公開も行わない。
キャッシュ不足や Cargo が解釈できない設定を別の registry へ切り替えて回避しない。
これは OS の network sandbox ではなく、toolchain の起動機構など外部の動作までは隔離しない。

## 検査

`check` は snapshot に対して Cargo の offline・locked な package 検査を実行する。
Cargo が package を作り、その展開内容をビルドして検証する。registry のオンライン公開可否や既存バージョンは、この検査では確認しない。構文表や
`include_text` 等の資源もファイル一覧で確認し、ビルドが必要とする資源が archive に
ない場合は検査に失敗する。実行時だけ参照する任意の資源の完全性までは推論しない。

検査は build script やコンパイラを実行する。「アップロードしない」は
「任意のコードを実行しない」という意味ではない。Cargo の offline 指定は、
build script のネットワークアクセスを sandbox するものではない。
信頼して実行できるソースと Cargo 設定だけを入力にする。

検査後に package archive のハッシュを保存する。`apply` は再度同じ検査を行い、
ソース・設定・ファイル一覧・archive が変わっていれば送信しない。
非決定的な archive を自動的に許容したり、新しいハッシュへ追従したりしない。

## 送信と再開

`apply` と `resume` は `--confirm` に、レビューした計画の完全なハッシュを必要とする。
確認なしの送信や汎用的な同意フラグは受け付けない。認証は Cargo に委譲し、
Tauto はトークンの入力・設定・保存を行わない。registry 名は必ず Cargo に渡す。

送信前に状態を `submitted-unknown` として永続化する。Cargo の workspace 公開に
依存順序と upload・公開確認を委譲し、成功時だけ `cargo-confirmed` を記録する。
全体は atomic ではない。失敗・timeout・中断のとき、一部だけが公開済みであり得る。
Cargo の人間向け出力から未送信を推測しない。認証 provider や build script の秘密が
混入し得るため、Cargo の出力を保存したりそのまま診断へ転記したりしない。

`resume` は確認済みの計画を再送しない。結果不明の計画は自動再送せず停止する。
registry の読み取り専用確認で版と checksum を照合し、確実に未送信の package だけを
別の計画としてレビューする必要がある。この操作は registry API の自動照合を実装しない。
状態ファイルをリセットして再送する運用はしない。中断時に残る lock は、送信状態を
確認してから手動で取り除く。

Cargo は既成 archive を受け取って公開するのではなく、送信時に再度 package を作る。
Tauto は固定 snapshot と送信直前の archive 一致を検査し、送信後にも一致を確認する。
送信後の検査は異常の**検出**であり、既に行われた upload を防止・取消できない。
敵対的な build script、同じ権限を持つ並行 writer、toolchain や環境全体の隔離を
保証しない。Cargo 本体の識別は、Rust toolchain 全体の暗号学的な固定とは異なる。

コマンドの回帰テストはローカルの偽 Cargo で送信状態を確認する。実 registry に
テスト用 crate を公開しない。
