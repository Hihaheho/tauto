# `--timings` of `tauto build` and `tauto check`. Statuses, backends, targets,
# phase names and cache states stay as they are.

timings-heading = ビルドの所要時間（{ $status }; { $backend } / { $target }; 実時間）:
timings-total = 合計
timings-generated-sources = 生成したソース: 変更なし { $unchanged } 件、書き込み { $written } 件（内容の一致で判定）
timings-generated-unknown = 生成したソースの再利用: 不明
timings-native-cache = ネイティブのキャッシュ: { $cache }
timings-proof-cache = 証明のキャッシュ: { $cache }
