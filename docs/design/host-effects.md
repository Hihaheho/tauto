# 標準エフェクトと権限

プログラムが実行環境（ホスト）に求めることは、すべて `std/prelude/Os.taut` の effect として行に出る。型を見れば、関数が標準出力に書くのか、ファイルを読むのか、ネットワークに出るのかがわかる。ホストへの権限は既定で拒否し、実行時に `--allow-*` で与える（[`nib.md`](nib.md)「原則」の Safe by Default）。

## 効果

| effect | 再開 | 権限 |
|---|---|---|
| `stdout(t)`, `stderr(t)` | direct | 不要 |
| `stdin(): Option(Text)`（改行を除いた一行、終わりで `None`） | direct | 不要 |
| `stdin_bytes(max): Bytes`（標準入力の先頭から、届き次第 `max` バイトまで。終わりでは空。行の区切りを見ない） | direct | 不要 |
| `stdout_flush(): Unit`（それまでの `stdout` と `stderr` を書き出す） | direct | 不要 |
| `shutdown_token(): CancelToken`（外から実行の終わりを求められると要求が立つトークン。[終了の要求](#終了の要求)） | direct | 不要 |
| `argv(): List(Text)` | direct | 不要 |
| `exit(code): Never` | 0 | 不要 |
| `stop(message): Never`（続けられない値で止まる。どのハンドラも答えなければ `message` を実行時エラーとして終わる） | 0 | 不要 |
| `wall_clock(): i64`（Unix 紀元からのミリ秒）, `monotonic_clock(): i64`（ナノ秒、戻らない） | direct | 不要 |
| `sleep(ms)` | 1 | 不要 |
| `wait(signal)`（`std/prelude/Par.taut` の効果。`Signal` が上がるまで待つ。タスクの終わりや `Mutex` の中身の受け渡しを待つ、ただ一つの効果。`pub` で、ホストだけが答える） | 1 | 不要 |
| `random(): u64`（2^63 未満の 63 ビット。秘密には使わない） | direct | 不要 |
| `secure_random(n): Result(Secret(Bytes), IoError)`（OS の暗号論的に安全な乱数源から `n` バイト。鍵・トークン・ソルト用） | direct | 不要 |
| `fs_read(path): Result(Text, IoError)` | direct | `read` |
| `fs_write(path, contents): Result((), IoError)` | direct | `write` |
| `fs_read_bytes(path): Result(Bytes, IoError)` | direct | `read` |
| `fs_write_bytes(path, contents): Result((), IoError)` | direct | `write` |
| `fs_read_under(root, path): Result(Text, IoError)`（下の「root の下だけを読む」） | direct | `read`（`root`） |
| `fs_read_bytes_under(root, path): Result(Bytes, IoError)` | direct | `read`（`root`） |
| `fs_create_dir(path): Result((), IoError)`（足りない親も作る。既にあるディレクトリは誤りにしない） | direct | `write` |
| `fs_list_dir(path): Result(List(Text), IoError)`（ディレクトリにある名前をバイト順で。`.` と `..` は含まない） | direct | `read` |
| `fs_remove(path): Result((), IoError)`（ファイル、またはディレクトリとその中身すべてを消す） | direct | `write` |
| `fs_stat(path): Result(Option(FileStat), IoError)`（下の「ファイルの情報と移動」） | direct | `read` |
| `fs_read_link(path): Result(Option(Text), IoError)`（下の「リンクそのものを見る・リンクをたどらずに作る」） | direct | `read`（リンクそのもの） |
| `fs_write_new(path, contents): Result((), IoError)`（同上） | direct | `write`（作るファイルそのもの） |
| `fs_rename(src, dst): Result((), IoError)` | direct | `write`（両方のパス） |
| `fs_copy(src, dst): Result((), IoError)` | direct | `read`（`src`）と `write`（`dst`） |
| `fs_canonicalize(path): Result(Text, IoError)` | direct | `read` |
| `fs_temp_dir(): Result(Text, IoError)`（下の「一時ディレクトリ」） | direct | 不要 |
| `proc_run(process): Result(ProcessOutput, IoError)`（下の「プログラムの実行」） | direct | `run` |
| `proc_spawn(process, io): Result(Child, IoError)`（下の「走らせたまま進むプログラム」） | 1 | `run` |
| `proc_read(child, which, max, deadline): Result(Bytes, IoError)` | 1 | 不要（起動した `run` の中） |
| `proc_write(child, bytes): Result((), IoError)`, `proc_close_stdin(child)` | 1 | 不要（同上） |
| `proc_wait(child, deadline): Result(Option(u64), IoError)` | 1 | 不要（同上） |
| `proc_close(child): Unit` | 1 | 不要（同上） |
| `env(name): Result(Option(Text), IoError)` | direct | `env` |
| `permission(kind, target): Option(Text)`（下の「権限の検査」） | direct | 不要 |
| `net(request): Result(Response, IoError)` | 1 | `net` |
| `net_addr(request, address): Result(Response, IoError)` | 1 | `net` |
| `net_resolve(host): Result(List(Text), IoError)` | 1 | `net` |
| `tcp_listen(address): Result(TcpListener, IoError)` | 1 | `net` |
| `tcp_accept(listener, deadline): Result(TcpStream, IoError)` | 1 | `net` |
| `tcp_connect(address, deadline): Result(TcpStream, IoError)` | 1 | `net` |
| `tcp_read(stream, max, deadline): Result(Bytes, IoError)`（届いた分を最大 `max` バイト。終わりで空） | 1 | `net` |
| `tcp_write(stream, bytes: Bytes, deadline): Result((), IoError)`（すべて書く） | 1 | `net` |
| `tcp_shutdown(stream, how): Result((), IoError)` | 1 | `net` |
| `tcp_close(stream)`, `tcp_unlisten(listener)` | 1 | `net` |

`IoError` は `Denied(Text)`（権限が覆わない）、`Failed(Text)`（ホストが試みて失敗した）、`TimedOut`（与えた期限までに終わらなかった）を区別する。

`Request` と `Response` の本文は `Bytes`（送られたままのバイト列。`std/prelude/Shared.taut`）である。バイナリの本文が置き換え文字に化けて黙って届くことはない。テキストとして読むときは `Text::of_bytes` で UTF-8 を検査し、検査に落ちれば `None` になる。ヘッダの名前と値は `Text` のままで、UTF-8 でないヘッダ値は変えて渡さず、ホストがその応答を断る（`Err(Failed(..))`）。`print`、`eprint`、`read_file`、`write_file`（誤りを文字列にする）、`http_get` は、これらの effect を行う普通の関数である。

`secure_random` に権限が要らないのは、乱数源から読むことが何かへの到達を与えないからである（時計や `random` と同じ側）。それでも独立した effect なので、行を見れば秘密の乱数を使う関数がわかり、テストではハンドラで決まったバイト列に差し替えられる。返す `Secret(A)` は値を包む型で、`Show` や `Eq` の instance を持たないので、うっかり表示したり比べたりできない。作るのは `secret`、中身を取り出すのは `expose` で、どちらも明示して書く。

`sleep`、`wait`、`net` 系、`tcp` 系と `tls` 系が resume 1 なのは、答えを待つあいだホストがほかのタスクを進めるからである（「時間のかかる答え」）。

### サーバー

HTTP のサーバーは effect にしない。待ち受け、要求の読み取り、枠付け（`content-length` と chunked）、上限と期限は、`tcp_*` の上の Tauto のライブラリとして書く。ホストが要求を読む形では、要求を読み終える前に答える（ストリーミング）、上限や期限を変える、読み手の正しさを証明する、のどれもプログラムからできないからである。

### 名前解決

`net_resolve("example.com")` はホスト名が指すアドレス（`93.184.215.14` や `2606:2800:…` の文字列）を、重複を除きシステムが返した順に返す。`127.0.0.1` のようなアドレスはそれ自身に解決される。ポートは持たない。接続はしないが、どのホストに向かうかを外へ漏らす操作なので、`net` の権限で守る。

名前は `http://host/` として読み、権限はそのホストを見る。`--allow-net=example.com` は覆い、`--allow-net=example.com:8080` は覆わない（ポートを名指した権限はそのポートへの要求だけを許す）。ホストは **検査した URL のホスト** を解決する。JavaScript のホストは `options.os_resolve(host)` で答え、無ければ `Failed` になる。

### 解決したアドレスへの接続

`net(request)` はホストが接続のときに URL のホスト名を引くので、プログラムが `net_resolve` で得たアドレスを検査（内部アドレスでないか、など）してから `net` を行っても、その間に名前の指す先が変われば検査していないアドレスへ繋がる（DNS rebinding）。`net_addr(request, address)` は URL のホスト名を引き直さず、`address`（`net_resolve` が返す形の IP アドレス）へ接続する。`Host` ヘッダと TLS の名前（SNI と証明書の検証）は URL のホストのままなので、検査したアドレスに、名前を名乗って繋がる。IP アドレスでない `address` は `Failed` になる。

権限は URL を `net` と同じに検査し、加えて `address` を `http://address/`（IPv6 は角括弧で囲む）として検査する。`--allow-net` はどのアドレスも覆う。`--allow-net=example.com` のように名前で絞った権限では、アドレスを名指しても名前の権限で別のホストへ繋がることはできず、アドレスそのものを権限に書く必要がある。Rust のホストは HTTP クライアントにその名前の解決先として `address` を渡し、JavaScript のホストは `options.os_fetch_at(url, init, address)`（状態、本文、ヘッダの名前と値の並び）で答え、無ければ `Failed` になる。node の入口は `node:http` と `node:https` の `lookup` で答える。

### バイトのストリーム

`tcp_*` は TCP と Unix ドメインソケットのバイトのストリームで、HTTP などのプロトコルはこの上に Tauto のライブラリとして書く。アドレスは `HOST:PORT`（IPv6 のホストは角括弧で囲む）か `unix:PATH`。`tcp_listen` はポート 0 ならシステムが選んだポートを `TcpListener.address` で示し、`tcp_accept` と `tcp_connect` の `TcpStream` は自分のアドレス `local` と相手のアドレス `peer` を持つ。バイトは `Bytes` で渡す。

- **期限。** 待つ要求（`tcp_accept`、`tcp_connect`、`tcp_read`、`tcp_write`）は、それぞれ `deadline: Option(i64)` を取る。値は `monotonic_clock` の時刻（ナノ秒）で、その時刻を過ぎれば `Err(TimedOut)` を答える。`None` は終わるまで待つ。期限を要求ごとに書かせるので、何も送らない相手がプログラムを止め続けることはなく、どこで待つかは型と呼び出しの場で読める。
- **別のタスクから止める。** `tcp_shutdown(stream, ShutdownRead)`（または `ShutdownBoth`）は、別のタスクの `tcp_read` の待ちを起こし、その読みはストリームの終わり（空の `Bytes`）を見る。`tcp_close` は、待っている読み書きを終わらせ、番号を無効にする。`tcp_unlisten` は待っている `tcp_accept` を失敗させ、Unix ソケットのファイルを消す。
- **権限。** `--allow-net` が覆う。`--allow-net=HOST` はそのホストのすべてのポート、`HOST:PORT` はそのポートだけ、`unix:DIR` はその下のソケットを許す（パスは `read`・`write` と同じく解決し、ホストは **解決したパス** に束ねる・つなぐ）。権限を見るのは `tcp_listen` と `tcp_connect` で、ストリームと待ち受けはそこで得た番号でしか手に入らない。ホスト名への接続は、名前で権限を見たあと、その名前の各アドレスを順に試す。
- **`tauto dev`。** 待ち受けは実行をまたいで残り、同じアドレスの `tcp_listen` は同じ待ち受けを返す。再起動の合図で `tcp_accept` の待ちは止まり、その実行のストリームはすべて閉じる。
- **ホスト。** 評価器と Rust はプロセスの表（`tauto_rt::tcp`）で答え、タスクのスレッドからも同じソケットに届く。プロトコルを重ねるホスト（TLS）は `tauto_rt::tcp::take` でソケットを取り出せ、期限と shutdown はソケットそのものにかかる。JavaScript は `options.os_tcp_*`（node の入口は `node:net`）で答え、組み込む側が渡さなければ `Err(Failed(..))` を答える。

### TLS

`tls_*` は `tcp_*` のストリームの上に TLS を重ねる。ホストが rustls で終端し、プログラムには平文のバイト列だけが見える。

| effect | 再開 |
|---|---|
| `tls_accept(stream, server, deadline): Result(TlsStream, IoError)` | 1 |
| `tls_connect(stream, client, deadline): Result(TlsStream, IoError)` | 1 |
| `tls_read(tls, max, deadline): Result(Bytes, IoError)`（空で相手の close_notify） | 1 |
| `tls_write(tls, bytes, deadline): Result((), IoError)` | 1 |
| `tls_shutdown(tls, how): Result((), IoError)`（書く側を終えるときは先に close_notify を送る） | 1 |
| `tls_close(tls): ()`（close_notify を送り、下のソケットを閉じる） | 1 |

- `TlsServer` は証明書の並び（`TlsCert`。`names` が SNI の名前で、空なら既定。鎖と鍵は PEM のバイト列で、鍵は `Secret(Bytes)`）、ALPN の候補、クライアント証明書を求めるときの根 `client_roots` を持つ。`TlsStream` から、選ばれた ALPN、サーバーならクライアントが送った SNI、相手の証明書（DER）を読める。
- `TlsClient` は `server_name`（SNI と証明書の照合に使う。IP アドレスなら照合だけ）、信頼する根（`SystemRoots`、`SystemRootsAnd(cas)`、`OnlyRoots(cas)`）、クライアント証明書、ALPN を持つ。**検証を切る道は作らない。** 自己署名の相手には、その CA を `OnlyRoots` で渡す。
- `tls_accept` と `tls_connect` はストリームのソケットを取り出す（`tauto_rt::tcp::take`）。成否にかかわらず、その `TcpStream` の番号はもうストリームを指さない。別のタスクがそのストリームで待っているあいだは `Failed` になる。
- **権限。** 新しい権限は足さない。ストリームは `tcp_*` の `net` 権限で得たもので、証明書と鍵はプログラムが `read` 権限で読んだバイト列である。行の検査は `tcp_read` と同じく `tls_*` に `--allow-net` を求めるが、TLS が権限の範囲を広げることはない。
- **期限と shutdown。** 待つ要求（握手、読み、書き）は `tcp_*` と同じく `deadline` を取り、ソケットそのものの期限として効く。`tls_shutdown(tls, ShutdownRead)` は別のタスクの `tls_read` の待ちを起こし、その読みは終わり（空の `Bytes`）を見る。読みは 10 ミリ秒ごとにセッションを手放すので、待っている読みが別のタスクの書きを止め続けることはない。
- close_notify を受けずに接続が終わったら `Failed` を返す（切り詰められたデータを終わりと取り違えないため）。
- **実装は選べる。** ホストの rustls と、Tauto で書いた TLS ライブラリ（TauTLS）が同じ effect に答える。TauTLS は `handle` で答えるハンドラとして差し込むので、プログラムの残りは変わらない。どのハンドラも答えなければホストの rustls が答える。
- **ホスト。** 評価器と Rust は `tauto_rt::tls_host`（`tls` フィーチャ。rustls の設定と握手は `tauto_rt::tls`）で答える。生成した Rust のクレートは、`net` を行うプログラムで `tls` フィーチャを有効にする（HTTP クライアントが既に rustls を持ち込んでいる）。フィーチャのないホストと JavaScript のホストは `Err(Failed(..))` を答えるので、そこで TLS が要るプログラムは自分のハンドラで答える。`tauto dev` は実行のあいだにセッションをすべて閉じる。

## 誰が答えるか

標準エフェクトは `pub(open)` の effect なので、プログラムが `handle` で答えてよい（[`visibility.md`](visibility.md)）。テストでファイルやネットワークを差し替えるのはこの形で書く。ホストが答えるのは、どの handler にも答えられずに最上位まで届いたときだけで、権限を求めるのもそのときだけである。

タスク（`spawn` の本体）の標準エフェクトは、`spawn` を囲むハンドラではなくホストが答える（[`nib.md`](nib.md)「タスク」）。タスクが行える効果は prelude の効果の集まり `Host` にまとめてあり、標準エフェクトを足すときはここにも足す。

最上位に届く標準エフェクトとタスクが行う標準エフェクトは、行の検査が求める（`RowReport::host_effects`・`RowReport::task_effects`）。どちらかが一つでもあれば、プログラムの最上位の文を prelude の `host_run(() => { … })` で包み、検査し直してから実行する。`host_run` の腕は、`std/prelude/Os.taut` の `module Os` の extern でホストに頼む。この extern は、それぞれが答える標準エフェクトを行に書く（`fn read_file(path: Text): Result(Text, Text) ! {fs_read}`）。腕の中の呼び出しが答えそのもので、エフェクトの要求ではないので、行の検査と各バックエンドはこの呼び出しをエフェクトとして数えない。プログラムがこの extern と、それを包む `module Host` の関数を名指すと、呼び出しの位置で型の誤りになる：直接の呼び出しはプログラム自身のハンドラと権限の検査（`Os::check`）を飛ばすので、エフェクトを `perform` するか、`read_file` のような公開の関数を呼ぶ。関数は最上位の `let` を見ないので、包んでも名前の意味は変わらない。包むとき、各 `perform spawn(f)` も `perform spawn(() => host_run(f))` にして、タスクの中でもホストが答えるようにする。標準エフェクトが最上位に届かず、タスクも行わないプログラムは包まない。

### 時間のかかる答え

`host_run` は `wait` に答えず、ホストへ渡す。`sleep` と `net` 系、待つ `tcp` 系（`tcp_listen`、`tcp_accept`、`tcp_connect`、`tcp_read`、`tcp_write`）と `tls` 系（`tls_accept`、`tls_connect`、`tls_read`、`tls_write`）の腕は、すぐに終わらない仕事を始めて `Pending` を受け取り（`os_sleep_pending`、`os_offload`）、その旗を `wait` で待ってから答える（`Pending::join`）。

```nib
sleep(ms), k => k(Pending::join(os_sleep_pending(ms)))
```

- ホストは、プログラムの最上位と各タスクの本体を終わりまで走らせるところで `wait` に答える。旗が上がっていなければ、上がるまでそのタスクを止め、そのあいだにほかのタスクを進める。
  - Rust のリアクター（既定）：タスクはスレッドを譲り、`sleep` は runtime のタイマー、`net` 系、`tcp` 系と `tls` 系は blocking pool で答える（[`rust-backend.md`](rust-backend.md)「タスク（`spawn`）」）。
  - Rust の `rust.executor = "threads"` と、`spawn` しないプログラム：その場で終わりまで行い、`wait` はすぐに答える。
  - JavaScript：`os_offload` は本体を別のタスクとして始め、`wait` は旗が上がったときに解ける Promise で答える。
  - 評価器：その場で終わりまで行う。上がっていない旗への `wait` は `deadlock` の実行時エラー（[`nib.md`](nib.md)「タスクの間で待つ」）。
- 待つのはタスクのことなので、タスクの `wait` は `spawn` の行に入らない。

## 権限

```
tauto run --allow-read=./data --allow-net=api.example.com main.taut -- ARGS…
```

- `--allow-read`、`--allow-write`、`--allow-env`、`--allow-net`、`--allow-run` は、その種類のすべてを許す。`--allow-clipboard` はクリップボードの読み取りを許す（書き込みは標準出力と同じく常に許す。読み取りは利用者が直前にコピーしたパスワードなどをそのまま渡すので、既定で拒否する）。`--allow-div` は、budget の外の `Div`（止まらないかもしれないループと呼び出し）をホストの歩数の上限なしに走らせる（下の「`--allow-div`」）。`--allow-all`（`-A`）はすべてを許す。
- `--allow-interactive` を付けると、フラグで許していない種類があっても実行を拒否せず、プログラムが実際にそこへ触れたときに端末で利用者に尋ねる。答えは「今回だけ」（`y`）、「この実行の間は常に」（`a`。範囲はそのファイル、変数、またはホストとポート）、「拒否」（それ以外。空行を含み、既定）。問いは標準入力ではなく端末（`/dev/tty`）で読むので、パイプで渡した入力を食わない。端末がなければ尋ねずに拒否し、拒否したものを標準エラーに出す。powerbox と同じく、許可を広げるのは利用者の答えだけで、プログラムには広げられない。
- `=A,B` を付けると、挙げたものだけを許す。
  - `read`、`write`：パス。システムと同じ順に解決する。絶対パスにして先頭から一つずつ進み、リンクはその場でたどり、`..` はたどった先から上がる。存在しない部分のあとには普通の名前しか置けず、`.` や `..` があれば拒否する。解決したパスが挙げたディレクトリの下にあるかを見て、ホストは **解決したパス** を読み書きする。
  - `env`：変数の名前と完全に一致するもの。
  - `net`：URL のホスト。待ち受けるアドレスも `http://address/` として同じく読む。URL は HTTP クライアントと同じ解析器（Rust は `url`、JavaScript は `URL`）で読み、ホストは **その解析済みの URL** で要求を送る。`example.com` はそのホストのすべてのポートを、`example.com:8080` はそのポートだけを許す。`http` と `https` 以外の URL は許さない。リダイレクトは追わない（許していないホストへ移る経路になるため）。
- **権限ファイル。** `--permissions FILE` は、Eure で書いた権限をフラグの代わりに与える（`tauto run`、`tauto dev`、`--backend` 付きの `run` も同じ）。

  ```eure
  read = ["data"]
  net = ["api.example.com", "localhost:8080"]
  clipboard = true
  ```

  キーは `read`、`write`、`env`、`net`、`run`、`clipboard`、`div`、`all` で、値は `true`（`--allow-KIND`）か名前のリスト（`--allow-KIND=A,B`）。CLI はファイルを読んで、それが表すフラグをその位置に置いてから引数を読むので、ファイルはフラグで書けること以上を許さず、`net` の `host:port` も `net_resolve` もフラグと同じに覆う。前後のフラグとは、同じフラグを重ねたときと同じく互いに広げ合う（どちらが勝つかの順序はない）。書かなかった種類は拒否のままである。`read`、`write` の相対パスはファイルのあるフォルダから読むので、どこから走らせても意味が変わらない。知らないキー、`false`、空のリスト、`,` を含む名前は誤りにする。
- **信頼の承認。** `tauto run`、`tauto dev`、`tauto build` は、プロジェクトの `Tauto.eure` の `trust` 節と各 `--permissions FILE` が与えるものを、前回利用者が承認したときと比べる。初めてのとき、または違うときは、与えるもの全体を一行ずつ（前回から増えた行に `+`、消えた行に `-`）端末に出して尋ね、`y` か `yes` でなければ（空行を含む既定は No）実行しない。承認したものは `~/.tauto/approved/`（`TAUTO_HOME` があればその下）に、プロジェクトのフォルダまたはファイルの絶対パスごとのスナップショットとして残す。比べるのはファイルのバイト列ではなく与えるものなので、コメントや並べ替えだけでは尋ねない。`trust` の下のキーはすべて比べるので、後から加わるキーも覆う。問いは `--allow-interactive` と同じく端末で読み、端末がなければ尋ねずに失敗して、何を承認することになるかを標準エラーに出す。中身を確かめたスクリプトや CI は `--approve-trust` で尋ねずに承認できる。
- **実行前の拒否。** 最上位に届く標準エフェクトとタスクが行う標準エフェクトが必要とする種類のうち、フラグがまったく無いものがあれば、実行を始めずに失敗し、足りないフラグを並べる（`the program needs --allow-net to run; the host denies it by default`）。
- **powerbox（GUI のホスト）。** ホストが自分のファイル選択ダイアログで利用者に選ばせたパスは、フラグに無くても `read` か `write` を許す（`Permissions::choose`、実行中は `tauto_rt::permissions::choose`）。プログラムがパスを名指しして権限を得る道はなく、利用者の選ぶ行為だけが権限になる。ファイルを選んだときはそのファイルだけ、フォルダを選んだときはその下を許す。選んだ時点で解決したパスを覚え、要求のたびに要求のパスを解決し直して比べるので、選んだあとに置かれたリンクで外へは出られない。`env`、`net`、`clipboard` は選べない。
- **tote のコマンド。** `tauto NAME` で走る tote のコマンドは `--allow-*` を読まず、プロジェクトの `Tauto.eure` の `trust.commands` が与えた権限だけで走る（[`commands.md`](commands.md)「権限」）。
- **実行時の拒否。** 範囲を絞った権限が覆わない要求には、`Err(Denied(..))` を答える。プログラムはそれを `Result` として扱える。対話的に尋ねることはしない。
- **権限の検査。** `permission(kind, target)` は、ホストが要求の前に行う検査そのものを答える。`kind` は `read`、`write`、`run`、`env`、`net`、`socket` のどれかで、覆うときはホストが使う形の対象（解決したパス、解析済みの URL など）を `Some` で、覆わないときは `None` を返す。prelude の `host_run` は、ほかの標準エフェクトの前に行うのと同じ検査（`os_check`）でこれに答えるので、`--allow-interactive` なら端末で尋ねもする。権限は要らない。答えから分かるのは、その要求を試みれば分かることだけだからである。権限を広げる道ではなく、検査を行うだけである。ほかのプログラムの要求に標準エフェクトで答えるプログラム（プログラムを走らせる機械など）は、これを使って、覆わない要求に `Failed` ではなく `Denied` を答える。`os_check` はホストのコードのための組み込みで、プログラムからは呼べないので、この効果がそのための入り口になる。

## バックエンド

- **評価器**（`tauto run`）：`RunOptions::permissions`。CLI が `--allow-*` を読む。
- **Rust**：生成した実行ファイルは、先頭に並んだ `--allow-*` を権限として読み（`--` で終わる）、残りをプログラムの引数にする（`tauto_rt::run_main`）。組み込むときは `tauto_rt::run_embedded(permissions, args, run)` で与える（既定の `Permissions` はすべて拒否）。一つのプロセスでは Tauto プログラムを同時に一つだけ実行でき、実行中の入れ子呼び出しも拒否する。埋め込み実行の関数は、開始した task をすべて終了またはキャンセルしてから戻る。実行が終わると、権限・引数・除算許可・step counter の設定は呼び出し前の状態に戻る。埋め込み実行は Rust の panic hook を変更しない。権限・引数・実行ファイル・step limit を設定する API はプログラムの実行中には呼べない。`net` を行うプログラムだけが、`tauto-rt` の `net` フィーチャ（HTTP クライアントの reqwest）を使う。
  - 権限の検査を通った要求は、プロセスの `tauto_rt::host::Host` が答える。既定はシステムのある対象（wasm32-wasip1 を含む）で `System`、`wasm32-unknown-unknown` で何も答えない `Absent`。組み込む側は、プログラムを走らせる前に `tauto_rt::host::set` で自分の `Host` に替えられる（ページ、UI、テスト）。`Host` は権限を広げない：権限が拒んだ要求は `Host` に届かない（[`rust-backend.md`](rust-backend.md)「wasm32」）。
- **JavaScript**：`run(show, externs, options)` の `options.permissions` が `{read, write, env, net, run}` で、それぞれ `true` か許すものの配列である。書かなかった種類は拒否する。`env` は `options.env`、パスの解決は `options.cwd` と `options.resolvePath`、HTTP は `options.fetch`（既定は `globalThis.fetch`）で、組み込む側がホストを制限できる。node の入口は `--allow-*` を読み、`process.env` と `fs` で答える。

## 未決定

- 評価器は標準出力をまとめて最後に書くので、`stdin` の前に書いたプロンプトがその場で出ない。
- `tauto test` は権限を与えない。テストの中のファイルやネットワークは handler で差し替える。

## 依存の extern

extern の関数はホストのコードをそのまま走らせ、その副作用は行に出ない。だから `--allow-*` は extern を覆えない。プロジェクトの作者が自分で書いた extern は自分で選んだものだが、依存の tote（とくに Git から取ったもの）の extern は、作者が見ないまま権限の外でネットワークやファイルに触れうる。

そこで、依存の tote が `extern` を宣言していれば、読み込みで拒否する（既定で拒否）。エラーはその tote の extern を一つずつ場所つきで挙げる。許すときは、プロジェクト（入口の tote）の `Tauto.eure` に名指しで書く。

```eure
trust {
  extern = ["regex"]
}
```

`trust` を読むのは入口の tote だけで、依存の `trust` は何も許さない（依存が自分の依存を許すことはできない）。入口の tote 自身の extern は許可を要らない。

## extern はその tote の中でだけ呼べる

extern は宣言した tote の外から呼べない。名前解決（マクロの展開の後）で、別の tote のファイルが extern の名前を参照していればエラーにする。tote はその extern を包む関数を書き、ほかの tote にはその関数を渡す。

```tauto
// tote a
extern {
  fn leak(url: Text): Text
}

fn fetch(url: Text): Text { leak(url) }

// tote b（a に依存する）
fn get(): Text { fetch("x") }   // よい
fn bad(): Text { leak("x") }    // エラー：`leak` は a の extern
```

`trust` は依存の extern を読み込むことを許すが、それを外から呼ぶことは許さない。ホストに触れるコードは extern を宣言した tote の中にとどまり、その tote が外に見せる API は包む関数だけになる。展開の後で調べるので、tote のマクロが extern の呼び出しをほかの tote に展開することもできない。

標準ライブラリと prelude の extern、tote に属さないファイル（manifest なしで読んだプログラム）の extern はこの制限を受けない。`extern { instance C(T) }` のインスタンスはクラスのメソッドとして呼ばれ、名前では調べない。

## 標準入出力のバイトと flush

`stdin` は一行ずつ、`stdin_bytes(max)` は行を見ずにバイトで読む。Content-Length の枠で区切るプロトコル（LSP など）は、ヘッダを `stdin` で読み、本文を `stdin_bytes` で必要なバイト数になるまで繰り返し読む。二つは同じ入力の続きを取り合うので、混ぜて使える。`stdin_bytes` は一バイトでも届けば返り、入力の終わりでだけ空を返す（`max` が 0 のときも空を返すが、終わりではない）。

`stdout_flush()` は、それまでに `stdout` と `stderr` に渡したものを書き出す。相手の返事を待つ前に呼べば、相手に届いている。評価器は既定で標準出力をまとめて最後に書くが、実行を流す形（ストリーミング）では一回ごとに書くので、その形では `stdout_flush` は何も変えない。どちらも権限は要らない（標準入出力は常に許す）。

**ホスト。** 評価器・VM・Rust は標準入力を `stdin` と同じバッファから、JavaScript は `options.os_read_stdin(max)` と `options.os_flush()` で答える。

## 終了の要求

`shutdown_token()` は、外から実行の終わりを求められたとき（Ctrl-C の SIGINT と SIGTERM）に要求が立つ `CancelToken` を返す。[協調的キャンセル](#協調的キャンセル)のトークンと同じもので、プログラムは `CancelToken::signal` を入力の Signal と `Signal::either` で合わせて待ち、要求を見たら資源を後始末して普通に返る。新しい制御の効果や途中での打ち切りは足さないので、linear な資源の検査はこの経路にも効く。

- 一度でも `shutdown_token` を行ったプログラムは、最初の要求では終わらない。要求はそれまでに渡したトークンすべてと、そのあとで渡すトークンに立つ。
- 二度目の要求では、プログラムを待たずにすぐ終わる（終了コードはシェルがそのシグナルでの終わりに付ける `128 + n`）。後始末が止まったときの逃げ道である。
- 一度も行わないプログラムでは、要求は今までどおりすぐに実行を終わらせる。
- 権限は要らない。自分のプロセスに届いた通知を読むだけで、外に何もしない。
- 要求を待つトークンがある間、待っている task がほかに起こされる見込みがなくても、ホストはデッドロックとして止めずに要求を待つ。

**ホスト。** ハンドラ（`Os.taut` の `Host::shutdown_token`）が `Cancellation` を作り、その Signal を `Os::on_shutdown` でホストに預ける。評価器・Rust・VM（`crates/tauto-vm`）は `tauto_rt::shutdown` で答える。シグナルのハンドラは旗を立てるだけで、旗は歩みごと（`host_tick`）と待つ間に Signal を上げる。task をスレッドで走らせるときは見張りのスレッドも上げる。ハンドラを入れる二つの unsafe な呼び出しは `tauto-rt-signal` に分け、`tauto-rt` は `#![forbid(unsafe_code)]` のままにする。Unix でないホストでは要求は立たない。JavaScript は `options.os_on_shutdown(raise)` で答え、node の入口は `process.on('SIGINT' / 'SIGTERM')` で `raise` を呼ぶ。ブラウザでは立たない。Tauto で書いた VM（`totes/vm`）は、プログラムが初めて求めたときにシェル自身が `shutdown_token` を行い、その要求を見て機械の Signal を上げる。

使用例は `examples/shutdown.taut`。

## ファイルの情報と移動

```tauto
pub(open) enum FileKind { IsFile, IsDir, IsOther }
pub(open) struct FileStat { kind: FileKind, size: u64, modified_ms: u64 }
```

- `fs_stat(path)` はパスにあるものの種別・バイト数・最後に変わった時刻（Unix 紀元からのミリ秒。ホストが知らないとき、または紀元より前のときは 0）を返す。何もなければ `Ok(None)` で、誤りにしない（存在の確認は `fs_stat` で足りる）。`fs_list_dir` は名前しか返さないので、ディレクトリかどうかや更新時刻はこれで知る。
- `fs_rename(src, dst)` はファイルやディレクトリを動かす。`src` を消し `dst` に書くので、どちらも `write` が覆っていなければならない。`dst` にファイルがあれば置き換わる。`src` と `dst` が別のファイルシステムにあるときの扱いはホストによる（失敗なら `Err(Failed(..))`）。
- `fs_copy(src, dst)` はファイルの中身を写す。`src` は `read`、`dst` は `write` で調べる。ディレクトリは写さない（`Err(Failed(..))`）。行に `fs_copy` があるプログラムは、実行前の拒否で `read` と `write` の両方のフラグを求める。
- `fs_canonicalize(path)` は存在するものの絶対パスを、リンクをたどって `.` と `..` を除いた形で返す。ないパスは `Err(Failed(..))`。
- **リンク。** 権限が覆うかどうかの検査（「権限の検査」）はリンクをたどった先のパスで行うので、`fs_stat` もリンクをたどった先を見る。リンクそのものかどうかは（検査の外で別のパスを見せてしまうので）プログラムには見せない。
- **ホスト。** 評価器・VM・Rust は `std::fs` で、JavaScript は `options.os_stat(path)`（`{ kind: 'file' | 'dir' | 'other', size, modified_ms }` か `null`）、`os_move_path(src, dst)`、`os_copy_file(src, dst)`、`os_canonicalize(path)` で答える（node の入口は `statSync`・`renameSync`・`copyFileSync`・`realpathSync`）。

## リンクそのものを見る・リンクをたどらずに作る

`fs_stat` と `fs_write` は、権限が覆うかどうかの検査と同じに、リンクをたどった先を相手にする。リンクを疑う側のプログラム（`tauto init` が、リンクの親を拒否し、リンクの上に書かないことなど）は、リンクそのものを見て、リンクの上に書かずに作れなければならない。そのための効果を二つ足した。それぞれ一つのことだけをし、既存の効果は変えない。

- `fs_read_link(path)` は、`path` にあるリンクの指す先をそのまま返す（たどらない）。リンクでないもの、何もないときは `Ok(None)`。
- `fs_write_new(path, contents)` は、何もない場所にファイルを作る。そこに何かがあれば（リンクも、指す先が無いリンクも）失敗し、リンクを通して書くことはない（Unix では `O_CREAT | O_EXCL`）。置き換える `fs_write` とは別の効果で、一緒にしない。
- **権限。** どちらも対象は「その場所にあるもの」そのもので、リンクをたどった先ではない。そこで検査するのは、親ディレクトリをリンクをたどって解いたものに、名前を書かれたままつないだ場所である。名前が空・`.`・`..` のときは場所を指さないので、権限が覆わないものとして拒否する。`read` が `fs_read_link` を、`write` が `fs_write_new` を覆う。
- **ホスト。** 評価器・VM・Rust は `symlink_metadata` と `read_link`、`OpenOptions::create_new` で、JavaScript は `options.os_read_link(path)`（リンクの指す先か `null`）と `options.os_write_new(path, contents)`（`flag: 'wx'`）で答える。

## root の下だけを読む

`fs_read_under(root, path)` と `fs_read_bytes_under(root, path)` は、ディレクトリ `root` の下にあるファイル `path` を、`root` の外に出ずに読む。展開した tote や受け取った書庫のように、中身を信用できないディレクトリからファイルを読むためのものである。

- **path。** `/` でつないだ名前で、絶対パス・空の名前・`.`・`..` を含まない。ほかの形は `Err(Failed(..))`。
- **リンク。** ファイルを含めて、どの成分もリンクであってはならない（`Err(Failed(..))`）。各成分を一つ前の成分のディレクトリ記述子から開く（`openat` と `O_NOFOLLOW`）ので、読んでいる間にリンクを置かれても、ディレクトリを改名されても、`root` の外は読まない。普通のファイルでないもの（FIFO など）も `Err(Failed(..))` で、開くときに待たない。
- **権限。** 調べるのは `root` だけで、`read` が `root` を覆っていればよい。`path` はリンクをたどらずに `root` の下に留まるので、`root` を覆う権限がその下も覆う。`root` そのものはほかのパスと同じくリンクをたどった先で調べる（「リンク」）。
- **一回ごと。** 一回の読み込みの中で `root` の外に出ないことを保証する。呼ぶたびに `root` を開き直すので、二回の読み込みの間に `root` が別のディレクトリに替われば、二回目は新しい方を読む。
- **ホスト。** 評価器・VM・Rust は Unix で `openat` を使い、それ以外のシステムでは `Err(Failed(..))` を返す。JavaScript は `options.os_read_under(root, path)` と `os_read_bytes_under(root, path)` で答える。node の入口は `openat` を持たないので、途中のディレクトリを `lstat` で調べ、ファイルを `O_NOFOLLOW` で開く。調べてから開くまでの間にディレクトリをリンクに替えられることは防がない。

## 一時ディレクトリ

`fs_temp_dir()` はシステムの一時ファイルの場所に新しい空のディレクトリを作り、そのパスを返す。権限は要らない。パスを選んだのはプログラムではなくホストなので、powerbox で利用者が選んだフォルダと同じく、その実行の間はその下を `read` と `write` で読み書きできる（`Permissions::choose`）。消すのはプログラムで、`fs_remove` で消す。

行に `fs_temp_dir` があるプログラムは、実行前の拒否（「権限」）で `read` と `write` のフラグを求めない。一時ディレクトリの下はフラグなしで読み書きできるので、そこにしか触れないプログラムに要らないフラグを書かせないためである。フラグの覆わない場所への要求は、ほかと同じく実行中に `Err(Denied(..))` になる。

## カレントディレクトリと環境変数

プログラムの実行全体のカレントディレクトリや環境変数を書き換える効果（`chdir`・`set_var`）は置かない。プロセス全体の状態を書き換えると、並行して走るタスクや、権限の検査と使用の間の相対パスの読み替えに効いてしまい、「検査したものを使う」（「権限の検査」）が崩れるからである。必要なことは次の形で足りる。

- **カレントディレクトリを知る。** `permission("read", ".")` は、`read` が覆っていれば `.` の絶対パス（リンクをたどった形）を `Some` で返す。覆っていなければ `None`。ディレクトリの名前を知ること自体が `read` の中身なので、別の効果は要らない。
- **子プロセスのディレクトリと環境変数。** `proc_run` の `Process::dir` と `Process::env`（「プログラムの実行」）で、その子だけに与える。
- **パスの解決。** 相対パスは `fs_canonicalize` で絶対パスにしてから渡す。

## プログラムの実行

```tauto
pub(open) struct Process { program: Text, args: List(Text), dir: Text, env: List(Pair(Text, Text)), stdin: Bytes }
pub(open) struct ProcessOutput { status: Option(u64), stdout: Bytes, stderr: Text }
pub(open) effect proc_run(p: Process): Result(ProcessOutput, IoError) direct
```

- `program` は名前（`PATH` から探す）かパス、`dir` は走らせるディレクトリ（空ならこの実行と同じ）、`env` はこの実行の環境変数に上書きして足す変数、`stdin` は標準入力に渡すバイト列。終わるまで待ち、終了コード（シグナルで終わったときは `None`）、標準出力のバイト列、標準エラー（UTF-8 でないバイトは U+FFFD）を返す。
- **権限。** `--allow-run` はすべてのプログラム、`--allow-run=git,clang` は `program` の綴りがそのどれかと一致するものだけを許す。パスで名指したものは同じパスの綴りでしか許さない。
- 走らせたプログラムはこの実行の権限の外で、Tauto を走らせた利用者ができることをすべてできる。だから `--allow-run=git` は「git にできることすべて」を許すことであり、ほかの権限より強い。行に `proc_run` があることで、それが型から見える。
- `tauto` という名前のプログラムは、いま走っている `tauto` 自身を指す（`tauto run` と tote のコマンド）。`--backend rust` で作った実行ファイルでは `PATH` の `tauto` である。
- **ホスト。** 評価器と Rust は `std::process` で、JavaScript は `options.os_run(program, args, dir, env, stdin)`（node の入口は `child_process.spawnSync`）で答える。

## 走らせたまま進むプログラム

`proc_run` は終わるまで待って全出力を捕まえる。子を止めて起動し直す `dev` や、出力を集めながらタイムアウトで止める `bench`、端末をそのまま渡す生成バイナリの実行には足りない。そこで `tcp_*` と同じ形（番号のハンドルと期限）で、起動と、その後の読み書きと待ちを分けた。

```tauto
pub(open) struct Child { id: u64 }
pub(open) enum Stdio { StdioPiped, StdioInherit }
pub(open) struct ProcessIo { stdin: Stdio, stdout: Stdio, stderr: Stdio }
pub(open) enum ChildStream { ChildStdout, ChildStderr }
```

- `proc_spawn(p, io)` は `proc_run` と同じ `Process` と同じ権限（`--allow-run`、`--allow-run=NAME`）で起動する。`Piped` の標準入力には `p.stdin` を先に書き、そのあとも開いたままにする。`Inherit` はこの実行自身の標準入出力を子に渡す。起動の検査を越えた子は、`proc_run` と同じく、この実行の権限の外で動く。
- `proc_read(c, which, max, deadline)` は標準出力か標準エラーを、届き次第 `max` バイトまで返す。終わりでは空で、`Piped` でない流れも空（終わり）として返す。`proc_write` は標準入力に全部書き、`proc_close_stdin` は閉じて子に終わりを読ませる。
- `proc_wait(c, deadline)` は子の終わりを待ち、終了コード（シグナルで終わったときは `None`）を返す。期限（`monotonic_clock` の値、`None` は待ち続ける）が来れば `Err(TimedOut)` で、子は走り続ける。
- `proc_close(c)` は走っている子を終わらせ、番号を手放す。待っている他のタスクの読みや待ちは終わる。JavaScript のホストは子のプロセスグループごと終わらせる。
- 読み・書き・待ちは `tcp_*` と同じく待つ間に他のタスクを進める。権限は起動の `run` が覆ったものだけで、番号を知っていればほかの検査は要らない。番号は起動した実行の中でしか意味を持たない。
- **ホスト。** 評価器と Rust は `std::process` と読み取りスレッドで、JavaScript は `options.os_child_spawn`・`os_child_read`・`os_child_write`・`os_child_close_stdin`・`os_child_wait`・`os_child_close`（node の入口は `child_process.spawn`）で答える。VM は `tcp_*` と同じく、シェル（`totes/vm`）が自分のホストに同じ効果を求めて答える。待つ要求（`tcp_accept`・`tcp_read`・`proc_read`・`proc_wait`）は、機械がその task だけを待たせて他の task を進め（`MstepStart`）、シェルは一つのスレッドで短い期限（10ms）を区切って順に尋ね直し、答えが来たものから機械に渡す。`tcp_connect`・`tcp_write`・`proc_write` はその場で答える。

## `--allow-div`

止まらないことが正しいプログラム（GUI のイベントループ、サーバ）がある。そうしたプログラムの行には `Div` があり、型がすでに「止まらないかもしれない」と言っている。一方、budget の外の `Div` はホストの歩数の上限（既定で一千万）で止まり、誤って止まらないループを書いたプログラムはそこで `interrupted: the step limit ran out` になる。上限は誤りへの既定の備えで、止まらないことを意図したプログラムでは外す必要がある。

外す手段は、ほかの権限と同じく実行の許可 `--allow-div` にする。`Div` は効果としてすでに行に書かれているので、言語に新しい構文や注釈は足さない。許すかどうかは、ファイルやネットワークと同じく、走らせる側が実行のたびに明示して決める（既定では上限がある）。値を取らず、`--allow-div=…` は誤り。`--allow-all` は含む。

- eval（`tauto run`）：`--steps N` がなければ上限なしで走る。`--steps N` を書けばその数が上限になる。`tauto dev` とコマンド（`tauto NAME`）は前から上限なし。
- Rust：生成した `main` が引数の `--allow-div` を読み、`tauto_rt::host_tick` が数えなくなる。埋め込むホストは `Permissions { div: Grant::All, .. }` を `permissions::set` に渡す。`TAUTO_STEP_LIMIT` はフラグがないときの上限のまま。
- JavaScript：`run` の `options.permissions.div === true` で、`options.steps` がなければ上限なし。node の入口は `--allow-div` を読む。
- 権限のファイルでは `div = true`。

budget の中は変わらない。`budget` は `Div` を `Exceeded` に変え、その数え方はプログラムが書いたとおりで、ホストの上限とは別である。プログラムの一部だけを上限から外したいときは、これまでどおり `budget` と `info.unbounded()` を書く。


## 協調的キャンセル

`std::prelude::Par` の `Cancellation` は要求を送る権限、`CancelToken` は要求を読む権限を表す。
`Cancellation::new` が要求元を作り、`Cancellation::token` がその通知を読むトークンを返す。
`Cancellation::request` は通知を立てる。同じ要求を繰り返しても通知は立ったままで、後から
作ったトークンにも届く。トークンから要求元は取り出せない。

`CancelToken::is_requested` は要求があるかを読み、`CancelToken::signal` は待機用の Signal を
返す。`Signal::either` はどちらかの入力が上がれば上がる Signal を作る。合成は入力を消費せず、
同じ入力と合成の入れ子を扱う。`wait` を行う前に立った通知も観測する。合成自体は待機用の
スレッドを起動しない。

要求は Task の停止や副作用の巻き戻しを行わない。処理は明示した場所でトークンを確認し、
必要な資源の解放を行って通常の戻り値で終了する。`Cancelled` はその結果を表す型として使える。
Task の持ち主は `Task::join` で後始末を含む終了を確認する。待機中に要求を受けたい処理は、
準備完了とキャンセルの Signal を合成して待ち、起床後に要求を確認する。通知を確認しない
計算や、通知を待たないホスト操作に対して、要求から終了までの時間の上限は保証しない。

使用例は `examples/cancellation.taut`、検査は `cases/eval/cancellation.eure`。
