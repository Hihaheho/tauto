//! The host's requests that wait on the network (`os_fetch`,
//! `os_tcp_*`, `os_tls_*` …): each runs on a thread of its own, and the task
//! that asked waits for its answer while the other tasks run.
//!
//! Values do not cross threads; the request takes plain arguments and its
//! answer is a [`Reply`], which the machine turns into a value.

use std::rc::Rc;

use tauto_rt::stdlib::Bytes;
use tauto_rt::{Text, stdlib, tcp, tls_host};

use crate::builtins::Known;
use crate::value::{R, Value, fail};

/// What a request answers, as plain data.
pub enum Reply {
    Unit,
    Text(String),
    Texts(Vec<String>),
    Bytes(Vec<u8>),
    /// A product's members, in its order.
    Product(Vec<Reply>),
    Some(Box<Reply>),
    None,
    Ok(Box<Reply>),
    Err(String),
    /// The request ended the run: a run-time error of the host.
    Fail(String),
}

impl Reply {
    pub fn value(self, k: &Known) -> Value {
        match self {
            Reply::Unit => Value::Unit,
            Reply::Text(t) => Value::text(&t),
            Reply::Texts(ts) => k.list(
                ts.iter()
                    .map(|t| Value::text(t))
                    .collect::<Vec<_>>()
                    .into_iter(),
            ),
            Reply::Bytes(b) => Value::Bytes(Rc::from(b)),
            Reply::Product(ms) => {
                Value::Product(Rc::new(ms.into_iter().map(|m| m.value(k)).collect()))
            }
            Reply::Some(a) => k.some(a.value(k)),
            Reply::None => k.none(),
            Reply::Ok(a) => k.ok(a.value(k)),
            Reply::Err(e) => k.err(Value::text(&e)),
            Reply::Fail(_) => Value::Unit,
        }
    }
}

pub type Job = Box<dyn FnOnce() -> Reply + Send>;

/// Runs the request on a thread of its own; its reply goes to `tx` with `id`.
pub fn start(job: Job, id: u64, tx: std::sync::mpsc::Sender<(u64, Reply)>) {
    std::thread::spawn(move || {
        let reply =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(job)).unwrap_or_else(|p| {
                Reply::Fail(
                    p.downcast_ref::<tauto_rt::TautoError>()
                        .map(|e| e.message.clone())
                        .or_else(|| p.downcast_ref::<String>().cloned())
                        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                        .unwrap_or_else(|| "interrupted: a panic".into()),
                )
            });
        let _ = tx.send((id, reply));
    });
}

/// The builtins that are requests of this kind.
pub const NAMES: &[&str] = &[
    "Os::list_dir",
    "Os::run",
    "Os::fetch",
    "Os::resolve",
    "Os::tcp_listen",
    "Os::tcp_accept",
    "Os::tcp_connect",
    "Os::tcp_read",
    "Os::tcp_write",
    "Os::tcp_shutdown",
    "Os::tcp_close",
    "Os::tcp_unlisten",
    "Os::tls_accept",
    "Os::tls_connect",
    "Os::tls_read",
    "Os::tls_write",
    "Os::tls_shutdown",
    "Os::tls_close",
];

fn texts(v: Vec<Text>) -> Vec<String> {
    v.into_iter().map(|t| t.to_string()).collect()
}

fn result<T>(r: Result<T, Text>, f: impl FnOnce(T) -> Reply) -> Reply {
    match r {
        Ok(x) => Reply::Ok(Box::new(f(x))),
        Err(e) => Reply::Err(e.to_string()),
    }
}

fn timed<T>(r: Result<Option<T>, Text>, f: impl FnOnce(T) -> Reply) -> Reply {
    result(r, |o| match o {
        Some(x) => Reply::Some(Box::new(f(x))),
        None => Reply::None,
    })
}

fn u64_of(v: &Value) -> R<u64> {
    u64::try_from(v.as_int()?).or_else(|_| fail(crate::value::TOO_LARGE))
}

fn deadline(k: &Known, v: &Value) -> R<Option<i64>> {
    let v = v.get()?;
    match &v {
        Value::Data(d) if d.fields.len() == 1 => {
            let _ = k;
            Ok(Some(d.fields[0].as_int()? as i64))
        }
        _ => Ok(None),
    }
}

fn bytes_of(v: &Value) -> R<Vec<u8>> {
    match v.get()? {
        Value::Bytes(b) => Ok(b.to_vec()),
        v => fail(format!("internal: expected Bytes, got {}", v.kind())),
    }
}

fn text_list(k: &Known, v: &Value) -> R<Vec<String>> {
    k.items(v.clone())?
        .iter()
        .map(|t| t.as_text().map(|t| t.to_string()))
        .collect()
}

/// The request a builtin makes of its arguments.
pub fn job(k: &Known, name: &str, a: &[Value]) -> R<Job> {
    let text = |i: usize| a[i].as_text().map(|t| t.to_string());
    Ok(match name {
        "Os::fetch" => {
            let (method, url, address) = (text(0)?, text(1)?, text(2)?);
            let (headers, body) = (text_list(k, &a[3])?, bytes_of(&a[4])?);
            Box::new(move || {
                let r = stdlib::os_fetch_vec(
                    method.into(),
                    url.into(),
                    address.into(),
                    headers.into_iter().map(Text::from).collect(),
                    Bytes::from(body),
                );
                result(r, |(items, body)| {
                    Reply::Product(vec![
                        Reply::Bytes(body.to_vec()),
                        Reply::Texts(texts(items)),
                    ])
                })
            })
        }
        "Os::list_dir" => {
            let path = text(0)?;
            Box::new(move || {
                result(stdlib::os_list_dir_vec(path.into()), |v| {
                    Reply::Texts(texts(v))
                })
            })
        }
        "Os::run" => {
            let (program, args, dir) = (text(0)?, text_list(k, &a[1])?, text(2)?);
            let (env, stdin) = (text_list(k, &a[3])?, bytes_of(&a[4])?);
            Box::new(move || {
                let r = stdlib::os_run_vec(
                    program.into(),
                    args.into_iter().map(Text::from).collect(),
                    dir.into(),
                    env.into_iter().map(Text::from).collect(),
                    Bytes::from(stdin),
                );
                result(r, |(items, out)| {
                    Reply::Product(vec![Reply::Bytes(out.to_vec()), Reply::Texts(texts(items))])
                })
            })
        }
        "Os::resolve" => {
            let url = text(0)?;
            Box::new(move || {
                result(stdlib::os_resolve_vec(url.into()), |v| {
                    Reply::Texts(texts(v))
                })
            })
        }
        "Os::tcp_listen" => {
            let address = text(0)?;
            Box::new(move || {
                result(tcp::os_tcp_listen_vec(address.into()), |v| {
                    Reply::Texts(texts(v))
                })
            })
        }
        "Os::tcp_accept" => {
            let (id, d) = (u64_of(&a[0])?, deadline(k, &a[1])?);
            Box::new(move || timed(tcp::os_tcp_accept_vec(id, d), |v| Reply::Texts(texts(v))))
        }
        "Os::tcp_connect" => {
            let (address, d) = (text(0)?, deadline(k, &a[1])?);
            Box::new(move || {
                timed(tcp::os_tcp_connect_vec(address.into(), d), |v| {
                    Reply::Texts(texts(v))
                })
            })
        }
        "Os::tcp_read" => {
            let (id, max, d) = (u64_of(&a[0])?, u64_of(&a[1])?, deadline(k, &a[2])?);
            Box::new(move || timed(tcp::os_tcp_read_vec(id, max, d), Reply::Bytes))
        }
        "Os::tcp_write" => {
            let (id, b, d) = (u64_of(&a[0])?, bytes_of(&a[1])?, deadline(k, &a[2])?);
            Box::new(move || timed(tcp::os_tcp_write(id, Bytes::from(b), d), |()| Reply::Unit))
        }
        "Os::tcp_shutdown" => {
            let (id, how) = (u64_of(&a[0])?, u64_of(&a[1])?);
            Box::new(move || result(tcp::os_tcp_shutdown(id, how), |()| Reply::Unit))
        }
        "Os::tcp_close" => {
            let id = u64_of(&a[0])?;
            Box::new(move || {
                tcp::os_tcp_close(id);
                Reply::Unit
            })
        }
        "Os::tcp_unlisten" => {
            let id = u64_of(&a[0])?;
            Box::new(move || {
                tcp::os_tcp_unlisten(id);
                Reply::Unit
            })
        }
        "Os::tls_accept" => {
            let id = u64_of(&a[0])?;
            let names = text_list(k, &a[1])?;
            let pems = k
                .items(a[2].clone())?
                .iter()
                .map(bytes_of)
                .collect::<R<Vec<_>>>()?;
            let alpn = text_list(k, &a[3])?;
            let (roots, d) = (bytes_of(&a[4])?, deadline(k, &a[5])?);
            Box::new(move || {
                let r = tls_host::os_tls_accept_vec(
                    id,
                    names.into_iter().map(Text::from).collect(),
                    pems.into_iter().map(Bytes::from).collect(),
                    alpn.into_iter().map(Text::from).collect(),
                    Bytes::from(roots),
                    d,
                );
                timed(r, |(items, cert)| {
                    Reply::Product(vec![Reply::Bytes(cert), Reply::Texts(texts(items))])
                })
            })
        }
        "Os::tls_connect" => {
            let (id, server) = (u64_of(&a[0])?, text(1)?);
            let roots = u64_of(&a[2])?;
            let pems = k
                .items(a[3].clone())?
                .iter()
                .map(bytes_of)
                .collect::<R<Vec<_>>>()?;
            let (alpn, d) = (text_list(k, &a[4])?, deadline(k, &a[5])?);
            Box::new(move || {
                let r = tls_host::os_tls_connect_vec(
                    id,
                    server.into(),
                    roots,
                    pems.into_iter().map(Bytes::from).collect(),
                    alpn.into_iter().map(Text::from).collect(),
                    d,
                );
                timed(r, |(items, cert)| {
                    Reply::Product(vec![Reply::Bytes(cert), Reply::Texts(texts(items))])
                })
            })
        }
        "Os::tls_read" => {
            let (id, max, d) = (u64_of(&a[0])?, u64_of(&a[1])?, deadline(k, &a[2])?);
            Box::new(move || {
                timed(tls_host::os_tls_read(id, max, d), |b| {
                    Reply::Bytes(b.to_vec())
                })
            })
        }
        "Os::tls_write" => {
            let (id, b, d) = (u64_of(&a[0])?, bytes_of(&a[1])?, deadline(k, &a[2])?);
            Box::new(move || {
                timed(tls_host::os_tls_write(id, Bytes::from(b), d), |()| {
                    Reply::Unit
                })
            })
        }
        "Os::tls_shutdown" => {
            let (id, how) = (u64_of(&a[0])?, u64_of(&a[1])?);
            Box::new(move || result(tls_host::os_tls_shutdown(id, how), |()| Reply::Unit))
        }
        "Os::tls_close" => {
            let id = u64_of(&a[0])?;
            Box::new(move || {
                tls_host::os_tls_close(id);
                Reply::Unit
            })
        }
        n => return fail(format!("unknown builtin {n}")),
    })
}
