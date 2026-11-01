//! TLS over loopback TCP, with the test certificates `tests/tls/certs.rs` makes.
#![cfg(feature = "tls")]

use std::net::{Shutdown, TcpListener, TcpStream};
use std::thread;

use tauto_rt::tls::{self, ClientOptions, Roots, ServerCert, ServerOptions};

#[path = "tls/certs.rs"]
mod certs;

fn pem(name: &str) -> Vec<u8> {
    certs::read(name)
}

fn cert(names: &[&str], file: &str) -> ServerCert {
    ServerCert {
        names: names.iter().map(|n| n.to_string()).collect(),
        chain_pem: pem(&format!("{file}.pem")),
        key_pem: pem(&format!("{file}.key")),
    }
}

fn server_options() -> ServerOptions {
    ServerOptions {
        certs: vec![cert(&[], "a"), cert(&["b.test"], "b")],
        alpn: vec![b"h2".to_vec(), b"http/1.1".to_vec()],
        client_roots: None,
    }
}

fn client_options() -> ClientOptions {
    ClientOptions {
        roots: Roots::Only(pem("ca.pem")),
        client_cert: None,
        alpn: vec![b"http/1.1".to_vec()],
    }
}

/// Runs `server` on one accepted connection and `client` against it.
fn pair<A: Send + 'static, B>(
    server: impl FnOnce(TcpStream) -> A + Send + 'static,
    client: impl FnOnce(TcpStream) -> B,
) -> (A, B) {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    let s = thread::spawn(move || server(listener.accept().unwrap().0));
    let b = client(TcpStream::connect(addr).unwrap());
    (s.join().unwrap(), b)
}

#[test]
fn sni_chooses_the_certificate_and_alpn_the_protocol() {
    for name in ["a.test", "b.test", "localhost"] {
        let server = tls::server_config(&server_options()).unwrap();
        let client = tls::client_config(&client_options()).unwrap();
        let (got, ()) = pair(
            move |sock| {
                let mut t = tls::accept(server, sock).unwrap();
                let seen = (
                    t.server_name().map(str::to_owned),
                    t.alpn().map(<[u8]>::to_vec),
                );
                let req = t.read(64).unwrap();
                t.write(&[b"echo ".as_slice(), &req].concat()).unwrap();
                t.close().unwrap();
                seen
            },
            |sock| {
                let mut t = tls::connect(client, name, sock).unwrap();
                assert_eq!(t.alpn(), Some(b"http/1.1".as_slice()));
                t.write(b"hi").unwrap();
                let mut got = Vec::new();
                loop {
                    let chunk = t.read(3).unwrap();
                    if chunk.is_empty() {
                        break;
                    }
                    got.extend(chunk);
                }
                assert_eq!(got, b"echo hi");
            },
        );
        // Only `b.test` has a certificate of its own; the default answers the
        // others, and the server still sees the name the client sent.
        assert_eq!(got, (Some(name.to_owned()), Some(b"http/1.1".to_vec())));
    }
}

fn handshake_error(server: ServerOptions, client: ClientOptions, name: &'static str) -> String {
    let server = tls::server_config(&server).unwrap();
    let client = tls::client_config(&client).unwrap();
    let (_, err) = pair(
        move |sock| tls::accept(server, sock).map(|_| ()),
        move |sock| tls::connect(client, name, sock).map(|_| ()).unwrap_err(),
    );
    err
}

#[test]
fn an_untrusted_certificate_is_refused() {
    let server = ServerOptions {
        certs: vec![cert(&[], "other")],
        ..server_options()
    };
    let err = handshake_error(server, client_options(), "a.test");
    assert!(err.contains("UnknownIssuer"), "{err}");
}

#[test]
fn a_certificate_for_another_name_is_refused() {
    let err = handshake_error(server_options(), client_options(), "c.test");
    assert!(err.contains("not valid for name \"c.test\""), "{err}");
}

#[test]
fn a_server_that_asks_for_a_client_certificate_gets_it_or_refuses() {
    let options = || ServerOptions {
        client_roots: Some(pem("ca.pem")),
        ..server_options()
    };
    let server = tls::server_config(&options()).unwrap();
    let client = tls::client_config(&client_options()).unwrap();
    let (refused, _) = pair(
        move |sock| tls::accept(server, sock).map(|_| ()).unwrap_err(),
        move |sock| {
            // TLS 1.3 finishes the client's side first; the refusal arrives
            // at the next read.
            let t = tls::connect(client, "a.test", sock);
            t.and_then(|mut t| t.read(1).map_err(|e| e.to_string()))
                .err()
        },
    );
    assert!(refused.contains("peer sent no certificates"), "{refused}");

    let server = tls::server_config(&options()).unwrap();
    let client = tls::client_config(&ClientOptions {
        client_cert: Some((pem("client.pem"), pem("client.key"))),
        ..client_options()
    })
    .unwrap();
    let (peer, ()) = pair(
        move |sock| {
            let mut t = tls::accept(server, sock).unwrap();
            let peer = t.peer_certificate().map(<[u8]>::to_vec);
            t.close().unwrap();
            peer
        },
        move |sock| {
            let mut t = tls::connect(client, "a.test", sock).unwrap();
            assert!(t.read(1).unwrap().is_empty());
        },
    );
    let client_der = pem_der(&pem("client.pem"));
    assert_eq!(peer, Some(client_der));
}

fn pem_der(pem: &[u8]) -> Vec<u8> {
    use rustls::pki_types::CertificateDer;
    use rustls::pki_types::pem::PemObject;
    CertificateDer::from_pem_slice(pem).unwrap().to_vec()
}

#[test]
fn a_close_without_close_notify_is_an_error() {
    let server = tls::server_config(&server_options()).unwrap();
    let client = tls::client_config(&client_options()).unwrap();
    let (_, err) = pair(
        move |sock| {
            let mut t = tls::accept(server, sock).unwrap();
            t.write(b"part").unwrap();
            t.get_mut().shutdown(Shutdown::Both).unwrap();
        },
        move |sock| {
            let mut t = tls::connect(client, "a.test", sock).unwrap();
            assert_eq!(t.read(16).unwrap(), b"part");
            t.read(16).unwrap_err()
        },
    );
    assert_eq!(err.kind(), std::io::ErrorKind::UnexpectedEof);
}

#[test]
fn configurations_that_cannot_work_are_refused() {
    let none = ServerOptions {
        certs: vec![],
        ..server_options()
    };
    assert!(
        tls::server_config(&none)
            .unwrap_err()
            .contains("needs a certificate")
    );
    let mismatched = ServerCert {
        key_pem: pem("b.key"),
        ..cert(&[], "a")
    };
    let err = tls::server_config(&ServerOptions {
        certs: vec![mismatched],
        ..server_options()
    })
    .unwrap_err();
    assert!(err.contains("certificate and key"), "{err}");
    let twice = ServerOptions {
        certs: vec![cert(&[], "a"), cert(&[], "b")],
        ..server_options()
    };
    assert!(
        tls::server_config(&twice)
            .unwrap_err()
            .contains("two default")
    );
    let empty_roots = ClientOptions {
        roots: Roots::Only(Vec::new()),
        ..client_options()
    };
    assert!(
        tls::client_config(&empty_roots)
            .unwrap_err()
            .contains("no certificate")
    );
}
