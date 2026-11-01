//! TLS over a byte stream the program already holds (the `tls` feature),
//! terminated by rustls. The stream is any `Read + Write`: a TCP connection
//! of the standard effects, or a pipe in tests. Deadlines and shutdown are
//! the stream's: TLS adds no clock of its own.
//!
//! Certificates, keys and roots come in as PEM bytes the program read itself,
//! so TLS needs no permission beyond the ones that gave it the bytes and the
//! connection. Verification of the server is always on; there is no way to
//! turn it off, only to name which roots to trust.

use std::fmt;
use std::io::{self, Read, Write};
use std::sync::Arc;

use rustls::client::WebPkiServerVerifier;
use rustls::crypto::CryptoProvider;
use rustls::pki_types::pem::PemObject;
use rustls::pki_types::{CertificateDer, PrivateKeyDer, ServerName};
use rustls::server::{ClientHello, ResolvesServerCert, WebPkiClientVerifier};
use rustls::sign::CertifiedKey;
use rustls::{ClientConfig, ClientConnection, RootCertStore, ServerConfig, ServerConnection};

/// One certificate the server can present.
pub struct ServerCert {
    /// The SNI names it answers. Empty: the default, for a hello that names
    /// no server or a name no other certificate has.
    pub names: Vec<String>,
    /// The chain, leaf first, as PEM.
    pub chain_pem: Vec<u8>,
    /// Its private key, as PEM (PKCS#8, PKCS#1 or SEC1).
    pub key_pem: Vec<u8>,
}

pub struct ServerOptions {
    pub certs: Vec<ServerCert>,
    /// ALPN protocols in order of preference. Empty: no ALPN.
    pub alpn: Vec<Vec<u8>>,
    /// `Some(roots)`: ask for a client certificate and require one these
    /// roots (PEM) sign.
    pub client_roots: Option<Vec<u8>>,
}

/// The roots a client trusts.
pub enum Roots {
    /// The system's.
    System,
    /// The system's and these (PEM).
    SystemAnd(Vec<u8>),
    /// These alone (PEM).
    Only(Vec<u8>),
}

pub struct ClientOptions {
    pub roots: Roots,
    /// The client certificate: chain and key, as PEM.
    pub client_cert: Option<(Vec<u8>, Vec<u8>)>,
    pub alpn: Vec<Vec<u8>>,
}

fn provider() -> Arc<CryptoProvider> {
    Arc::new(rustls::crypto::aws_lc_rs::default_provider())
}

fn certs(pem: &[u8], what: &str) -> Result<Vec<CertificateDer<'static>>, String> {
    let certs = CertificateDer::pem_slice_iter(pem)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| format!("{what}: {e}"))?;
    if certs.is_empty() {
        return Err(format!("{what}: no certificate in the PEM"));
    }
    Ok(certs)
}

fn key(pem: &[u8]) -> Result<PrivateKeyDer<'static>, String> {
    PrivateKeyDer::from_pem_slice(pem).map_err(|e| format!("private key: {e}"))
}

fn root_store(pem: &[u8]) -> Result<RootCertStore, String> {
    let mut store = RootCertStore::empty();
    for cert in certs(pem, "roots")? {
        store.add(cert).map_err(|e| format!("roots: {e}"))?;
    }
    Ok(store)
}

/// Picks the certificate by the hello's SNI name, else the default.
#[derive(Debug)]
struct BySni {
    named: Vec<(String, Arc<CertifiedKey>)>,
    default: Option<Arc<CertifiedKey>>,
}

impl ResolvesServerCert for BySni {
    fn resolve(&self, hello: ClientHello<'_>) -> Option<Arc<CertifiedKey>> {
        hello
            .server_name()
            .and_then(|sni| {
                self.named
                    .iter()
                    .find(|(name, _)| name.eq_ignore_ascii_case(sni))
                    .map(|(_, key)| key.clone())
            })
            .or_else(|| self.default.clone())
    }
}

pub fn server_config(options: &ServerOptions) -> Result<Arc<ServerConfig>, String> {
    let provider = provider();
    let mut resolver = BySni {
        named: Vec::new(),
        default: None,
    };
    for cert in &options.certs {
        let chain = certs(&cert.chain_pem, "certificate chain")?;
        let signing = provider
            .key_provider
            .load_private_key(key(&cert.key_pem)?)
            .map_err(|e| format!("private key: {e}"))?;
        let certified = Arc::new(CertifiedKey::new(chain, signing));
        certified
            .keys_match()
            .map_err(|e| format!("certificate and key: {e}"))?;
        if cert.names.is_empty() {
            if resolver.default.is_some() {
                return Err("two default certificates (with no names)".into());
            }
            resolver.default = Some(certified);
        } else {
            for name in &cert.names {
                if resolver
                    .named
                    .iter()
                    .any(|(n, _)| n.eq_ignore_ascii_case(name))
                {
                    return Err(format!("two certificates for `{name}`"));
                }
                resolver.named.push((name.clone(), certified.clone()));
            }
        }
    }
    if resolver.named.is_empty() && resolver.default.is_none() {
        return Err("a server needs a certificate".into());
    }
    let builder = ServerConfig::builder_with_provider(provider.clone())
        .with_safe_default_protocol_versions()
        .map_err(|e| e.to_string())?;
    let builder = match &options.client_roots {
        None => builder.with_no_client_auth(),
        Some(pem) => {
            let verifier =
                WebPkiClientVerifier::builder_with_provider(Arc::new(root_store(pem)?), provider)
                    .build()
                    .map_err(|e| format!("client roots: {e}"))?;
            builder.with_client_cert_verifier(verifier)
        }
    };
    let mut config = builder.with_cert_resolver(Arc::new(resolver));
    config.alpn_protocols = options.alpn.clone();
    Ok(Arc::new(config))
}

pub fn client_config(options: &ClientOptions) -> Result<Arc<ClientConfig>, String> {
    let provider = provider();
    let verifier: Arc<dyn rustls::client::danger::ServerCertVerifier> = match &options.roots {
        Roots::System => Arc::new(
            rustls_platform_verifier::Verifier::new(provider.clone()).map_err(|e| e.to_string())?,
        ),
        Roots::SystemAnd(pem) => Arc::new(
            rustls_platform_verifier::Verifier::new_with_extra_roots(
                certs(pem, "roots")?,
                provider.clone(),
            )
            .map_err(|e| e.to_string())?,
        ),
        Roots::Only(pem) => WebPkiServerVerifier::builder_with_provider(
            Arc::new(root_store(pem)?),
            provider.clone(),
        )
        .build()
        .map_err(|e| format!("roots: {e}"))?,
    };
    let builder = ClientConfig::builder_with_provider(provider)
        .with_safe_default_protocol_versions()
        .map_err(|e| e.to_string())?
        .dangerous()
        .with_custom_certificate_verifier(verifier);
    let mut config = match &options.client_cert {
        None => builder.with_no_client_auth(),
        Some((chain, key_pem)) => builder
            .with_client_auth_cert(certs(chain, "client certificate")?, key(key_pem)?)
            .map_err(|e| format!("client certificate: {e}"))?,
    };
    config.alpn_protocols = options.alpn.clone();
    Ok(Arc::new(config))
}

/// An established TLS session over `S`.
pub struct TlsStream<S: Read + Write> {
    pub(crate) conn: rustls::Connection,
    pub(crate) sock: S,
}

impl<S: Read + Write> fmt::Debug for TlsStream<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TlsStream")
            .field("alpn", &self.alpn())
            .finish()
    }
}

fn handshake<S: Read + Write>(
    mut conn: rustls::Connection,
    mut sock: S,
) -> Result<TlsStream<S>, String> {
    while conn.is_handshaking() {
        conn.complete_io(&mut sock)
            .map_err(|e| format!("TLS handshake: {e}"))?;
    }
    Ok(TlsStream { conn, sock })
}

/// A server's session on `sock` whose handshake has not run yet.
pub(crate) fn server<S: Read + Write>(
    config: Arc<ServerConfig>,
    sock: S,
) -> Result<TlsStream<S>, String> {
    let conn = ServerConnection::new(config).map_err(|e| e.to_string())?;
    Ok(TlsStream {
        conn: conn.into(),
        sock,
    })
}

/// A client's session on `sock` whose handshake has not run yet.
pub(crate) fn client<S: Read + Write>(
    config: Arc<ClientConfig>,
    name: &str,
    sock: S,
) -> Result<TlsStream<S>, String> {
    let name =
        ServerName::try_from(name.to_owned()).map_err(|e| format!("server name `{name}`: {e}"))?;
    let conn = ClientConnection::new(config, name).map_err(|e| e.to_string())?;
    Ok(TlsStream {
        conn: conn.into(),
        sock,
    })
}

/// Answers a client's handshake on `sock`.
pub fn accept<S: Read + Write>(config: Arc<ServerConfig>, sock: S) -> Result<TlsStream<S>, String> {
    let t = server(config, sock)?;
    handshake(t.conn, t.sock)
}

/// Starts a handshake with the server `name` (sent as SNI and checked
/// against its certificate; an IP address is checked, not sent).
pub fn connect<S: Read + Write>(
    config: Arc<ClientConfig>,
    name: &str,
    sock: S,
) -> Result<TlsStream<S>, String> {
    let t = client(config, name, sock)?;
    handshake(t.conn, t.sock)
}

impl<S: Read + Write> TlsStream<S> {
    /// The protocol ALPN chose, if any.
    pub fn alpn(&self) -> Option<&[u8]> {
        self.conn.alpn_protocol()
    }

    /// On a server, the SNI name the client sent.
    pub fn server_name(&self) -> Option<&str> {
        match &self.conn {
            rustls::Connection::Server(c) => c.server_name(),
            rustls::Connection::Client(_) => None,
        }
    }

    /// The peer's leaf certificate (DER): the server's on a client, the
    /// verified client's on a server that asked for one.
    pub fn peer_certificate(&self) -> Option<&[u8]> {
        self.conn
            .peer_certificates()
            .and_then(|c| c.first())
            .map(|c| c.as_ref())
    }

    /// Up to `max` bytes; empty at the peer's close_notify. A peer that closes
    /// the stream without close_notify is an error, since the data may have
    /// been cut short.
    pub fn read(&mut self, max: usize) -> io::Result<Vec<u8>> {
        let mut buf = vec![0; max];
        loop {
            match self.conn.reader().read(&mut buf) {
                Ok(n) => {
                    buf.truncate(n);
                    return Ok(buf);
                }
                // Nothing decrypted yet: read more records. At the stream's
                // end the next `reader().read` answers `UnexpectedEof`.
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    self.conn.complete_io(&mut self.sock)?;
                }
                Err(e) => return Err(e),
            }
        }
    }

    pub fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.conn.writer().write_all(bytes)?;
        self.flush_tls()
    }

    /// Sends close_notify. The stream stays open for reading the rest and
    /// for the caller to shut down or close.
    pub fn close(&mut self) -> io::Result<()> {
        self.conn.send_close_notify();
        self.flush_tls()
    }

    fn flush_tls(&mut self) -> io::Result<()> {
        while self.conn.wants_write() {
            self.conn.write_tls(&mut self.sock)?;
        }
        self.sock.flush()
    }

    /// The stream underneath, to shut it down or close it.
    pub fn get_mut(&mut self) -> &mut S {
        &mut self.sock
    }
}
