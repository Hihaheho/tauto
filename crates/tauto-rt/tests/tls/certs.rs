//! The test certificates, made afresh by each test run so that no key sits in
//! the repository. `ca.pem` signs `a` (a.test, localhost), `b` (b.test) and
//! `client`; `other` is self-signed for a.test and not trusted. The CA key is
//! thrown away once they are signed.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use rcgen::{BasicConstraints, CertificateParams, DnType, IsCa, Issuer, KeyPair};

/// The directory that holds `ca.pem` and `<name>.pem` and `<name>.key` for
/// `a`, `b`, `client` and `other`.
pub fn dir() -> &'static Path {
    static DIR: OnceLock<PathBuf> = OnceLock::new();
    DIR.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!("tauto-tls-certs-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let write = |name: &str, text: String| std::fs::write(dir.join(name), text).unwrap();
        // Each has a name of its own: a verifier looks for the issuer by name,
        // and an `other` named like the CA would fail on its signature, not
        // on its issuer.
        let params = |cn: &str, names: &[&str]| {
            let names = names.iter().map(|n| n.to_string()).collect::<Vec<_>>();
            let mut p = CertificateParams::new(names).unwrap();
            p.distinguished_name.push(DnType::CommonName, cn);
            p
        };

        let ca_key = KeyPair::generate().unwrap();
        let mut ca_params = params("tauto test ca", &[]);
        ca_params.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
        write("ca.pem", ca_params.self_signed(&ca_key).unwrap().pem());
        let ca = Issuer::new(ca_params, ca_key);

        for (file, names) in [
            ("a", &["a.test", "localhost"][..]),
            ("b", &["b.test"]),
            ("client", &["client.test"]),
        ] {
            let key = KeyPair::generate().unwrap();
            let cert = params(file, names).signed_by(&key, &ca).unwrap();
            write(&format!("{file}.pem"), cert.pem());
            write(&format!("{file}.key"), key.serialize_pem());
        }
        let key = KeyPair::generate().unwrap();
        let cert = params("other", &["a.test"]).self_signed(&key).unwrap();
        write("other.pem", cert.pem());
        write("other.key", key.serialize_pem());
        dir
    })
}

/// The bytes of one file of [`dir`].
pub fn read(name: &str) -> Vec<u8> {
    std::fs::read(dir().join(name)).unwrap()
}
