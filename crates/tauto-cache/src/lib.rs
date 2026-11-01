//! The build cache: what a build step made, kept under what it was made from,
//! for every project on this machine.
//!
//! An action is one step (`kind`, such as `verify` or `codegen`) run on named
//! inputs. Its [`ActionKey`] is the SHA-256 of those inputs in one canonical
//! form; each output is a blob kept under its own [`BlobDigest`], so two
//! actions that make the same bytes keep them once.
//!
//! ```text
//! $TAUTO_BUILD (else $XDG_CACHE_HOME/tauto/build, else ~/.cache/tauto/build)
//!   blobs/<hex>      an output, read-only
//!   actions-v2/<hex> the record of an action: its inputs' digests and outputs
//!   last-v2/<hex>    the key an action of one kind and subject last had
//!   tmp/             files being written
//! ```
//!
//! Everything is written to `tmp/` and renamed into place, so a file under
//! `blobs/` or `actions-v2/` is whole whenever it exists. An action is recorded
//! only after every blob it names is in place.

/// A message of this crate as text: `say!("cache-…", name = value, …)`.
macro_rules! say {
    ($($t:tt)*) => {
        ::tauto_message::msg!($($t)*).to_string()
    };
}

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use tauto_syntax::sha256_hex;

fn frame(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
    out.extend_from_slice(bytes);
}

/// The key of an action:
///
/// ```text
/// action-v1 = UTF8("tauto-action-v1\0") || frame(kind) || u64be(number of inputs)
///             || each input, in the byte order of its name:
///                frame(UTF8(name)) || frame(SHA256(value))
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ActionKey(String);

/// The SHA-256 of an output: `SHA256("tauto-blob-v1\0" || bytes)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BlobDigest(String);

impl ActionKey {
    pub fn hex(&self) -> &str {
        &self.0
    }
}

impl BlobDigest {
    pub fn of(bytes: &[u8]) -> BlobDigest {
        let mut b = b"tauto-blob-v1\0".to_vec();
        b.extend_from_slice(bytes);
        BlobDigest(sha256_hex(&b))
    }

    pub fn hex(&self) -> &str {
        &self.0
    }
}

/// What an action is run on. A name is given once; the order they are given
/// in does not change the key.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Action {
    pub kind: String,
    /// What the action is run for (a tote, a module), used only to explain a
    /// miss by the action of the same kind and subject before it.
    pub subject: String,
    /// Each input's SHA-256, by name.
    inputs: BTreeMap<String, String>,
}

impl Action {
    pub fn new(kind: &str, subject: &str) -> Action {
        Action {
            kind: kind.to_string(),
            subject: subject.to_string(),
            inputs: BTreeMap::new(),
        }
    }

    /// Adds the input `name`; a name given twice is a mistake of the caller.
    pub fn input(mut self, name: &str, value: &[u8]) -> Action {
        let old = self.inputs.insert(name.to_string(), sha256_hex(value));
        assert!(old.is_none(), "the input {name} is given twice");
        self
    }

    pub fn key(&self) -> ActionKey {
        let mut b = b"tauto-action-v1\0".to_vec();
        frame(&mut b, self.kind.as_bytes());
        b.extend_from_slice(&(self.inputs.len() as u64).to_be_bytes());
        for (name, digest) in &self.inputs {
            frame(&mut b, name.as_bytes());
            frame(&mut b, digest.as_bytes());
        }
        ActionKey(sha256_hex(&b))
    }

    fn last_name(&self) -> String {
        let mut b = b"tauto-last-v1\0".to_vec();
        frame(&mut b, self.kind.as_bytes());
        frame(&mut b, self.subject.as_bytes());
        sha256_hex(&b)
    }
}

/// What a recorded action made: each output's digest, by name.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Outputs(pub BTreeMap<String, BlobDigest>);

/// Why an action is or is not in the cache.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Explain {
    Hit(ActionKey),
    /// No action of this kind and subject was recorded before.
    New,
    /// The one recorded before had other inputs.
    Changed {
        changed: Vec<String>,
        added: Vec<String>,
        removed: Vec<String>,
    },
    /// The inputs are the ones recorded before, but its record or a blob it
    /// names is gone.
    Lost,
}

#[derive(Debug, Clone)]
pub struct BuildCache {
    root: PathBuf,
}

impl BuildCache {
    /// The cache the environment names.
    pub fn from_env() -> Result<BuildCache, String> {
        let root = match std::env::var("TAUTO_BUILD") {
            Ok(v) if !v.is_empty() => PathBuf::from(v),
            _ => match std::env::var("XDG_CACHE_HOME") {
                Ok(v) if !v.is_empty() => PathBuf::from(v).join("tauto/build"),
                _ => match std::env::var("HOME") {
                    Ok(h) if !h.is_empty() => PathBuf::from(h).join(".cache/tauto/build"),
                    _ => return Err(say!("cache-no-place")),
                },
            },
        };
        Ok(BuildCache::at(root))
    }

    pub fn at(root: PathBuf) -> BuildCache {
        BuildCache { root }
    }

    pub fn blob_path(&self, d: &BlobDigest) -> PathBuf {
        self.root.join("blobs").join(d.hex())
    }

    /// Keeps `bytes`, unless they are kept already.
    pub fn put_blob(&self, bytes: &[u8]) -> Result<BlobDigest, String> {
        let d = BlobDigest::of(bytes);
        let dest = self.blob_path(&d);
        if !dest.is_file() {
            self.publish(&dest, bytes, true)?;
        }
        Ok(d)
    }

    /// The blob `d`, checked to be still those bytes; none when it is not
    /// here or has changed.
    pub fn get_blob(&self, d: &BlobDigest) -> Option<Vec<u8>> {
        let bytes = std::fs::read(self.blob_path(d)).ok()?;
        (BlobDigest::of(&bytes) == *d).then_some(bytes)
    }

    /// Records what `action` made. Every output must already be a blob here.
    pub fn put(&self, action: &Action, outputs: &Outputs) -> Result<ActionKey, String> {
        for (name, d) in &outputs.0 {
            if !self.blob_path(d).is_file() {
                return Err(say!("cache-no-blob", output = name, blob = d.hex()));
            }
        }
        let key = action.key();
        let mut bytes = b"tauto-action-record-v2\0".to_vec();
        frame(&mut bytes, action.kind.as_bytes());
        bytes.extend_from_slice(&(action.inputs.len() as u64).to_be_bytes());
        for (name, digest) in &action.inputs {
            frame(&mut bytes, name.as_bytes());
            frame(&mut bytes, digest.as_bytes());
        }
        bytes.extend_from_slice(&(outputs.0.len() as u64).to_be_bytes());
        for (name, d) in &outputs.0 {
            frame(&mut bytes, name.as_bytes());
            frame(&mut bytes, d.hex().as_bytes());
        }
        self.publish(&self.root.join("actions-v2").join(key.hex()), &bytes, true)?;
        self.publish(
            &self.root.join("last-v2").join(action.last_name()),
            key.hex().as_bytes(),
            false,
        )?;
        Ok(key)
    }

    /// What `action` made, when it is recorded and every output is still here.
    pub fn get(&self, action: &Action) -> Option<Outputs> {
        let (_, outputs) = self.read(&action.key())?;
        outputs
            .0
            .values()
            .all(|d| self.blob_path(d).is_file())
            .then_some(outputs)
    }

    /// Why `action` is or is not in the cache.
    pub fn explain(&self, action: &Action) -> Explain {
        let key = action.key();
        if self.get(action).is_some() {
            return Explain::Hit(key);
        }
        let last = std::fs::read_to_string(self.root.join("last-v2").join(action.last_name()))
            .ok()
            .and_then(|k| self.read(&ActionKey(k.trim().to_string())));
        let Some((before, _)) = last else {
            return Explain::New;
        };
        if before == action.inputs {
            return Explain::Lost;
        }
        let changed = action
            .inputs
            .iter()
            .filter(|(n, d)| before.get(*n).is_some_and(|b| b != *d))
            .map(|(n, _)| n.clone())
            .collect();
        let added = action
            .inputs
            .keys()
            .filter(|n| !before.contains_key(*n))
            .cloned()
            .collect();
        let removed = before
            .keys()
            .filter(|n| !action.inputs.contains_key(*n))
            .cloned()
            .collect();
        Explain::Changed {
            changed,
            added,
            removed,
        }
    }

    /// The inputs and outputs of the record `key`; none when it is not here
    /// or cannot be read.
    fn read(&self, key: &ActionKey) -> Option<(BTreeMap<String, String>, Outputs)> {
        let bytes = std::fs::read(self.root.join("actions-v2").join(key.hex())).ok()?;
        let mut reader = RecordReader(bytes.strip_prefix(b"tauto-action-record-v2\0")?);
        let kind = reader.text()?.to_string();
        let inputs = reader.entries()?;
        let outputs = Outputs(
            reader
                .entries()?
                .into_iter()
                .map(|(n, d)| (n, BlobDigest(d)))
                .collect(),
        );
        let action = Action {
            kind,
            subject: String::new(),
            inputs,
        };
        if !reader.0.is_empty() || action.key() != *key {
            return None;
        }
        Some((action.inputs, outputs))
    }

    /// Writes `bytes` to `tmp/` and renames them to `dest`.
    fn publish(&self, dest: &Path, bytes: &[u8], read_only: bool) -> Result<(), String> {
        let at = |place: &Path, e: std::io::Error| {
            say!(
                "cache-at",
                place = place.display().to_string(),
                error = e.to_string()
            )
        };
        let tmp_root = self.root.join("tmp");
        std::fs::create_dir_all(&tmp_root).map_err(|e| at(&tmp_root, e))?;
        if let Some(parent) = dest.parent() {
            std::fs::create_dir_all(parent).map_err(|e| at(parent, e))?;
        }
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let tmp = tmp_root.join(format!("{}-{nanos}", std::process::id()));
        let written = std::fs::write(&tmp, bytes).and_then(|()| {
            if read_only {
                let mut p = std::fs::metadata(&tmp)?.permissions();
                p.set_readonly(true);
                std::fs::set_permissions(&tmp, p)?;
            }
            std::fs::rename(&tmp, dest)
        });
        written.map_err(|e| {
            let _ = std::fs::remove_file(&tmp);
            at(dest, e)
        })
    }
}

/// Length-delimited UTF-8 fields keep names independent of record separators.
struct RecordReader<'a>(&'a [u8]);

impl<'a> RecordReader<'a> {
    fn number(&mut self) -> Option<usize> {
        let (number, rest) = self.0.split_at_checked(8)?;
        self.0 = rest;
        usize::try_from(u64::from_be_bytes(number.try_into().ok()?)).ok()
    }

    fn text(&mut self) -> Option<&'a str> {
        let length = self.number()?;
        let (text, rest) = self.0.split_at_checked(length)?;
        self.0 = rest;
        std::str::from_utf8(text).ok()
    }

    fn entries(&mut self) -> Option<BTreeMap<String, String>> {
        let count = self.number()?;
        let mut entries = BTreeMap::new();
        for _ in 0..count {
            let name = self.text()?.to_string();
            let digest = self.text()?;
            if digest.len() != 64
                || !digest
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            {
                return None;
            }
            if entries.insert(name, digest.to_string()).is_some() {
                return None;
            }
        }
        Some(entries)
    }
}
