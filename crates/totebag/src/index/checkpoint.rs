//! The history of an index: a line of commits from a root with no parent,
//! each with one parent, each adding the batch in its `observations.eure`.
//! A checkpoint's digest fixes the whole prefix up to it:
//!
//! ```text
//! P(c) = 0x00                          at the root
//!      = 0x01 || raw32(H(parent(c)))   otherwise
//! H(c) = SHA256(UTF8("tauto-index-checkpoint-v1\0") || P(c)
//!               || frame(UTF8(GitRevision(c))) || frame(commit payload)
//!               || frame(Index.eure blob) || frame(observations.eure blob))
//! ```
//!
//! Every object read is hashed again by Git and compared with its ID; the two
//! files are read as blobs of mode 100644, not from a checkout.

use tauto_syntax::Sha256 as Hasher;

use super::ledger::{self, Batch, Config, Sha256};
use super::strict::hex_bytes;
use crate::git::Mirror;
use crate::spec::Rev;

/// At most this many commits in an index's history.
pub const MAX_HISTORY: usize = 100_000;

#[derive(Debug, Clone)]
pub struct Checkpoint {
    pub rev: Rev,
    pub digest: Sha256,
    pub batch: Batch,
}

#[derive(Debug, Clone)]
pub struct History {
    pub config: Config,
    /// The bytes of `Index.eure`, the same at every commit.
    pub config_bytes: Vec<u8>,
    /// Root first.
    pub checkpoints: Vec<Checkpoint>,
}

impl History {
    /// The index's ID: the digest of its root checkpoint.
    pub fn id(&self) -> Sha256 {
        self.checkpoints[0].digest
    }

    /// The SHA-256 of `Index.eure`.
    pub fn config_id(&self) -> Sha256 {
        hex_bytes(&tauto_syntax::sha256_hex(&self.config_bytes))
    }
}

struct Commit {
    tree: String,
    parents: Vec<String>,
    payload: Vec<u8>,
}

fn read_commit(mirror: &Mirror, rev: &Rev) -> Result<Commit, String> {
    let payload = mirror.commit(rev)?;
    let text = String::from_utf8_lossy(&payload);
    let mut tree = None;
    let mut parents = Vec::new();
    // The header ends at the first empty line.
    for line in text.split('\n').take_while(|l| !l.is_empty()) {
        if let Some(t) = line.strip_prefix("tree ") {
            tree = Some(t.to_string());
        } else if let Some(p) = line.strip_prefix("parent ") {
            parents.push(p.to_string());
        }
    }
    Ok(Commit {
        tree: tree.ok_or_else(|| say!("totebag-commit-no-tree", rev = rev.short()))?,
        parents,
        payload,
    })
}

fn root_blob(
    mirror: &Mirror,
    rev: &Rev,
    tree: &str,
    name: &str,
    max: usize,
) -> Result<Vec<u8>, String> {
    match mirror.root_entry(tree, name)? {
        Some((mode, oid)) if mode == "100644" => mirror.blob(&oid, max),
        Some((mode, _)) => Err(say!(
            "totebag-root-not-regular",
            name = name,
            rev = rev.short(),
            mode = &mode
        )),
        None => Err(say!("totebag-has-no", what = rev.short(), key = name)),
    }
}

fn frame(h: &mut Hasher, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_be_bytes());
    h.update(bytes);
}

pub fn digest(
    parent: Option<&Sha256>,
    rev: &Rev,
    payload: &[u8],
    config: &[u8],
    batch: &[u8],
) -> Sha256 {
    let mut h = Hasher::new();
    h.update(b"tauto-index-checkpoint-v1\0");
    match parent {
        None => h.update(&[0]),
        Some(p) => {
            h.update(&[1]);
            h.update(p);
        }
    }
    frame(&mut h, rev.to_string().as_bytes());
    frame(&mut h, payload);
    frame(&mut h, config);
    frame(&mut h, batch);
    hex_bytes(&h.finish_hex())
}

/// The history that ends at `head`, read from `mirror`: every commit back to
/// the root, each with at most one parent, `Index.eure` the same throughout,
/// the root's batch numbered 0 and empty.
pub fn history(mirror: &Mirror, head: &Rev) -> Result<History, String> {
    let mut line = Vec::new();
    let mut at = head.clone();
    loop {
        if line.len() >= MAX_HISTORY {
            return Err(say!("totebag-history-too-long", max = MAX_HISTORY));
        }
        let commit = read_commit(mirror, &at)?;
        let parent = match commit.parents.as_slice() {
            [] => None,
            [p] => Some(Rev::from_git(p)?),
            _ => {
                return Err(say!("totebag-history-merge", rev = at.short()));
            }
        };
        line.push((at.clone(), commit));
        match parent {
            Some(p) => at = p,
            None => break,
        }
    }
    line.reverse();
    let (root_rev, root) = &line[0];
    let config_bytes = root_blob(
        mirror,
        root_rev,
        &root.tree,
        ledger::CONFIG_FILE,
        ledger::MAX_CONFIG,
    )?;
    let config = ledger::config(&config_bytes)?;
    if config.git_object_format != head.format() {
        return Err(say!(
            "totebag-object-format-differs",
            file = ledger::CONFIG_FILE,
            said = &config.git_object_format,
            found = head.format()
        ));
    }
    let mut checkpoints: Vec<Checkpoint> = Vec::with_capacity(line.len());
    for (rev, commit) in &line {
        let this_config = root_blob(
            mirror,
            rev,
            &commit.tree,
            ledger::CONFIG_FILE,
            ledger::MAX_CONFIG,
        )?;
        if this_config != config_bytes {
            return Err(say!(
                "totebag-config-changed",
                file = ledger::CONFIG_FILE,
                rev = rev.short()
            ));
        }
        let batch_bytes = root_blob(
            mirror,
            rev,
            &commit.tree,
            ledger::BATCH_FILE,
            ledger::MAX_BATCH,
        )?;
        let batch = ledger::batch(&batch_bytes, &config.git_object_format)
            .map_err(|e| say!("totebag-at-rev", rev = rev.short(), error = e))?;
        let parent = checkpoints.last().map(|c| c.digest);
        if parent.is_none() && (batch.sequence != 0 || !batch.events.is_empty()) {
            return Err(say!("totebag-root-not-empty", rev = rev.short()));
        }
        let digest = digest(
            parent.as_ref(),
            rev,
            &commit.payload,
            &config_bytes,
            &batch_bytes,
        );
        checkpoints.push(Checkpoint {
            rev: rev.clone(),
            digest,
            batch,
        });
    }
    Ok(History {
        config,
        config_bytes,
        checkpoints,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_digest_fixes_its_parent() {
        let rev = Rev::from_git(&"1".repeat(40)).unwrap();
        let a = digest(None, &rev, b"c", b"i", b"o");
        let b = digest(Some(&a), &rev, b"c", b"i", b"o");
        let c = digest(Some(&b), &rev, b"c", b"i", b"o");
        assert_ne!(a, b);
        assert_ne!(b, c);
        // The frames keep one file's bytes from running into the next.
        assert_ne!(
            digest(None, &rev, b"c", b"io", b""),
            digest(None, &rev, b"c", b"i", b"o")
        );
        // The spelled form, by hand.
        let mut spelled = b"tauto-index-checkpoint-v1\0".to_vec();
        spelled.push(0);
        for part in [rev.to_string().as_bytes(), b"c", b"i", b"o"] {
            spelled.extend((part.len() as u64).to_be_bytes());
            spelled.extend(part);
        }
        assert_eq!(
            super::super::strict::hex_of(&a),
            tauto_syntax::sha256_hex(&spelled)
        );
    }
}
