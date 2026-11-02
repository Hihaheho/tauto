//! Reading an Eure document strictly: every key known, none twice, no hole,
//! no extension, no code literal, and a value only of the type asked for.
//! Nothing is fetched or run while reading.

use std::collections::BTreeMap;

use eure_document::document::node::NodeValue;
use eure_document::document::{EureDocument, NodeId};
use eure_document::text::Language;
use eure_document::value::{ObjectKey, PrimitiveValue as P};

/// At most this many levels of blocks and lists.
pub const MAX_DEPTH: usize = 64;

pub struct Doc {
    doc: EureDocument,
}

impl Doc {
    /// Parses `bytes` (UTF-8, at most `max` bytes) as Eure.
    pub fn parse(bytes: &[u8], name: &str, max: usize) -> Result<Doc, String> {
        if bytes.len() > max {
            return Err(say!("totebag-file-too-large", name = name, max = max));
        }
        let text =
            std::str::from_utf8(bytes).map_err(|_| say!("totebag-file-not-utf8", name = name))?;
        let doc = eure_reader::parse_to_document(text, name).map_err(|e| {
            say!(
                "totebag-at",
                place = name,
                error = e.to_string().lines().next().unwrap_or("")
            )
        })?;
        let d = Doc { doc };
        d.check_depth(d.root(), 0)
            .map_err(|e| say!("totebag-at", place = name, error = e))?;
        Ok(d)
    }

    pub fn root(&self) -> NodeId {
        self.doc.get_root_id()
    }

    fn check_depth(&self, id: NodeId, depth: usize) -> Result<(), String> {
        if depth > MAX_DEPTH {
            return Err(say!("totebag-too-deep", max = MAX_DEPTH));
        }
        let node = self.doc.node(id);
        if !node.extensions.is_empty() {
            return Err(say!("totebag-no-extension"));
        }
        match &node.content {
            NodeValue::Map(m) => {
                for (_, v) in m.iter() {
                    self.check_depth(*v, depth + 1)?;
                }
            }
            NodeValue::Array(a) => {
                for v in a.iter() {
                    self.check_depth(*v, depth + 1)?;
                }
            }
            NodeValue::Primitive(_) => {}
            NodeValue::Hole(_) => return Err(say!("totebag-no-hole")),
            _ => return Err(say!("totebag-unread-value")),
        }
        Ok(())
    }

    /// The fields of a block, to be taken one by one and then [`Fields::finish`]ed.
    pub fn fields(&self, id: NodeId, what: &str) -> Result<Fields<'_>, String> {
        let NodeValue::Map(m) = &self.doc.node(id).content else {
            return Err(say!("totebag-is-a-block", what = what));
        };
        let mut entries = BTreeMap::new();
        for (k, v) in m.iter() {
            let ObjectKey::String(k) = k else {
                return Err(say!("totebag-key-is-a-name", what = what));
            };
            entries.insert(k.clone(), *v);
        }
        Ok(Fields {
            doc: self,
            what: what.to_string(),
            entries,
        })
    }

    pub fn text(&self, id: NodeId) -> Result<String, String> {
        match &self.doc.node(id).content {
            NodeValue::Primitive(P::Text(t)) if t.language == Language::Plaintext => {
                Ok(t.content.clone())
            }
            _ => Err(say!("totebag-expected-quoted-text")),
        }
    }

    pub fn integer(&self, id: NodeId) -> Result<u64, String> {
        match &self.doc.node(id).content {
            NodeValue::Primitive(P::Integer(n)) => n
                .to_string()
                .parse::<u64>()
                .map_err(|_| say!("totebag-integer-range")),
            _ => Err(say!("totebag-expected-integer")),
        }
    }

    pub fn list(&self, id: NodeId, max: usize) -> Result<Vec<NodeId>, String> {
        match &self.doc.node(id).content {
            NodeValue::Array(a) if a.len() <= max => Ok(a.iter().copied().collect()),
            NodeValue::Array(_) => Err(say!("totebag-too-many-items", max = max)),
            _ => Err(say!("totebag-expected-list")),
        }
    }
}

pub struct Fields<'a> {
    doc: &'a Doc,
    what: String,
    entries: BTreeMap<String, NodeId>,
}

impl<'a> Fields<'a> {
    /// Whether the field `key` is there and not yet taken.
    pub fn has(&self, key: &str) -> bool {
        self.entries.contains_key(key)
    }

    pub fn optional(&mut self, key: &str) -> Option<NodeId> {
        self.entries.remove(key)
    }

    pub fn required(&mut self, key: &str) -> Result<NodeId, String> {
        self.entries
            .remove(key)
            .ok_or_else(|| say!("totebag-has-no", what = &self.what, key = key))
    }

    /// A required field, read by `read`, its errors naming the field.
    pub fn read<T>(
        &mut self,
        key: &str,
        read: impl FnOnce(&'a Doc, NodeId) -> Result<T, String>,
    ) -> Result<T, String> {
        let id = self.required(key)?;
        read(self.doc, id).map_err(|e| {
            say!(
                "totebag-at",
                place = format!("{}.{key}", self.what),
                error = e
            )
        })
    }

    pub fn text_as<T>(
        &mut self,
        key: &str,
        check: impl FnOnce(&str) -> Result<T, String>,
    ) -> Result<T, String> {
        self.read(key, |d, id| check(&d.text(id)?))
    }

    pub fn integer(&mut self, key: &str) -> Result<u64, String> {
        self.read(key, |d, id| d.integer(id))
    }

    /// Fails on a key not taken.
    pub fn finish(self) -> Result<(), String> {
        match self.entries.keys().next() {
            Some(k) => Err(say!("totebag-unknown-key-in", key = k, what = &self.what)),
            None => Ok(()),
        }
    }
}

/// A SHA-256 written `sha256:<64 lowercase hex>`.
pub fn sha256(s: &str) -> Result<[u8; 32], String> {
    let hex = s
        .strip_prefix("sha256:")
        .filter(|h| h.len() == 64 && h.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')))
        .ok_or_else(|| say!("totebag-bad-sha256", value = format!("{s:?}")))?;
    Ok(hex_bytes(hex))
}

pub fn hex_bytes<const N: usize>(hex: &str) -> [u8; N] {
    let mut out = [0u8; N];
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).expect("checked hex");
    }
    out
}

pub fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn is_leap(y: u64) -> bool {
    (y.is_multiple_of(4) && !y.is_multiple_of(100)) || y.is_multiple_of(400)
}

/// A time `YYYY-MM-DDTHH:MM:SSZ` in UTC, 1970 to 9999, as seconds since 1970.
pub fn time(s: &str) -> Result<u64, String> {
    let bad = || say!("totebag-bad-time", value = format!("{s:?}"));
    let b = s.as_bytes();
    if b.len() != 20
        || b[4] != b'-'
        || b[7] != b'-'
        || b[10] != b'T'
        || b[13] != b':'
        || b[16] != b':'
        || b[19] != b'Z'
    {
        return Err(bad());
    }
    let num = |r: std::ops::Range<usize>| -> Result<u64, String> {
        let part = &s[r];
        if part.bytes().all(|c| c.is_ascii_digit()) {
            Ok(part.parse().unwrap())
        } else {
            Err(bad())
        }
    };
    let (y, mo, d) = (num(0..4)?, num(5..7)?, num(8..10)?);
    let (h, mi, se) = (num(11..13)?, num(14..16)?, num(17..19)?);
    let leap = is_leap(y);
    let days_in = [
        31,
        if leap { 29 } else { 28 },
        31,
        30,
        31,
        30,
        31,
        31,
        30,
        31,
        30,
        31,
    ];
    if !(1970..=9999).contains(&y)
        || !(1..=12).contains(&mo)
        || d == 0
        || d > days_in[mo as usize - 1]
        || h > 23
        || mi > 59
        || se > 59
    {
        return Err(bad());
    }
    let mut days = 0u64;
    for year in 1970..y {
        days += if is_leap(year) { 366 } else { 365 };
    }
    days += days_in[..mo as usize - 1].iter().sum::<u64>() + d - 1;
    Ok(days * 86_400 + h * 3_600 + mi * 60 + se)
}

/// Seconds since 1970 as `YYYY-MM-DDTHH:MM:SSZ`, the form [`time`] reads.
pub fn time_text(secs: u64) -> String {
    let (mut days, rest) = (secs / 86_400, secs % 86_400);
    let mut y = 1970;
    while days >= if is_leap(y) { 366 } else { 365 } {
        days -= if is_leap(y) { 366 } else { 365 };
        y += 1;
    }
    let mut mo = 0;
    for (i, n) in [
        31,
        if is_leap(y) { 29 } else { 28 },
        31,
        30,
        31,
        30,
        31,
        31,
        30,
        31,
        30,
        31,
    ]
    .into_iter()
    .enumerate()
    {
        if days < n {
            mo = i + 1;
            break;
        }
        days -= n;
    }
    format!(
        "{y:04}-{mo:02}-{:02}T{:02}:{:02}:{:02}Z",
        days + 1,
        rest / 3_600,
        rest % 3_600 / 60,
        rest % 60
    )
}

/// A length of time in seconds, 0 to 315360000 (ten years).
pub fn seconds(n: u64) -> Result<u64, String> {
    if n <= 315_360_000 {
        Ok(n)
    } else {
        Err(say!("totebag-too-many-seconds", n = n))
    }
}

/// An alias of an index: 1 to 64 lowercase letters, digits and `-`, starting
/// with a letter; `local` is the local witness.
pub fn alias(s: &str) -> Result<String, String> {
    if crate::valid_name(s) {
        Ok(s.to_string())
    } else {
        Err(say!("totebag-bad-alias", value = format!("{s:?}")))
    }
}

/// An explanation: 1 to 4096 bytes.
pub fn reason(s: &str) -> Result<String, String> {
    if (1..=4096).contains(&s.len()) {
        Ok(s.to_string())
    } else {
        Err(say!("totebag-reason-length"))
    }
}

/// A package revision: 1 to 256 ASCII letters, digits and `._:+-`.
pub fn package_rev(s: &str) -> Result<String, String> {
    if (1..=256).contains(&s.len())
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b':' | b'+' | b'-'))
    {
        Ok(s.to_string())
    } else {
        Err(say!("totebag-bad-package-rev", value = format!("{s:?}")))
    }
}

/// An `https://` URL without credentials, query or fragment.
pub fn https_url(s: &str) -> Result<String, String> {
    crate::spec::check_url(s)?;
    if s.starts_with("https://") {
        Ok(s.to_string())
    } else {
        Err(say!("totebag-index-https", value = format!("{s:?}")))
    }
}

/// A full branch ref, `refs/heads/NAME`.
pub fn branch(s: &str) -> Result<String, String> {
    crate::spec::check_ref(s)?;
    if s.starts_with("refs/heads/") {
        Ok(s.to_string())
    } else {
        Err(say!("totebag-index-branch", value = format!("{s:?}")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn times() {
        assert_eq!(time("1970-01-01T00:00:00Z"), Ok(0));
        assert_eq!(time("2026-10-01T12:00:00Z"), Ok(1_790_856_000));
        assert_eq!(time("2000-02-29T23:59:59Z"), Ok(951_868_799));
        for t in [0, 951_868_799, 1_790_856_000, 253_402_300_799] {
            assert_eq!(time(&time_text(t)), Ok(t));
        }
        for bad in [
            "1969-12-31T23:59:59Z",
            "2026-02-29T00:00:00Z",
            "2026-13-01T00:00:00Z",
            "2026-10-01T24:00:00Z",
            "2026-10-01T12:00:60Z",
            "2026-10-01T12:00:00.5Z",
            "2026-10-01T12:00:00+09:00",
            "2026-10-01 12:00:00Z",
            "+026-10-01T12:00:00Z",
        ] {
            assert!(time(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn strict_documents() {
        let d = Doc::parse(b"a = 1\nb = \"x\"\n", "t", 100).unwrap();
        let mut f = d.fields(d.root(), "t").unwrap();
        assert_eq!(f.integer("a"), Ok(1));
        assert!(f.finish().is_err(), "b was not taken");
        for bad in [
            "a = !\n",
            "a = `x`\n",
            "a = 1.5\n",
            "a = -1\n",
            "a = true\n",
        ] {
            let read = Doc::parse(bad.as_bytes(), "t", 100).and_then(|d| {
                let mut f = d.fields(d.root(), "t")?;
                f.read("a", |d, id| {
                    d.integer(id).or_else(|_| d.text(id).map(|_| 0))
                })
            });
            assert!(read.is_err(), "{bad}");
        }
        assert!(Doc::parse(b"a = 1\na = 1\n", "t", 100).is_err());
        assert!(Doc::parse(b"a = 1\n", "t", 3).is_err());
        assert!(Doc::parse(b"a = \"\xff\"\n", "t", 100).is_err());
    }

    #[test]
    fn values() {
        assert!(sha256(&format!("sha256:{}", "ab".repeat(32))).is_ok());
        assert!(sha256(&format!("sha256:{}", "AB".repeat(32))).is_err());
        assert!(package_rev("0123abc").is_ok() && package_rev("v1.0.0+build").is_ok());
        assert!(package_rev("").is_err() && package_rev("a b").is_err());
        assert!(https_url("file:///x").is_err());
        assert!(branch("refs/tags/v1").is_err() && branch("refs/heads/main").is_ok());
        assert!(seconds(315_360_001).is_err());
    }
}
