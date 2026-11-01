# url

URLs after the WHATWG URL Standard: parsing, serialization, percent-encoding and
resolving a reference against a base. No dependencies beyond `std`, and no axioms.

A URL that this tote cannot handle exactly as the standard does is refused (`None`)
rather than given a different result.

## Use

| Function | What it does |
| --- | --- |
| `url_parse(t)` | Parses an absolute URL; `Some(u)` or `None` |
| `url_resolve(base, t)` | Parses `t` as a reference relative to `base` |
| `url_text(u)` | The serialization of `u` as `Text` |
| `parse_bytes(l)`, `serialize(u)` | The same on byte lists |
| `pct_encode(set, l)`, `pct_decode(l)` | Percent-encoding with one of the encode sets, and decoding |
| `url_valid(u)` | Whether `u` is in the normal form the parser produces |

```
url_text(url_parse("HTTP://Example.COM:80/a/./b/../c?x#y"))
// "http://example.com/a/c?x#y"
```

What is handled:

- Special schemes (`http`, `https`, `ws`, `wss`, `ftp`) with lower-cased hosts, default ports
  dropped, backslashes as slashes, and `.`/`..` segments (also `%2e`) removed.
- Other schemes with an authority, a path of segments, or an opaque path.
- Credentials, ports, queries and fragments, each encoded with its own encode set.
- Leading and trailing C0 controls and spaces, and tabs and newlines anywhere, removed.
- Relative references, checked against every example of RFC 3986 section 5.4.

## What is proved

In `proof/`:

- `pct_encode_idem`: encoding twice is encoding once, for every encode set.
- `pct_decode_encode`: decoding undoes encoding, for every set that encodes `%`.
- `parse_serialize`: `parse_bytes(serialize(u)) = Some(u)` for every `u` with `url_valid(u)`.
- `parse_valid`: whatever `parse_bytes` returns is valid.
- `parse_idem`: if `parse_bytes(l) = Some(u)` then `parse_bytes(serialize(u)) = Some(u)`, so
  parsing is a normalization that reaches its fixpoint in one step.

## Not yet handled

- `file:` URLs, IPv6 hosts, non-ASCII hosts (IDNA) and `xn--` labels, and `%` in special
  hosts. These are refused.
- IPv4 hosts other than canonical dotted decimal, such as `0x7f.1`. These are refused.
- The statements above at the `Text` level (`url_parse(url_text(u))`), and proofs about
  `url_resolve`; resolution is checked by the examples only.

## Check

```
tauto check examples/whatwg.taut
tauto check examples/resolve.taut
tauto check proof/bytes.taut
tauto check proof/percent.taut
tauto check proof/round.taut
tauto check proof/normal.taut
```
