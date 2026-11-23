# sha256

SHA-256 (FIPS 180-4) in Nib, for the identities Tauto writes: `sha256_hex(pieces)`
is the lowercase hex digest of the byte strings in `pieces` taken as one message,
so a caller that frames many parts (a source tree) never joins them first.

```
tauto run src/main.taut -- FILE…
```

prints the digest of each file, as `sha256sum` does without the name.
