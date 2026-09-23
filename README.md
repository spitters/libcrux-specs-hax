# libcrux-specs-hax

Hax-extractable pure-Rust specifications of the cryptographic primitives
provided by [libcrux](https://github.com/cryspen/libcrux). The code is
written in a restricted Rust subset that survives extraction via
[`hax`](https://github.com/hacspec/hax) into Coq/F\*/Lean, so the same text
acts as both a runnable reference and a formal specification. The crate
contains specifications of libcrux primitives; it contains no libcrux code.

## What's in here

| Module                 | Primitive                                                   |
| ---------------------- | ----------------------------------------------------------- |
| `sha256`, `sha512`, `sha3`, `blake2` | Hash functions                                |
| `hmac`                 | HMAC (generic over hash)                                    |
| `hkdf`                 | HMAC-based Extract-and-Expand Key Derivation (RFC 5869)     |
| `chacha20`, `poly1305`, `chacha20poly1305` | Stream cipher + MAC + AEAD             |
| `aes`, `aes128`, `gf128`, `aes_gcm` | AES primitives + GF(2^128) + AES-GCM             |
| `curve25519`, `x25519`, `edwards25519`, `ed25519` | Elliptic-curve primitives         |
| `p256`, `ecdsa_p256`   | NIST P-256 primitives + ECDSA signatures                    |
| `ed25519_comb`         | Fixed-base radix-16 comb scalar multiplication on edwards25519 |
| `ristretto255`         | The ristretto255 prime-order group (RFC 9496)               |
| `hash_to_field`        | `expand_message_xmd` (SHA-256, SHA-512) and `hash_to_field` (RFC 9380) |
| `hash_to_curve25519`   | Elligator 2 hash-to-curve suites for curve25519 and edwards25519 (RFC 9380, §8.5) |
| `hash_to_curve_p256`   | Simplified SWU hash-to-curve suites for P-256 (RFC 9380, §8.2) |
| `secret`               | The secret scalar type, released only by an explicit `declassify` |

About 9 300 lines across 26 modules. Zero production dependencies. The
crate needs no operating system: `std` is a default feature, and with
`default-features = false` the modules that hold a `Vec` take it from
`alloc`.

The crate root exports the trait `LibcruxCrypto`, a set of fixed-length
(32-byte) wrappers over the modules above, and `ConcreteLibcrux`, its
instantiation by the specifications in this crate. Downstream crates that
need to be generic over the primitive implementation depend on the trait;
extraction tooling extracts the concrete instance.

## Spec references

- FIPS 180-4 — SHA-256, SHA-384, SHA-512
- FIPS 202 — SHA-3, SHAKE
- RFC 7693 — BLAKE2b, BLAKE2s
- RFC 2104 — HMAC
- RFC 5869 — HKDF
- RFC 8439 — ChaCha20, Poly1305, ChaCha20-Poly1305
- FIPS 197 — AES
- NIST SP 800-38D — GHASH, AES-GCM
- RFC 7748 — X25519
- RFC 8032 — Ed25519
- FIPS 186-4, NIST SP 800-186 — P-256 curve and ECDSA (the P-256 domain
  parameters and the ECDSA algorithm are unchanged in FIPS 186-5)
- RFC 6979 §A.2.5 — the deterministic ECDSA P-256/SHA-256 test vector
- RFC 9380 — hashing to elliptic curves: `expand_message_xmd`,
  `hash_to_field`, Elligator 2 and simplified SWU
- RFC 9496 — ristretto255

## Running the tests

```bash
cargo test --release
```

Each module carries the known-answer tests printed in its standard; the
vectors of RFC 9380 Appendices J and K and of RFC 9496 Appendix A are in
`tests/hash_to_field_vectors.rs`, `tests/hash_to_curve25519_vectors.rs`,
`tests/hash_to_curve_p256_vectors.rs` and `tests/ristretto255_vectors.rs`. In
addition, `tests/cross_check.rs` differentially tests five functions —
`sha256_32`, `hmac_sha256_32`, `hkdf_extract_32`, `aes128_encrypt` and
`x25519::scalarmult` — against independent implementations pulled in as
dev-dependencies: the upstream
[`libcrux-specs`](https://github.com/spitters/libcrux-lean-specs) pure
specifications, Cryspen's `libcrux-sha2` and `libcrux-hmac`, and RustCrypto's
`aes`. These oracles are dev-dependencies only; nothing from them is linked
into the library.

## Hax extraction

The Lean extraction is committed at
`proofs/lean/extraction/Libcrux_specs_hax.lean`. The intermediate hax
frontend export (`hax_frontend_export.json`, about 80 MB) is not tracked;
regenerate it with

```bash
cargo hax json
```

which requires the `cargo-hax` frontend from the hax repository.

## Attribution

Thirteen modules are copies of `rust-specs/src/<module>.rs` in
[`spitters/libcrux-lean-specs`](https://github.com/spitters/libcrux-lean-specs)
(MIT, Copyright (c) 2026 Bas Spitters), at the commit pinned by
`Cargo.lock` for the `libcrux-specs` dev-dependency. Two are byte-identical
(`gf128`, `sha512`); three differ from upstream only in documentation
comments (`aes`, `curve25519`, `ecdsa_p256`); four differ only by the
`alloc::vec::Vec` import that the `no_std` build needs (`chacha20`,
`chacha20poly1305`, `ed25519`, `sha3`). Four differ in code:

- `blake2`: the key block is padded by a loop of `push` in place of
  `Vec::resize`.
- `edwards25519`: a borrow bit is converted to an integer by `if` in place of
  a `bool` cast.
- `poly1305`: carry bits are converted by `if` in place of `bool` casts, and
  the constant `P_LO` is written as a literal.
- `p256`: each correction step of `reduce_mod_p` adds the carry or borrow
  that its addition or subtraction of p produces, so it moves the value by
  exactly p.

Four modules are copies of the same upstream files with local additions,
besides the `alloc` import:

- `sha256`: adds the fixed-length wrapper `sha256_32`; the message bit
  length is computed in `u128` and truncated to `u64`.
- `aes_gcm`: the AAD and ciphertext bit lengths are computed in `u128` and
  truncated to `u64`; the block cipher is selected by the helper `gcm_block`.
- `hmac`: adds the fixed-length wrapper `hmac_sha256_32`.
- `hkdf`: adds the fixed-length wrappers `hkdf_extract_32` and
  `hkdf_expand_32`; `extract` calls `hmac_sha256` in each branch of the
  empty-salt test.

Nine modules are not from upstream: `lib.rs` (module list and the
`LibcruxCrypto` trait), `aes128` (a standalone AES-128 block cipher, the
value-passing form of the AES-128 in `aes`), `x25519` (fixed-length
wrappers over `curve25519`), and `ed25519_comb`, `ristretto255`,
`hash_to_field`, `hash_to_curve25519`, `hash_to_curve_p256` and `secret`.
Three of these take their layout from hacspec:

- `hash_to_field`: the text of `expand_message_xmd` and `hash_to_field` is
  adapted from the hacspec examples `edwards25519-hash` and `bls12-381-hash`
  ([hacspec/hacspec](https://github.com/hacspec/hacspec), MIT OR Apache-2.0;
  Malte Thomsen, Marcus Rasmussen, Tobias Vestergaard and the hacspec
  authors), rewritten over this crate's hash functions and field
  representations.
- `hash_to_curve25519`: the suite layout follows `edwards25519-hash` from the
  same repository; the function bodies transcribe the pseudocode of RFC 9380.
- `ristretto255`: the function layout follows `ristretto/src/ristretto.rs` of
  [hacspec/specs](https://github.com/hacspec/specs) (Apache-2.0); the
  function bodies transcribe the pseudocode of RFC 9496.

The `libcrux-sha2` and `libcrux-hmac` crates (Apache-2.0) and the
RustCrypto `aes` crate are test oracles only; they are not redistributed.

## License

MIT. See [`LICENSE`](./LICENSE).
