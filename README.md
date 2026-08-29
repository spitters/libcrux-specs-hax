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

About 7 100 lines across 20 modules. Zero production dependencies.

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

## Running the tests

```bash
cargo test --release
```

Each module carries the known-answer tests printed in its standard. In
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
`Cargo.lock` for the `libcrux-specs` dev-dependency. Seven are byte-identical
(`blake2`, `chacha20`, `chacha20poly1305`, `ed25519`, `edwards25519`,
`gf128`, `sha512`); six differ from upstream only in documentation comments
(`aes`, `curve25519`, `ecdsa_p256`, `p256`, `poly1305`, `sha3`).

Four modules are copies of the same upstream files with local additions:

- `sha256`: adds the fixed-length wrapper `sha256_32`; the message bit
  length is computed in `u128` and truncated to `u64`.
- `aes_gcm`: the AAD and ciphertext bit lengths are computed in `u128` and
  truncated to `u64`.
- `hmac`: adds the fixed-length wrapper `hmac_sha256_32`.
- `hkdf`: adds the fixed-length wrappers `hkdf_extract_32` and
  `hkdf_expand_32`.

Three modules are not from upstream: `lib.rs` (module list and the
`LibcruxCrypto` trait), `aes128` (a standalone AES-128 block cipher, the
value-passing form of the AES-128 in `aes`) and `x25519` (fixed-length
wrappers over `curve25519`).

The `libcrux-sha2` and `libcrux-hmac` crates (Apache-2.0) and the
RustCrypto `aes` crate are test oracles only; they are not redistributed.

## License

MIT. See [`LICENSE`](./LICENSE).
