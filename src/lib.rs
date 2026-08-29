//! Pure Rust cryptographic specifications for libcrux primitives.
//!
//! Each module provides pure, value-passing implementations of cryptographic
//! primitives matching the corresponding RFC/NIST specification, in the Rust
//! subset that the hax frontend extracts.
//!
//! The `LibcruxCrypto` trait provides fixed-length wrappers over the modules;
//! `ConcreteLibcrux` instantiates it with the specifications in this crate.

#![allow(clippy::manual_memcpy)]
#![allow(clippy::needless_range_loop)]
#![allow(clippy::manual_repeat_n)]
#![allow(clippy::assign_op_pattern)]
#![allow(clippy::needless_late_init)]
#![allow(clippy::needless_borrow)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::manual_div_ceil)]
#![allow(clippy::manual_range_contains)]
#![allow(clippy::manual_rotate)]
#![allow(clippy::same_item_push)]
#![allow(clippy::unnecessary_cast)]
#![allow(clippy::let_and_return)]
#![allow(clippy::len_zero)]
#![allow(unused_mut)]

// Hash functions
pub mod sha256;
pub mod sha512;
pub mod sha3;
pub mod blake2;

// MACs, KDFs, stream cipher and AEAD
pub mod hmac;
pub mod hkdf;
pub mod chacha20;
pub mod poly1305;
pub mod chacha20poly1305;

// Block ciphers and AES-GCM
pub mod aes128;
pub mod aes;
pub mod gf128;
pub mod aes_gcm;

// Elliptic curves
pub mod curve25519;
pub mod x25519;
pub mod p256;
pub mod edwards25519;
pub mod ed25519;
pub mod ecdsa_p256;

/// Fixed-length (32-byte) wrappers over the primitive modules, so that
/// downstream code and extraction tooling can be generic over the
/// implementation.
pub trait LibcruxCrypto {
    fn sha256_32(msg: [u8; 32]) -> [u8; 32];
    fn hmac_sha256_32(key: [u8; 32], msg: [u8; 32]) -> [u8; 32];
    fn hkdf_extract_32(salt: [u8; 32], ikm: [u8; 32]) -> [u8; 32];
    fn hkdf_expand_32(prk: [u8; 32], info: [u8; 32]) -> [u8; 32];
    fn aes128_encrypt(key: [u8; 16], block: [u8; 16]) -> [u8; 16];
    fn x25519_scalarmult(scalar: [u8; 32], point: [u8; 32]) -> [u8; 32];
    fn x25519_base(scalar: [u8; 32]) -> [u8; 32];
    fn ed25519_sign(secret_key: [u8; 32], msg: &[u8]) -> [u8; 64];
    fn ed25519_verify(public_key: [u8; 32], msg: &[u8], signature: [u8; 64]) -> bool;
}

/// Concrete instantiation using the pure specs in this crate.
pub struct ConcreteLibcrux;

impl LibcruxCrypto for ConcreteLibcrux {
    fn sha256_32(msg: [u8; 32]) -> [u8; 32] { sha256::sha256_32(msg) }
    fn hmac_sha256_32(key: [u8; 32], msg: [u8; 32]) -> [u8; 32] { hmac::hmac_sha256_32(key, msg) }
    fn hkdf_extract_32(salt: [u8; 32], ikm: [u8; 32]) -> [u8; 32] { hkdf::hkdf_extract_32(salt, ikm) }
    fn hkdf_expand_32(prk: [u8; 32], info: [u8; 32]) -> [u8; 32] { hkdf::hkdf_expand_32(prk, info) }
    fn aes128_encrypt(key: [u8; 16], block: [u8; 16]) -> [u8; 16] { aes128::aes128_encrypt(key, block) }
    fn x25519_scalarmult(scalar: [u8; 32], point: [u8; 32]) -> [u8; 32] { x25519::scalarmult(scalar, point) }
    fn x25519_base(scalar: [u8; 32]) -> [u8; 32] { x25519::base_mult(scalar) }
    fn ed25519_sign(secret_key: [u8; 32], msg: &[u8]) -> [u8; 64] {
        ed25519::ed25519_sign(&secret_key, msg)
    }
    fn ed25519_verify(public_key: [u8; 32], msg: &[u8], signature: [u8; 64]) -> bool {
        ed25519::ed25519_verify(&public_key, msg, &signature)
    }
}

/// Convenience: SHA-512 on a 64-byte input (for Ed25519 internal use).
pub fn sha512_64(msg: [u8; 64]) -> [u8; 64] {
    sha512::sha512(&msg)
}
