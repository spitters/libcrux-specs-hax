//! Pure Rust Ed25519 signature scheme specification (RFC 8032, Section 5.1).
//!
//! Uses `crate::sha512` for hashing and `crate::edwards25519` for curve
//! operations. No external dependencies.
//!
//! All functions are pure and value-passing.

use alloc::vec::Vec;

use crate::edwards25519::{
    ed25519_base_point, point_add, point_decode, point_encode, scalar_add, scalar_mult,
    scalar_mul_mod_l, scalar_reduce,
};
use crate::sha512::sha512;

/// Clamp a 32-byte hash prefix into a valid Ed25519 scalar.
///
/// Per RFC 8032: clear the lowest 3 bits, clear bit 255, set bit 254.
fn clamp(h: &[u8; 32]) -> [u8; 32] {
    let mut a = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        a[i] = h[i];
        i += 1;
    }
    a[0] &= 248;
    a[31] &= 127;
    a[31] |= 64;
    a
}

/// Derive the Ed25519 public key from a 32-byte secret key.
///
/// 1. Compute h = SHA-512(secret_key).
/// 2. Clamp h[0..32] to get scalar a.
/// 3. Return encode(a * B).
pub fn ed25519_public_key(secret_key: &[u8; 32]) -> [u8; 32] {
    let h = sha512(secret_key);
    let mut h_lo = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        h_lo[i] = h[i];
        i += 1;
    }
    let a = clamp(&h_lo);

    let base = ed25519_base_point();
    let public_point = scalar_mult(&a, &base);
    point_encode(&public_point)
}

/// Ed25519 signature generation (RFC 8032, Section 5.1.6).
///
/// Input: 32-byte secret key, arbitrary-length message.
/// Output: 64-byte signature (R_enc || S_enc).
///
/// Steps:
/// 1. h = SHA-512(secret_key)
/// 2. a = clamp(h[0..32])
/// 3. prefix = h[32..64]
/// 4. r = SHA-512(prefix || msg) mod L
/// 5. R = r * B
/// 6. public_key = encode(a * B)
/// 7. k = SHA-512(R_enc || public_key || msg) mod L
/// 8. S = (r + k * a) mod L
/// 9. Return R_enc || S_enc
pub fn ed25519_sign(secret_key: &[u8; 32], msg: &[u8]) -> [u8; 64] {
    let h = sha512(secret_key);

    // Extract scalar and prefix from hash.
    let mut h_lo = [0u8; 32];
    let mut prefix = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        h_lo[i] = h[i];
        prefix[i] = h[32 + i];
        i += 1;
    }
    let a = clamp(&h_lo);

    // Compute public key: A = a * B
    let base = ed25519_base_point();
    let public_point = scalar_mult(&a, &base);
    let public_key = point_encode(&public_point);

    // r = SHA-512(prefix || msg) mod L
    let mut r_input: Vec<u8> = Vec::new();
    i = 0;
    while i < 32 {
        r_input.push(prefix[i]);
        i += 1;
    }
    i = 0;
    while i < msg.len() {
        r_input.push(msg[i]);
        i += 1;
    }
    let r_hash = sha512(&r_input);
    let r_scalar = scalar_reduce(&r_hash);

    // R = r * B
    let r_point = scalar_mult(&r_scalar, &base);
    let r_enc = point_encode(&r_point);

    // k = SHA-512(R_enc || public_key || msg) mod L
    let mut k_input: Vec<u8> = Vec::new();
    i = 0;
    while i < 32 {
        k_input.push(r_enc[i]);
        i += 1;
    }
    i = 0;
    while i < 32 {
        k_input.push(public_key[i]);
        i += 1;
    }
    i = 0;
    while i < msg.len() {
        k_input.push(msg[i]);
        i += 1;
    }
    let k_hash = sha512(&k_input);
    let k_scalar = scalar_reduce(&k_hash);

    // S = (r + k * a) mod L
    let ka = scalar_mul_mod_l(&k_scalar, &a);
    let s = scalar_add(&r_scalar, &ka);

    // Signature = R_enc || S
    let mut signature = [0u8; 64];
    i = 0;
    while i < 32 {
        signature[i] = r_enc[i];
        signature[32 + i] = s[i];
        i += 1;
    }

    signature
}

/// Ed25519 signature verification (RFC 8032, Section 5.1.7).
///
/// Input: 32-byte public key, arbitrary-length message, 64-byte signature.
/// Output: true if the signature is valid.
///
/// Steps:
/// 1. A = decode(public_key)
/// 2. R = decode(signature[0..32])
/// 3. S = le_decode(signature[32..64])
/// 4. k = SHA-512(R_enc || public_key || msg) mod L
/// 5. Check: S * B == R + k * A
pub fn ed25519_verify(public_key: &[u8; 32], msg: &[u8], signature: &[u8; 64]) -> bool {
    // Decode public key.
    let a_point = match point_decode(public_key) {
        Some(p) => p,
        None => return false,
    };

    // Decode R from signature.
    let mut r_enc = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        r_enc[i] = signature[i];
        i += 1;
    }
    let r_point = match point_decode(&r_enc) {
        Some(p) => p,
        None => return false,
    };

    // Decode S from signature (32 bytes, little-endian).
    let mut s_bytes = [0u8; 32];
    i = 0;
    while i < 32 {
        s_bytes[i] = signature[32 + i];
        i += 1;
    }

    // Check S < L.
    let l_bytes: [u8; 32] = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
        0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
    ];
    // Compare S with L (little-endian): S must be < L.
    let mut s_ge_l = false;
    i = 32;
    while i > 0 {
        i -= 1;
        if s_bytes[i] > l_bytes[i] {
            s_ge_l = true;
            break;
        }
        if s_bytes[i] < l_bytes[i] {
            break;
        }
    }
    if s_ge_l {
        return false;
    }

    // Compute k = SHA-512(R_enc || public_key || msg) mod L
    let mut k_input: Vec<u8> = Vec::new();
    i = 0;
    while i < 32 {
        k_input.push(r_enc[i]);
        i += 1;
    }
    i = 0;
    while i < 32 {
        k_input.push(public_key[i]);
        i += 1;
    }
    i = 0;
    while i < msg.len() {
        k_input.push(msg[i]);
        i += 1;
    }
    let k_hash = sha512(&k_input);
    let k_scalar = scalar_reduce(&k_hash);

    // Compute S * B
    let base = ed25519_base_point();
    let sb = scalar_mult(&s_bytes, &base);

    // Compute R + k * A
    let ka = scalar_mult(&k_scalar, &a_point);
    let rka = point_add(&r_point, &ka);

    // Compare: encode both and check equality.
    let sb_enc = point_encode(&sb);
    let rka_enc = point_encode(&rka);

    sb_enc == rka_enc
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex_to_bytes(hex: &str) -> Vec<u8> {
        let mut bytes = Vec::new();
        let mut i = 0;
        while i < hex.len() {
            let hi = u8::from_str_radix(&hex[i..i + 1], 16).unwrap();
            let lo = u8::from_str_radix(&hex[i + 1..i + 2], 16).unwrap();
            bytes.push((hi << 4) | lo);
            i += 2;
        }
        bytes
    }

    fn hex_to_32(hex: &str) -> [u8; 32] {
        let v = hex_to_bytes(hex);
        let mut out = [0u8; 32];
        let mut i = 0;
        while i < 32 {
            out[i] = v[i];
            i += 1;
        }
        out
    }

    fn hex_to_64(hex: &str) -> [u8; 64] {
        let v = hex_to_bytes(hex);
        let mut out = [0u8; 64];
        let mut i = 0;
        while i < 64 {
            out[i] = v[i];
            i += 1;
        }
        out
    }

    /// RFC 8032, Section 7.1 — Test Vector 1 (empty message).
    ///
    /// Secret key: 9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60
    /// Public key: d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a
    /// Message: (empty)
    /// Signature: e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b
    #[test]
    fn test_rfc8032_vector1_keygen() {
        let sk = hex_to_32(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        );
        let expected_pk = hex_to_32(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        );
        let pk = ed25519_public_key(&sk);
        assert_eq!(pk, expected_pk);
    }

    #[test]
    fn test_rfc8032_vector1_sign() {
        let sk = hex_to_32(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        );
        let expected_sig = hex_to_64(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
             5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        );
        let msg: &[u8] = b"";
        let sig = ed25519_sign(&sk, msg);
        assert_eq!(sig, expected_sig);
    }

    #[test]
    fn test_rfc8032_vector1_verify() {
        let pk = hex_to_32(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        );
        let sig = hex_to_64(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
             5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        );
        let msg: &[u8] = b"";
        assert!(ed25519_verify(&pk, msg, &sig));
    }

    /// RFC 8032, Section 7.1 — Test Vector 2 (one-byte message 0x72).
    ///
    /// Secret key: 4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb
    /// Public key: 3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c
    /// Message: 72
    /// Signature: 92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e159c7e94b6b505da2c80c6ee3b05e2a1c0e0a3379ef3f8de1c1d40b
    #[test]
    fn test_rfc8032_vector2_keygen() {
        let sk = hex_to_32(
            "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
        );
        let expected_pk = hex_to_32(
            "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
        );
        let pk = ed25519_public_key(&sk);
        assert_eq!(pk, expected_pk);
    }

    #[test]
    fn test_rfc8032_vector2_sign() {
        let sk = hex_to_32(
            "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
        );
        let expected_sig = hex_to_64(
            "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
             085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
        );
        let msg: &[u8] = &[0x72];
        let sig = ed25519_sign(&sk, msg);
        assert_eq!(sig[..], expected_sig[..]);
    }

    #[test]
    fn test_rfc8032_vector2_verify() {
        let pk = hex_to_32(
            "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
        );
        let sig = hex_to_64(
            "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da\
             085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
        );
        let msg: &[u8] = &[0x72];
        assert!(ed25519_verify(&pk, msg, &sig));
    }

    /// A signature on a wrong message should fail.
    #[test]
    fn test_verify_wrong_message() {
        let pk = hex_to_32(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        );
        let sig = hex_to_64(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
             5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        );
        let msg: &[u8] = b"wrong";
        assert!(!ed25519_verify(&pk, msg, &sig));
    }

    /// Self-consistency: sign then verify.
    #[test]
    fn test_sign_verify_roundtrip() {
        let sk = hex_to_32(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        );
        let pk = ed25519_public_key(&sk);
        let msg = b"Hello, Ed25519!";
        let sig = ed25519_sign(&sk, msg);
        assert!(ed25519_verify(&pk, msg, &sig));
    }
}
