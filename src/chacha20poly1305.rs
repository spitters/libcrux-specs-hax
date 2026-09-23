//! Pure Rust ChaCha20-Poly1305 AEAD specification (RFC 8439, Section 2.8).
//!
//! ChaCha20-Poly1305 is an Authenticated Encryption with Associated Data (AEAD)
//! construction that combines:
//! - ChaCha20 for encryption (with counter starting at 1)
//! - Poly1305 for authentication (keyed by ChaCha20 block 0)
//!
//! The MAC covers both the associated data (AAD) and the ciphertext, with
//! lengths appended as little-endian 64-bit integers.
//!
//! No external dependencies. Uses `crate::chacha20` and `crate::poly1305`.

use alloc::vec::Vec;

use crate::chacha20::{chacha20_block, chacha20_encrypt};
use crate::poly1305::poly1305;

/// Pad data to a multiple of 16 bytes by appending zeros.
/// Returns the data followed by 0 to 15 zero bytes.
pub fn pad16(data: &[u8]) -> Vec<u8> {
    let mut padded = Vec::with_capacity(data.len() + 15);
    for i in 0..data.len() {
        padded.push(data[i]);
    }
    let remainder = data.len() % 16;
    if remainder != 0 {
        let pad_len = 16 - remainder;
        for _ in 0..pad_len {
            padded.push(0);
        }
    }
    padded
}

/// Encode a usize as 8 little-endian bytes (u64).
pub fn le64(value: usize) -> [u8; 8] {
    let v = value as u64;
    let mut out = [0u8; 8];
    for i in 0..8 {
        out[i] = (v >> (8 * i)) as u8;
    }
    out
}

/// Build the Poly1305 MAC input for AEAD (RFC 8439, Section 2.8).
///
/// ```text
/// mac_data = pad16(aad) || pad16(ciphertext) || le64(aad.len()) || le64(ciphertext.len())
/// ```
pub fn build_mac_data(aad: &[u8], ciphertext: &[u8]) -> Vec<u8> {
    let padded_aad = pad16(aad);
    let padded_ct = pad16(ciphertext);
    let aad_len = le64(aad.len());
    let ct_len = le64(ciphertext.len());

    let total_len = padded_aad.len() + padded_ct.len() + 8 + 8;
    let mut mac_data = Vec::with_capacity(total_len);

    for i in 0..padded_aad.len() {
        mac_data.push(padded_aad[i]);
    }
    for i in 0..padded_ct.len() {
        mac_data.push(padded_ct[i]);
    }
    for i in 0..8 {
        mac_data.push(aad_len[i]);
    }
    for i in 0..8 {
        mac_data.push(ct_len[i]);
    }

    mac_data
}

/// Generate the one-time Poly1305 key from ChaCha20 block 0.
///
/// The first 32 bytes of chacha20_block(key, nonce, 0) are used as the
/// Poly1305 key (RFC 8439, Section 2.6).
pub fn poly1305_key_gen(key: &[u8; 32], nonce: &[u8; 12]) -> [u8; 32] {
    let block = chacha20_block(key, nonce, 0);
    let mut poly_key = [0u8; 32];
    for i in 0..32 {
        poly_key[i] = block[i];
    }
    poly_key
}

/// Constant-time comparison of two 16-byte tags.
///
/// Returns true if and only if all bytes are equal. Evaluates all bytes
/// regardless of where a mismatch occurs.
pub fn constant_time_eq(a: &[u8; 16], b: &[u8; 16]) -> bool {
    let mut diff: u8 = 0;
    for i in 0..16 {
        diff |= a[i] ^ b[i];
    }
    diff == 0
}

/// Encrypt and authenticate with ChaCha20-Poly1305 (RFC 8439, Section 2.8).
///
/// 1. Generate one-time Poly1305 key from ChaCha20 block 0.
/// 2. Encrypt plaintext with ChaCha20 starting at counter 1.
/// 3. Compute Poly1305 tag over pad16(aad) || pad16(ciphertext) || le64(aad_len) || le64(ct_len).
///
/// Returns (ciphertext, tag).
pub fn chacha20_poly1305_encrypt(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    msg: &[u8],
) -> (Vec<u8>, [u8; 16]) {
    // Step 1: Generate Poly1305 key
    let poly_key = poly1305_key_gen(key, nonce);

    // Step 2: Encrypt
    let ciphertext = chacha20_encrypt(key, nonce, 1, msg);

    // Step 3: Compute tag
    let mac_data = build_mac_data(aad, &ciphertext);
    let tag = poly1305(&mac_data, &poly_key);

    (ciphertext, tag)
}

/// Decrypt and verify with ChaCha20-Poly1305 (RFC 8439, Section 2.8).
///
/// 1. Generate one-time Poly1305 key from ChaCha20 block 0.
/// 2. Recompute Poly1305 tag over pad16(aad) || pad16(ciphertext) || le64(aad_len) || le64(ct_len).
/// 3. If tag matches, decrypt ciphertext with ChaCha20 starting at counter 1.
///
/// Returns `Some(plaintext)` on success, `None` if authentication fails.
pub fn chacha20_poly1305_decrypt(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    ciphertext: &[u8],
    tag: &[u8; 16],
) -> Option<Vec<u8>> {
    // Step 1: Generate Poly1305 key
    let poly_key = poly1305_key_gen(key, nonce);

    // Step 2: Recompute tag
    let mac_data = build_mac_data(aad, ciphertext);
    let computed_tag = poly1305(&mac_data, &poly_key);

    // Step 3: Verify and decrypt
    if constant_time_eq(&computed_tag, tag) {
        let plaintext = chacha20_encrypt(key, nonce, 1, ciphertext);
        Some(plaintext)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// RFC 8439, Section 2.8.2: AEAD test vector.
    ///
    /// Key:       80:81:82:...9f (32 bytes)
    /// Nonce:     07:00:00:00:40:41:42:43:44:45:46:47
    /// AAD:       50:51:52:53:c0:c1:c2:c3:c4:c5:c6:c7
    /// Plaintext: "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."
    #[test]
    fn test_rfc8439_aead_encrypt() {
        let mut key = [0u8; 32];
        for i in 0..32 {
            key[i] = (0x80 + i) as u8;
        }

        #[rustfmt::skip]
        let nonce: [u8; 12] = [
            0x07, 0x00, 0x00, 0x00,
            0x40, 0x41, 0x42, 0x43,
            0x44, 0x45, 0x46, 0x47,
        ];

        #[rustfmt::skip]
        let aad: [u8; 12] = [
            0x50, 0x51, 0x52, 0x53,
            0xc0, 0xc1, 0xc2, 0xc3,
            0xc4, 0xc5, 0xc6, 0xc7,
        ];

        let plaintext = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";

        let (ciphertext, tag) = chacha20_poly1305_encrypt(&key, &nonce, &aad, plaintext);

        #[rustfmt::skip]
        let expected_ct: [u8; 114] = [
            0xd3, 0x1a, 0x8d, 0x34, 0x64, 0x8e, 0x60, 0xdb,
            0x7b, 0x86, 0xaf, 0xbc, 0x53, 0xef, 0x7e, 0xc2,
            0xa4, 0xad, 0xed, 0x51, 0x29, 0x6e, 0x08, 0xfe,
            0xa9, 0xe2, 0xb5, 0xa7, 0x36, 0xee, 0x62, 0xd6,
            0x3d, 0xbe, 0xa4, 0x5e, 0x8c, 0xa9, 0x67, 0x12,
            0x82, 0xfa, 0xfb, 0x69, 0xda, 0x92, 0x72, 0x8b,
            0x1a, 0x71, 0xde, 0x0a, 0x9e, 0x06, 0x0b, 0x29,
            0x05, 0xd6, 0xa5, 0xb6, 0x7e, 0xcd, 0x3b, 0x36,
            0x92, 0xdd, 0xbd, 0x7f, 0x2d, 0x77, 0x8b, 0x8c,
            0x98, 0x03, 0xae, 0xe3, 0x28, 0x09, 0x1b, 0x58,
            0xfa, 0xb3, 0x24, 0xe4, 0xfa, 0xd6, 0x75, 0x94,
            0x55, 0x85, 0x80, 0x8b, 0x48, 0x31, 0xd7, 0xbc,
            0x3f, 0xf4, 0xde, 0xf0, 0x8e, 0x4b, 0x7a, 0x9d,
            0xe5, 0x76, 0xd2, 0x65, 0x86, 0xce, 0xc6, 0x4b,
            0x61, 0x16,
        ];
        assert_eq!(ciphertext, expected_ct);

        #[rustfmt::skip]
        let expected_tag: [u8; 16] = [
            0x1a, 0xe1, 0x0b, 0x59, 0x4f, 0x09, 0xe2, 0x6a,
            0x7e, 0x90, 0x2e, 0xcb, 0xd0, 0x60, 0x06, 0x91,
        ];
        assert_eq!(tag, expected_tag);
    }

    /// RFC 8439, Section 2.8.2: AEAD decryption test (inverse of the encryption test).
    #[test]
    fn test_rfc8439_aead_decrypt() {
        let mut key = [0u8; 32];
        for i in 0..32 {
            key[i] = (0x80 + i) as u8;
        }

        #[rustfmt::skip]
        let nonce: [u8; 12] = [
            0x07, 0x00, 0x00, 0x00,
            0x40, 0x41, 0x42, 0x43,
            0x44, 0x45, 0x46, 0x47,
        ];

        #[rustfmt::skip]
        let aad: [u8; 12] = [
            0x50, 0x51, 0x52, 0x53,
            0xc0, 0xc1, 0xc2, 0xc3,
            0xc4, 0xc5, 0xc6, 0xc7,
        ];

        #[rustfmt::skip]
        let ciphertext: [u8; 114] = [
            0xd3, 0x1a, 0x8d, 0x34, 0x64, 0x8e, 0x60, 0xdb,
            0x7b, 0x86, 0xaf, 0xbc, 0x53, 0xef, 0x7e, 0xc2,
            0xa4, 0xad, 0xed, 0x51, 0x29, 0x6e, 0x08, 0xfe,
            0xa9, 0xe2, 0xb5, 0xa7, 0x36, 0xee, 0x62, 0xd6,
            0x3d, 0xbe, 0xa4, 0x5e, 0x8c, 0xa9, 0x67, 0x12,
            0x82, 0xfa, 0xfb, 0x69, 0xda, 0x92, 0x72, 0x8b,
            0x1a, 0x71, 0xde, 0x0a, 0x9e, 0x06, 0x0b, 0x29,
            0x05, 0xd6, 0xa5, 0xb6, 0x7e, 0xcd, 0x3b, 0x36,
            0x92, 0xdd, 0xbd, 0x7f, 0x2d, 0x77, 0x8b, 0x8c,
            0x98, 0x03, 0xae, 0xe3, 0x28, 0x09, 0x1b, 0x58,
            0xfa, 0xb3, 0x24, 0xe4, 0xfa, 0xd6, 0x75, 0x94,
            0x55, 0x85, 0x80, 0x8b, 0x48, 0x31, 0xd7, 0xbc,
            0x3f, 0xf4, 0xde, 0xf0, 0x8e, 0x4b, 0x7a, 0x9d,
            0xe5, 0x76, 0xd2, 0x65, 0x86, 0xce, 0xc6, 0x4b,
            0x61, 0x16,
        ];

        #[rustfmt::skip]
        let tag: [u8; 16] = [
            0x1a, 0xe1, 0x0b, 0x59, 0x4f, 0x09, 0xe2, 0x6a,
            0x7e, 0x90, 0x2e, 0xcb, 0xd0, 0x60, 0x06, 0x91,
        ];

        let result = chacha20_poly1305_decrypt(&key, &nonce, &aad, &ciphertext, &tag);
        assert!(result.is_some());

        let plaintext = result.unwrap();
        let expected = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
        assert_eq!(plaintext, expected);
    }

    /// Verify that a tampered ciphertext is rejected.
    #[test]
    fn test_aead_tampered_ciphertext() {
        let mut key = [0u8; 32];
        for i in 0..32 {
            key[i] = i as u8;
        }

        #[rustfmt::skip]
        let nonce: [u8; 12] = [
            0x07, 0x00, 0x00, 0x00,
            0x40, 0x41, 0x42, 0x43,
            0x44, 0x45, 0x46, 0x47,
        ];

        let aad = [0x50u8, 0x51, 0x52, 0x53];
        let plaintext = b"Hello, world!";

        let (mut ciphertext, tag) = chacha20_poly1305_encrypt(&key, &nonce, &aad, plaintext);

        // Tamper with ciphertext
        ciphertext[0] ^= 0xff;

        let result = chacha20_poly1305_decrypt(&key, &nonce, &aad, &ciphertext, &tag);
        assert!(result.is_none());
    }

    /// Verify that a tampered tag is rejected.
    #[test]
    fn test_aead_tampered_tag() {
        let mut key = [0u8; 32];
        for i in 0..32 {
            key[i] = i as u8;
        }

        #[rustfmt::skip]
        let nonce: [u8; 12] = [
            0x07, 0x00, 0x00, 0x00,
            0x40, 0x41, 0x42, 0x43,
            0x44, 0x45, 0x46, 0x47,
        ];

        let aad = [0x50u8, 0x51, 0x52, 0x53];
        let plaintext = b"Hello, world!";

        let (ciphertext, mut tag) = chacha20_poly1305_encrypt(&key, &nonce, &aad, plaintext);

        // Tamper with tag
        tag[0] ^= 0x01;

        let result = chacha20_poly1305_decrypt(&key, &nonce, &aad, &ciphertext, &tag);
        assert!(result.is_none());
    }

    /// Round-trip: encrypt then decrypt with empty AAD.
    #[test]
    fn test_aead_round_trip_no_aad() {
        let key = [0x42u8; 32];
        let nonce = [0x01u8; 12];
        let aad: &[u8] = &[];
        let plaintext = b"The quick brown fox jumps over the lazy dog";

        let (ciphertext, tag) = chacha20_poly1305_encrypt(&key, &nonce, aad, plaintext);
        let result = chacha20_poly1305_decrypt(&key, &nonce, aad, &ciphertext, &tag);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), plaintext);
    }
}
