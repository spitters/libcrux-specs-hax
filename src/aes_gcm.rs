//! Pure Rust AES-GCM specification (NIST SP 800-38D).
//!
//! No external dependencies. All functions are pure and value-passing.
//! Supports AES-128-GCM and AES-256-GCM.
//!
//! AES-GCM combines AES in counter mode (CTR) for encryption with the
//! GHASH universal hash function for authentication.

use alloc::vec::Vec;

use crate::aes;
use crate::gf128;

/// Increment the rightmost 32 bits of a 16-byte counter block (big-endian).
fn inc32(counter: [u8; 16]) -> [u8; 16] {
    let mut result = counter;

    // Read last 4 bytes as big-endian u32, increment, write back
    let ctr = u32::from_be_bytes([result[12], result[13], result[14], result[15]]);
    let incremented = ctr.wrapping_add(1);
    let bytes = incremented.to_be_bytes();
    result[12] = bytes[0];
    result[13] = bytes[1];
    result[14] = bytes[2];
    result[15] = bytes[3];

    result
}

/// XOR a keystream block with a data block, handling partial last blocks.
fn xor_block(data: &[u8], keystream: [u8; 16]) -> Vec<u8> {
    let mut result = Vec::new();
    let len = data.len();
    let mut i = 0;
    while i < len {
        result.push(data[i] ^ keystream[i]);
        i += 1;
    }
    result
}

/// Build the GHASH input: A || pad(A) || C || pad(C) || len(A) || len(C)
///
/// Where pad(X) pads X to a 16-byte boundary with zeros, and lengths are
/// in bits encoded as big-endian u64.
fn build_ghash_input(aad: &[u8], ciphertext: &[u8]) -> Vec<u8> {
    let mut input = Vec::new();

    // A (AAD) padded to 16-byte boundary
    let mut i = 0;
    while i < aad.len() {
        input.push(aad[i]);
        i += 1;
    }
    let aad_pad = (16 - (aad.len() % 16)) % 16;
    i = 0;
    while i < aad_pad {
        input.push(0);
        i += 1;
    }

    // C (ciphertext) padded to 16-byte boundary
    i = 0;
    while i < ciphertext.len() {
        input.push(ciphertext[i]);
        i += 1;
    }
    let ct_pad = (16 - (ciphertext.len() % 16)) % 16;
    i = 0;
    while i < ct_pad {
        input.push(0);
        i += 1;
    }

    // Length block: [len(A) in bits as u64 BE] || [len(C) in bits as u64 BE]
    // Compute in u128 then truncate to u64 to avoid a debug-mode panic on
    // multiplication overflow when the byte length is >= 2^61. The truncation
    // matches u64.to_be_bytes() under saturating semantics, so the wire
    // format is unchanged for all practical inputs. Per NIST SP 800-38D the
    // length field is `mod 2^64` regardless, so this is spec-conformant.
    let aad_bits = ((aad.len() as u128) * 8) as u64;
    let ct_bits = ((ciphertext.len() as u128) * 8) as u64;
    let aad_len_bytes = aad_bits.to_be_bytes();
    let ct_len_bytes = ct_bits.to_be_bytes();
    i = 0;
    while i < 8 {
        input.push(aad_len_bytes[i]);
        i += 1;
    }
    i = 0;
    while i < 8 {
        input.push(ct_len_bytes[i]);
        i += 1;
    }

    input
}

/// One AES block encryption under the selected key: AES-256 with `k32` when
/// `key256` holds, AES-128 with `k16` otherwise.
fn gcm_block(key256: bool, k16: [u8; 16], k32: [u8; 32], block: [u8; 16]) -> [u8; 16] {
    if key256 {
        aes::aes256_encrypt(k32, block)
    } else {
        aes::aes128_encrypt(k16, block)
    }
}

/// AES-GCM encryption for either key size.
///
/// key256 selects AES-256 with key k32; otherwise AES-128 with key k16. The
/// key that is not selected is ignored.
/// nonce: 12-byte nonce (IV).
/// aad: additional authenticated data (not encrypted, but authenticated).
/// plaintext: data to encrypt and authenticate.
///
/// Returns (ciphertext, tag).
fn aes_gcm_encrypt_generic(
    key256: bool,
    k16: [u8; 16],
    k32: [u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    plaintext: &[u8],
) -> (Vec<u8>, [u8; 16]) {
    // Step 1: H = AES_K(0^128) — hash subkey
    let h_bytes = gcm_block(key256, k16, k32, [0u8; 16]);
    let h = gf128::bytes_to_u128(&h_bytes);

    // Step 2: J0 = nonce || 0x00000001 — initial counter block (for 96-bit nonce)
    let mut j0 = [0u8; 16];
    let mut i = 0;
    while i < 12 {
        j0[i] = nonce[i];
        i += 1;
    }
    j0[12] = 0x00;
    j0[13] = 0x00;
    j0[14] = 0x00;
    j0[15] = 0x01;

    // Step 3: Encrypt plaintext using CTR mode starting from inc32(J0)
    let mut ciphertext = Vec::new();
    let num_blocks = (plaintext.len() + 15) / 16;
    let mut counter = j0;

    i = 0;
    while i < num_blocks {
        counter = inc32(counter);
        let keystream = gcm_block(key256, k16, k32, counter);

        let block_start = i * 16;
        let block_end = if block_start + 16 > plaintext.len() {
            plaintext.len()
        } else {
            block_start + 16
        };

        let encrypted = xor_block(&plaintext[block_start..block_end], keystream);
        let mut j = 0;
        while j < encrypted.len() {
            ciphertext.push(encrypted[j]);
            j += 1;
        }

        i += 1;
    }

    // Step 4: Compute GHASH over AAD and ciphertext
    let ghash_input = build_ghash_input(aad, &ciphertext);
    let s = gf128::ghash(h, &ghash_input);

    // Step 5: Tag = AES_K(J0) XOR S
    let encrypted_j0 = gcm_block(key256, k16, k32, j0);
    let encrypted_j0_val = gf128::bytes_to_u128(&encrypted_j0);
    let tag_val = encrypted_j0_val ^ s;
    let tag = gf128::u128_to_bytes(tag_val);

    (ciphertext, tag)
}

/// AES-GCM decryption for either key size.
///
/// Returns Some(plaintext) if the tag is valid, None otherwise.
fn aes_gcm_decrypt_generic(
    key256: bool,
    k16: [u8; 16],
    k32: [u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    ciphertext: &[u8],
    tag: &[u8; 16],
) -> Option<Vec<u8>> {
    // Step 1: H = AES_K(0^128) — hash subkey
    let h_bytes = gcm_block(key256, k16, k32, [0u8; 16]);
    let h = gf128::bytes_to_u128(&h_bytes);

    // Step 2: J0 = nonce || 0x00000001
    let mut j0 = [0u8; 16];
    let mut i = 0;
    while i < 12 {
        j0[i] = nonce[i];
        i += 1;
    }
    j0[12] = 0x00;
    j0[13] = 0x00;
    j0[14] = 0x00;
    j0[15] = 0x01;

    // Step 3: Compute GHASH over AAD and ciphertext to verify tag
    let ghash_input = build_ghash_input(aad, ciphertext);
    let s = gf128::ghash(h, &ghash_input);

    let encrypted_j0 = gcm_block(key256, k16, k32, j0);
    let encrypted_j0_val = gf128::bytes_to_u128(&encrypted_j0);
    let expected_tag_val = encrypted_j0_val ^ s;
    let expected_tag = gf128::u128_to_bytes(expected_tag_val);

    // Constant-time comparison (spec-level: simple byte comparison)
    let mut tag_ok = true;
    i = 0;
    while i < 16 {
        if tag[i] != expected_tag[i] {
            tag_ok = false;
        }
        i += 1;
    }

    if !tag_ok {
        return None;
    }

    // Step 4: Decrypt ciphertext using CTR mode starting from inc32(J0)
    let mut plaintext = Vec::new();
    let num_blocks = (ciphertext.len() + 15) / 16;
    let mut counter = j0;

    i = 0;
    while i < num_blocks {
        counter = inc32(counter);
        let keystream = gcm_block(key256, k16, k32, counter);

        let block_start = i * 16;
        let block_end = if block_start + 16 > ciphertext.len() {
            ciphertext.len()
        } else {
            block_start + 16
        };

        let decrypted = xor_block(&ciphertext[block_start..block_end], keystream);
        let mut j = 0;
        while j < decrypted.len() {
            plaintext.push(decrypted[j]);
            j += 1;
        }

        i += 1;
    }

    Some(plaintext)
}

// --- AES-128-GCM ---

/// AES-128-GCM authenticated encryption (NIST SP 800-38D).
///
/// Returns (ciphertext, 16-byte authentication tag).
pub fn aes128_gcm_encrypt(
    key: &[u8; 16],
    nonce: &[u8; 12],
    aad: &[u8],
    plaintext: &[u8],
) -> (Vec<u8>, [u8; 16]) {
    aes_gcm_encrypt_generic(
        false,
        *key,
        [0u8; 32],
        nonce,
        aad,
        plaintext,
    )
}

/// AES-128-GCM authenticated decryption (NIST SP 800-38D).
///
/// Returns Some(plaintext) if the tag verifies, None otherwise.
pub fn aes128_gcm_decrypt(
    key: &[u8; 16],
    nonce: &[u8; 12],
    aad: &[u8],
    ciphertext: &[u8],
    tag: &[u8; 16],
) -> Option<Vec<u8>> {
    aes_gcm_decrypt_generic(
        false,
        *key,
        [0u8; 32],
        nonce,
        aad,
        ciphertext,
        tag,
    )
}

// --- AES-256-GCM ---

/// AES-256-GCM authenticated encryption (NIST SP 800-38D).
///
/// Returns (ciphertext, 16-byte authentication tag).
pub fn aes256_gcm_encrypt(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    plaintext: &[u8],
) -> (Vec<u8>, [u8; 16]) {
    aes_gcm_encrypt_generic(
        true,
        [0u8; 16],
        *key,
        nonce,
        aad,
        plaintext,
    )
}

/// AES-256-GCM authenticated decryption (NIST SP 800-38D).
///
/// Returns Some(plaintext) if the tag verifies, None otherwise.
pub fn aes256_gcm_decrypt(
    key: &[u8; 32],
    nonce: &[u8; 12],
    aad: &[u8],
    ciphertext: &[u8],
    tag: &[u8; 16],
) -> Option<Vec<u8>> {
    aes_gcm_decrypt_generic(
        true,
        [0u8; 16],
        *key,
        nonce,
        aad,
        ciphertext,
        tag,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// NIST SP 800-38D, Test Case 1: AES-128-GCM with empty plaintext and empty AAD.
    #[test]
    fn test_aes128_gcm_test_case_1() {
        let key = [0u8; 16];
        let nonce = [0u8; 12];
        let aad: &[u8] = &[];
        let plaintext: &[u8] = &[];

        let expected_tag: [u8; 16] = [
            0x58, 0xe2, 0xfc, 0xce, 0xfa, 0x7e, 0x30, 0x61,
            0x36, 0x7f, 0x1d, 0x57, 0xa4, 0xe7, 0x45, 0x5a,
        ];

        let (ciphertext, tag) = aes128_gcm_encrypt(&key, &nonce, aad, plaintext);
        assert!(ciphertext.is_empty());
        assert_eq!(tag, expected_tag);

        // Verify decryption
        let result = aes128_gcm_decrypt(&key, &nonce, aad, &ciphertext, &tag);
        assert!(result.is_some());
        assert!(result.unwrap().is_empty());
    }

    /// NIST SP 800-38D, Test Case 2: AES-128-GCM with one block plaintext, empty AAD.
    #[test]
    fn test_aes128_gcm_test_case_2() {
        let key = [0u8; 16];
        let nonce = [0u8; 12];
        let aad: &[u8] = &[];
        let plaintext = [0u8; 16];

        let expected_ct: [u8; 16] = [
            0x03, 0x88, 0xda, 0xce, 0x60, 0xb6, 0xa3, 0x92,
            0xf3, 0x28, 0xc2, 0xb9, 0x71, 0xb2, 0xfe, 0x78,
        ];
        let expected_tag: [u8; 16] = [
            0xab, 0x6e, 0x47, 0xd4, 0x2c, 0xec, 0x13, 0xbd,
            0xf5, 0x3a, 0x67, 0xb2, 0x12, 0x57, 0xbd, 0xdf,
        ];

        let (ciphertext, tag) = aes128_gcm_encrypt(&key, &nonce, aad, &plaintext);
        assert_eq!(ciphertext.as_slice(), &expected_ct);
        assert_eq!(tag, expected_tag);

        // Verify decryption
        let result = aes128_gcm_decrypt(&key, &nonce, aad, &ciphertext, &tag);
        assert!(result.is_some());
        assert_eq!(result.unwrap().as_slice(), &plaintext);
    }

    /// Verify that decryption fails with a modified tag.
    #[test]
    fn test_aes128_gcm_bad_tag() {
        let key = [0u8; 16];
        let nonce = [0u8; 12];
        let aad: &[u8] = &[];
        let plaintext = [0u8; 16];

        let (ciphertext, mut tag) = aes128_gcm_encrypt(&key, &nonce, aad, &plaintext);

        // Flip one bit in the tag
        tag[0] ^= 0x01;

        let result = aes128_gcm_decrypt(&key, &nonce, aad, &ciphertext, &tag);
        assert!(result.is_none());
    }

    /// Verify that decryption fails with modified ciphertext.
    #[test]
    fn test_aes128_gcm_bad_ciphertext() {
        let key = [0u8; 16];
        let nonce = [0u8; 12];
        let aad: &[u8] = &[];
        let plaintext = [0u8; 16];

        let (mut ciphertext, tag) = aes128_gcm_encrypt(&key, &nonce, aad, &plaintext);

        // Flip one bit in the ciphertext
        ciphertext[0] ^= 0x01;

        let result = aes128_gcm_decrypt(&key, &nonce, aad, &ciphertext, &tag);
        assert!(result.is_none());
    }

    /// Test AES-256-GCM encrypt/decrypt round-trip.
    #[test]
    fn test_aes256_gcm_roundtrip() {
        let key: [u8; 32] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
        ];
        let nonce: [u8; 12] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b,
        ];
        let aad = b"additional data";
        let plaintext = b"Hello, AES-256-GCM!";

        let (ciphertext, tag) = aes256_gcm_encrypt(&key, &nonce, aad, plaintext);
        assert_eq!(ciphertext.len(), plaintext.len());

        let result = aes256_gcm_decrypt(&key, &nonce, aad, &ciphertext, &tag);
        assert!(result.is_some());
        assert_eq!(result.unwrap().as_slice(), plaintext);
    }

    /// Test AES-256-GCM with empty plaintext and empty AAD.
    #[test]
    fn test_aes256_gcm_empty() {
        let key = [0u8; 32];
        let nonce = [0u8; 12];
        let aad: &[u8] = &[];
        let plaintext: &[u8] = &[];

        let (ciphertext, tag) = aes256_gcm_encrypt(&key, &nonce, aad, plaintext);
        assert!(ciphertext.is_empty());

        let result = aes256_gcm_decrypt(&key, &nonce, aad, &ciphertext, &tag);
        assert!(result.is_some());
        assert!(result.unwrap().is_empty());
    }

    /// Test with AAD but no plaintext (authentication-only mode).
    #[test]
    fn test_aes128_gcm_aad_only() {
        let key = [0x42u8; 16];
        let nonce = [0x01u8; 12];
        let aad = b"Authenticate this data without encrypting anything";
        let plaintext: &[u8] = &[];

        let (ciphertext, tag) = aes128_gcm_encrypt(&key, &nonce, aad, plaintext);
        assert!(ciphertext.is_empty());

        // Decryption should succeed with correct tag
        let result = aes128_gcm_decrypt(&key, &nonce, aad, &ciphertext, &tag);
        assert!(result.is_some());

        // Decryption should fail with modified AAD
        let bad_aad = b"Modified AAD";
        let result = aes128_gcm_decrypt(&key, &nonce, bad_aad, &ciphertext, &tag);
        assert!(result.is_none());
    }
}
