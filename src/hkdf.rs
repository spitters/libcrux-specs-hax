//! Pure Rust HKDF-SHA256 specification (RFC 5869).
//!
//! HKDF (HMAC-based Key Derivation Function) has two phases:
//! - Extract: derives a pseudorandom key (PRK) from input keying material (IKM) and an
//!   optional salt using HMAC-SHA256.
//! - Expand: expands the PRK into output keying material (OKM) of desired length
//!   using HMAC-SHA256 with an info string.
//!
//! No external dependencies. Uses `crate::hmac::hmac_sha256` for the MAC.

use crate::hmac::hmac_sha256;

/// SHA-256 output length in bytes.
pub const HASH_LEN: usize = 32;

/// HKDF-Extract: PRK = HMAC-SHA256(salt, IKM).
///
/// If `salt` is empty, a string of `HASH_LEN` zeros is used as the salt
/// (per RFC 5869, Section 2.2).
pub fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> [u8; 32] {
    let default_salt = [0u8; HASH_LEN];
    let actual_salt = if salt.is_empty() {
        &default_salt[..]
    } else {
        salt
    };
    hmac_sha256(actual_salt, ikm)
}

/// HKDF-Expand: derive `length` bytes of output keying material from PRK and info.
///
/// T(0) = empty string
/// T(i) = HMAC-SHA256(PRK, T(i-1) || info || i)   for i = 1, 2, ...
/// OKM  = first `length` bytes of T(1) || T(2) || ...
///
/// Panics if `length` > 255 * HASH_LEN (per RFC 5869, Section 2.3).
pub fn hkdf_expand(prk: &[u8; 32], info: &[u8], length: usize) -> Vec<u8> {
    let n = (length + HASH_LEN - 1) / HASH_LEN;
    assert!(n <= 255, "HKDF-Expand: length too large (max 255 * 32 = 8160 bytes)");

    let mut okm = Vec::with_capacity(n * HASH_LEN);
    let mut t_prev: Vec<u8> = Vec::new(); // T(0) = empty

    for i in 1..=n {
        // Build HMAC input: T(i-1) || info || i
        let mut hmac_input = Vec::with_capacity(t_prev.len() + info.len() + 1);
        for j in 0..t_prev.len() {
            hmac_input.push(t_prev[j]);
        }
        for j in 0..info.len() {
            hmac_input.push(info[j]);
        }
        hmac_input.push(i as u8);

        let t_i = hmac_sha256(prk, &hmac_input);

        for j in 0..HASH_LEN {
            okm.push(t_i[j]);
        }

        t_prev = Vec::with_capacity(HASH_LEN);
        for j in 0..HASH_LEN {
            t_prev.push(t_i[j]);
        }
    }

    okm.truncate(length);
    okm
}

/// Full HKDF: extract then expand.
///
/// Equivalent to `hkdf_expand(&hkdf_extract(salt, ikm), info, length)`.
pub fn hkdf(salt: &[u8], ikm: &[u8], info: &[u8], length: usize) -> Vec<u8> {
    let prk = hkdf_extract(salt, ikm);
    hkdf_expand(&prk, info, length)
}

/// Fixed-length wrapper: HKDF-Extract with 32-byte salt and IKM.
pub fn hkdf_extract_32(salt: [u8; 32], ikm: [u8; 32]) -> [u8; 32] {
    hkdf_extract(&salt, &ikm)
}

/// Fixed-length wrapper: HKDF-Expand with 32-byte PRK and info, 32-byte output.
pub fn hkdf_expand_32(prk: [u8; 32], info: [u8; 32]) -> [u8; 32] {
    let out = hkdf_expand(&prk, &info, 32);
    let mut result = [0u8; 32];
    result.copy_from_slice(&out[..32]);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    /// RFC 5869 Test Case 1 (SHA-256):
    /// IKM  = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (22 bytes)
    /// salt = 0x000102030405060708090a0b0c (13 bytes)
    /// info = 0xf0f1f2f3f4f5f6f7f8f9 (10 bytes)
    /// L    = 42
    #[test]
    fn test_rfc5869_case1() {
        let ikm = [0x0bu8; 22];
        #[rustfmt::skip]
        let salt = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c,
        ];
        #[rustfmt::skip]
        let info = [
            0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7,
            0xf8, 0xf9,
        ];
        let length = 42;

        // Check PRK
        let prk = hkdf_extract(&salt, &ikm);
        #[rustfmt::skip]
        let expected_prk: [u8; 32] = [
            0x07, 0x77, 0x09, 0x36, 0x2c, 0x2e, 0x32, 0xdf,
            0x0d, 0xdc, 0x3f, 0x0d, 0xc4, 0x7b, 0xba, 0x63,
            0x90, 0xb6, 0xc7, 0x3b, 0xb5, 0x0f, 0x9c, 0x31,
            0x22, 0xec, 0x84, 0x4a, 0xd7, 0xc2, 0xb3, 0xe5,
        ];
        assert_eq!(prk, expected_prk);

        // Check OKM
        let okm = hkdf_expand(&prk, &info, length);
        #[rustfmt::skip]
        let expected_okm: [u8; 42] = [
            0x3c, 0xb2, 0x5f, 0x25, 0xfa, 0xac, 0xd5, 0x7a,
            0x90, 0x43, 0x4f, 0x64, 0xd0, 0x36, 0x2f, 0x2a,
            0x2d, 0x2d, 0x0a, 0x90, 0xcf, 0x1a, 0x5a, 0x4c,
            0x5d, 0xb0, 0x2d, 0x56, 0xec, 0xc4, 0xc5, 0xbf,
            0x34, 0x00, 0x72, 0x08, 0xd5, 0xb8, 0x87, 0x18,
            0x58, 0x65,
        ];
        assert_eq!(okm, expected_okm);
    }

    /// RFC 5869 Test Case 2 (SHA-256):
    /// Longer inputs for all fields.
    /// IKM  = 0x000102...4f (80 bytes)
    /// salt = 0x606162...af (80 bytes)
    /// info = 0xb0b1b2...ff (80 bytes)
    /// L    = 82
    #[test]
    fn test_rfc5869_case2() {
        let mut ikm = [0u8; 80];
        for i in 0..80 {
            ikm[i] = i as u8;
        }
        let mut salt = [0u8; 80];
        for i in 0..80 {
            salt[i] = (0x60 + i) as u8;
        }
        let mut info = [0u8; 80];
        for i in 0..80 {
            info[i] = (0xb0 + i) as u8;
        }
        let length = 82;

        let prk = hkdf_extract(&salt, &ikm);
        #[rustfmt::skip]
        let expected_prk: [u8; 32] = [
            0x06, 0xa6, 0xb8, 0x8c, 0x58, 0x53, 0x36, 0x1a,
            0x06, 0x10, 0x4c, 0x9c, 0xeb, 0x35, 0xb4, 0x5c,
            0xef, 0x76, 0x00, 0x14, 0x90, 0x46, 0x71, 0x01,
            0x4a, 0x19, 0x3f, 0x40, 0xc1, 0x5f, 0xc2, 0x44,
        ];
        assert_eq!(prk, expected_prk);

        let okm = hkdf_expand(&prk, &info, length);
        #[rustfmt::skip]
        let expected_okm: [u8; 82] = [
            0xb1, 0x1e, 0x39, 0x8d, 0xc8, 0x03, 0x27, 0xa1,
            0xc8, 0xe7, 0xf7, 0x8c, 0x59, 0x6a, 0x49, 0x34,
            0x4f, 0x01, 0x2e, 0xda, 0x2d, 0x4e, 0xfa, 0xd8,
            0xa0, 0x50, 0xcc, 0x4c, 0x19, 0xaf, 0xa9, 0x7c,
            0x59, 0x04, 0x5a, 0x99, 0xca, 0xc7, 0x82, 0x72,
            0x71, 0xcb, 0x41, 0xc6, 0x5e, 0x59, 0x0e, 0x09,
            0xda, 0x32, 0x75, 0x60, 0x0c, 0x2f, 0x09, 0xb8,
            0x36, 0x77, 0x93, 0xa9, 0xac, 0xa3, 0xdb, 0x71,
            0xcc, 0x30, 0xc5, 0x81, 0x79, 0xec, 0x3e, 0x87,
            0xc1, 0x4c, 0x01, 0xd5, 0xc1, 0xf3, 0x43, 0x4f,
            0x1d, 0x87,
        ];
        assert_eq!(okm, expected_okm);
    }

    /// RFC 5869 Test Case 3 (SHA-256):
    /// IKM  = 0x0b repeated 22 times
    /// salt = empty
    /// info = empty
    /// L    = 42
    #[test]
    fn test_rfc5869_case3_empty_salt_info() {
        let ikm = [0x0bu8; 22];
        let salt: &[u8] = &[];
        let info: &[u8] = &[];
        let length = 42;

        let prk = hkdf_extract(salt, &ikm);
        #[rustfmt::skip]
        let expected_prk: [u8; 32] = [
            0x19, 0xef, 0x24, 0xa3, 0x2c, 0x71, 0x7b, 0x16,
            0x7f, 0x33, 0xa9, 0x1d, 0x6f, 0x64, 0x8b, 0xdf,
            0x96, 0x59, 0x67, 0x76, 0xaf, 0xdb, 0x63, 0x77,
            0xac, 0x43, 0x4c, 0x1c, 0x29, 0x3c, 0xcb, 0x04,
        ];
        assert_eq!(prk, expected_prk);

        let okm = hkdf_expand(&prk, info, length);
        #[rustfmt::skip]
        let expected_okm: [u8; 42] = [
            0x8d, 0xa4, 0xe7, 0x75, 0xa5, 0x63, 0xc1, 0x8f,
            0x71, 0x5f, 0x80, 0x2a, 0x06, 0x3c, 0x5a, 0x31,
            0xb8, 0xa1, 0x1f, 0x5c, 0x5e, 0xe1, 0x87, 0x9e,
            0xc3, 0x45, 0x4e, 0x5f, 0x3c, 0x73, 0x8d, 0x2d,
            0x9d, 0x20, 0x13, 0x95, 0xfa, 0xa4, 0xb6, 0x1a,
            0x96, 0xc8,
        ];
        assert_eq!(okm, expected_okm);
    }
}
