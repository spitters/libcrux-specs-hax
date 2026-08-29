//! Pure Rust HMAC-SHA256 specification (RFC 2104).
//!
//! HMAC(K, text) = H((K' XOR opad) || H((K' XOR ipad) || text))
//! where K' is the key padded or hashed to the block size (64 bytes for SHA-256).
//!
//! No external dependencies. Uses `crate::sha256::sha256` for the hash function.

use crate::sha256::sha256;

/// HMAC block size for SHA-256 (512 bits = 64 bytes).
pub const BLOCK_SIZE: usize = 64;

/// Inner padding byte (RFC 2104, Section 2).
pub const IPAD: u8 = 0x36;

/// Outer padding byte (RFC 2104, Section 2).
pub const OPAD: u8 = 0x5c;

/// Compute HMAC-SHA256 of `msg` under `key`.
///
/// 1. If `key` is longer than 64 bytes, replace it with SHA-256(key).
/// 2. Pad the (possibly hashed) key to 64 bytes with zeros.
/// 3. inner = SHA-256((key_padded XOR ipad) || msg)
/// 4. result = SHA-256((key_padded XOR opad) || inner)
pub fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    // Step 1: If key > block size, hash it
    let key_hash: [u8; 32] = if key.len() > BLOCK_SIZE {
        sha256(key)
    } else {
        [0u8; 32]
    };
    let key_bytes: &[u8] = if key.len() > BLOCK_SIZE {
        &key_hash
    } else {
        key
    };

    // Step 2: Pad key to BLOCK_SIZE with zeros
    let mut key_padded = [0u8; BLOCK_SIZE];
    for i in 0..key_bytes.len() {
        key_padded[i] = key_bytes[i];
    }

    // Step 3: Compute inner hash = SHA-256((key_padded XOR ipad) || msg)
    let mut inner_key = [0u8; BLOCK_SIZE];
    for i in 0..BLOCK_SIZE {
        inner_key[i] = key_padded[i] ^ IPAD;
    }

    // Build inner_data = inner_key || msg
    let mut inner_data = Vec::with_capacity(BLOCK_SIZE + msg.len());
    for i in 0..BLOCK_SIZE {
        inner_data.push(inner_key[i]);
    }
    for i in 0..msg.len() {
        inner_data.push(msg[i]);
    }

    let inner_hash = sha256(&inner_data);

    // Step 4: Compute outer hash = SHA-256((key_padded XOR opad) || inner_hash)
    let mut outer_key = [0u8; BLOCK_SIZE];
    for i in 0..BLOCK_SIZE {
        outer_key[i] = key_padded[i] ^ OPAD;
    }

    let mut outer_data = [0u8; BLOCK_SIZE + 32];
    for i in 0..BLOCK_SIZE {
        outer_data[i] = outer_key[i];
    }
    for i in 0..32 {
        outer_data[BLOCK_SIZE + i] = inner_hash[i];
    }

    sha256(&outer_data)
}

/// Fixed-length wrapper: HMAC-SHA256 on 32-byte key and message.
pub fn hmac_sha256_32(key: [u8; 32], msg: [u8; 32]) -> [u8; 32] {
    hmac_sha256(&key, &msg)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// RFC 4231 Test Case 1:
    /// Key  = 0x0b repeated 20 times
    /// Data = "Hi There"
    #[test]
    fn test_rfc4231_case1() {
        let key = [0x0bu8; 20];
        let data = b"Hi There";
        let tag = hmac_sha256(&key, data);
        #[rustfmt::skip]
        let expected: [u8; 32] = [
            0xb0, 0x34, 0x4c, 0x61, 0xd8, 0xdb, 0x38, 0x53,
            0x5c, 0xa8, 0xaf, 0xce, 0xaf, 0x0b, 0xf1, 0x2b,
            0x88, 0x1d, 0xc2, 0x00, 0xc9, 0x83, 0x3d, 0xa7,
            0x26, 0xe9, 0x37, 0x6c, 0x2e, 0x32, 0xcf, 0xf7,
        ];
        assert_eq!(tag, expected);
    }

    /// RFC 4231 Test Case 2:
    /// Key  = "Jefe"
    /// Data = "what do ya want for nothing?"
    #[test]
    fn test_rfc4231_case2() {
        let key = b"Jefe";
        let data = b"what do ya want for nothing?";
        let tag = hmac_sha256(key, data);
        #[rustfmt::skip]
        let expected: [u8; 32] = [
            0x5b, 0xdc, 0xc1, 0x46, 0xbf, 0x60, 0x75, 0x4e,
            0x6a, 0x04, 0x24, 0x26, 0x08, 0x95, 0x75, 0xc7,
            0x5a, 0x00, 0x3f, 0x08, 0x9d, 0x27, 0x39, 0x83,
            0x9d, 0xec, 0x58, 0xb9, 0x64, 0xec, 0x38, 0x43,
        ];
        assert_eq!(tag, expected);
    }

    /// RFC 4231 Test Case 3:
    /// Key  = 0xaa repeated 20 times
    /// Data = 0xdd repeated 50 times
    #[test]
    fn test_rfc4231_case3() {
        let key = [0xaau8; 20];
        let data = [0xddu8; 50];
        let tag = hmac_sha256(&key, &data);
        #[rustfmt::skip]
        let expected: [u8; 32] = [
            0x77, 0x3e, 0xa9, 0x1e, 0x36, 0x80, 0x0e, 0x46,
            0x85, 0x4d, 0xb8, 0xeb, 0xd0, 0x91, 0x81, 0xa7,
            0x29, 0x59, 0x09, 0x8b, 0x3e, 0xf8, 0xc1, 0x22,
            0xd9, 0x63, 0x55, 0x14, 0xce, 0xd5, 0x65, 0xfe,
        ];
        assert_eq!(tag, expected);
    }

    /// RFC 4231 Test Case 6:
    /// Key  = 0xaa repeated 131 times (longer than block size, triggers hashing)
    /// Data = "Test Using Larger Than Block-Size Key - Hash Key First"
    #[test]
    fn test_rfc4231_case6_long_key() {
        let key = [0xaau8; 131];
        let data = b"Test Using Larger Than Block-Size Key - Hash Key First";
        let tag = hmac_sha256(&key, data);
        #[rustfmt::skip]
        let expected: [u8; 32] = [
            0x60, 0xe4, 0x31, 0x59, 0x1e, 0xe0, 0xb6, 0x7f,
            0x0d, 0x8a, 0x26, 0xaa, 0xcb, 0xf5, 0xb7, 0x7f,
            0x8e, 0x0b, 0xc6, 0x21, 0x37, 0x28, 0xc5, 0x14,
            0x05, 0x46, 0x04, 0x0f, 0x0e, 0xe3, 0x7f, 0x54,
        ];
        assert_eq!(tag, expected);
    }
}

