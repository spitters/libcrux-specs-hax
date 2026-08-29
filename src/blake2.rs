//! Pure Rust specification of BLAKE2b and BLAKE2s (RFC 7693).
//!
//! No external dependencies. Plain integer types, fixed-size arrays, value-passing.

// ---------------------------------------------------------------------------
// Shared constants
// ---------------------------------------------------------------------------

/// Message schedule permutation table (10 standard permutations from RFC 7693).
pub const SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

// ===========================================================================
// BLAKE2b
// ===========================================================================

/// BLAKE2b initialization vector: fractional parts of sqrt(2..19) truncated to 64 bits.
pub const IV_B: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

/// BLAKE2b block size in bytes.
pub const BLOCK_B: usize = 128;

/// BLAKE2b mixing function G.
///
/// Operates on the 4x4 working state `v`, mixing in message words `x` and `y`
/// at positions `a`, `b`, `c`, `d`. Rotation amounts: 32, 24, 16, 63.
pub fn g_b(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize, x: u64, y: u64) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

/// BLAKE2b compression function.
///
/// Compresses one 128-byte block of message words `m` into the chaining value `h`.
/// `t` is the byte offset counter (up to 2^128), `last` signals the final block.
pub fn compress_b(h: [u64; 8], m: [u64; 16], t: u128, last: bool) -> [u64; 8] {
    let mut v = [0u64; 16];

    // Initialize working vector: first half from chaining value, second half from IV.
    for i in 0..8 {
        v[i] = h[i];
        v[i + 8] = IV_B[i];
    }

    // XOR counter into v[12..13].
    v[12] ^= t as u64;
    v[13] ^= (t >> 64) as u64;

    // If this is the last block, invert all bits of v[14].
    if last {
        v[14] = !v[14];
    }

    // 12 rounds of mixing. BLAKE2b uses SIGMA[i % 10].
    for i in 0..12 {
        let s = &SIGMA[i % 10];

        // Column step
        g_b(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        g_b(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        g_b(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        g_b(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);

        // Diagonal step
        g_b(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        g_b(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        g_b(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        g_b(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }

    // Finalize: XOR the two halves of v back into the chaining value.
    let mut result = [0u64; 8];
    for i in 0..8 {
        result[i] = h[i] ^ v[i] ^ v[i + 8];
    }
    result
}

/// Decode a slice of bytes into an array of `u64` words (little-endian).
pub fn bytes_to_words_b(block: &[u8]) -> [u64; 16] {
    let mut m = [0u64; 16];
    for i in 0..16 {
        let base = i * 8;
        if base + 8 <= block.len() {
            m[i] = u64::from_le_bytes([
                block[base],
                block[base + 1],
                block[base + 2],
                block[base + 3],
                block[base + 4],
                block[base + 5],
                block[base + 6],
                block[base + 7],
            ]);
        } else {
            // Partial word: pad with zeros.
            let mut buf = [0u8; 8];
            for j in 0..8 {
                if base + j < block.len() {
                    buf[j] = block[base + j];
                }
            }
            m[i] = u64::from_le_bytes(buf);
        }
    }
    m
}

/// BLAKE2b hash function (RFC 7693).
///
/// - `msg`: input message (arbitrary length).
/// - `key`: optional key (0 to 64 bytes). Pass `&[]` for unkeyed hashing.
/// - `out_len`: desired output length in bytes (1 to 64).
///
/// Returns the hash as a `Vec<u8>` of length `out_len`.
///
/// # Panics
///
/// Panics if `out_len` is not in 1..=64 or `key.len()` exceeds 64.
pub fn blake2b(msg: &[u8], key: &[u8], out_len: usize) -> Vec<u8> {
    assert!(out_len >= 1 && out_len <= 64, "blake2b: out_len must be 1..64");
    assert!(key.len() <= 64, "blake2b: key length must be 0..64");

    let key_len = key.len();

    // Initialize chaining value with parameter block.
    // Parameter block (word 0): fanout=1, depth=1, key_len, out_len.
    let mut h = IV_B;
    h[0] ^= 0x01010000 ^ ((key_len as u64) << 8) ^ (out_len as u64);

    // If keyed, the first block is the key padded to BLOCK_B bytes.
    let mut data: Vec<u8> = if key_len > 0 {
        let mut d = Vec::with_capacity(BLOCK_B + msg.len());
        d.extend_from_slice(key);
        d.resize(BLOCK_B, 0);
        d.extend_from_slice(msg);
        d
    } else {
        msg.to_vec()
    };

    // If the data is empty (unkeyed, empty message), we still compress one block of zeros.
    if data.is_empty() {
        let block = [0u8; BLOCK_B];
        let m = bytes_to_words_b(&block);
        h = compress_b(h, m, 0, true);
    } else {
        let total = data.len();
        let mut offset = 0;

        while offset < total {
            let remaining = total - offset;
            let take = if remaining > BLOCK_B { BLOCK_B } else { remaining };
            let last = remaining <= BLOCK_B;

            // Pad the last block with zeros if shorter than BLOCK_B.
            let mut block = [0u8; BLOCK_B];
            for i in 0..take {
                block[i] = data[offset + i];
            }

            let bytes_compressed = offset + take;
            let t = bytes_compressed as u128;

            let m = bytes_to_words_b(&block);
            h = compress_b(h, m, t, last);

            offset += take;
        }
    }

    // Produce output: first out_len bytes of h (little-endian).
    let mut out = Vec::with_capacity(out_len);
    for i in 0..8 {
        let word_bytes = h[i].to_le_bytes();
        for &b in &word_bytes {
            if out.len() < out_len {
                out.push(b);
            }
        }
    }
    out
}

// ===========================================================================
// BLAKE2s
// ===========================================================================

/// BLAKE2s initialization vector: fractional parts of sqrt(2..19) truncated to 32 bits.
pub const IV_S: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

/// BLAKE2s block size in bytes.
pub const BLOCK_S: usize = 64;

/// BLAKE2s mixing function G.
///
/// Operates on the 4x4 working state `v`, mixing in message words `x` and `y`
/// at positions `a`, `b`, `c`, `d`. Rotation amounts: 16, 12, 8, 7.
pub fn g_s(v: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, x: u32, y: u32) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(12);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(8);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(7);
}

/// BLAKE2s compression function.
///
/// Compresses one 64-byte block of message words `m` into the chaining value `h`.
/// `t` is the byte offset counter (up to 2^64), `last` signals the final block.
pub fn compress_s(h: [u32; 8], m: [u32; 16], t: u64, last: bool) -> [u32; 8] {
    let mut v = [0u32; 16];

    // Initialize working vector: first half from chaining value, second half from IV.
    for i in 0..8 {
        v[i] = h[i];
        v[i + 8] = IV_S[i];
    }

    // XOR counter into v[12..13].
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;

    // If this is the last block, invert all bits of v[14].
    if last {
        v[14] = !v[14];
    }

    // 10 rounds of mixing. BLAKE2s uses SIGMA[i] directly.
    for i in 0..10 {
        let s = &SIGMA[i];

        // Column step
        g_s(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        g_s(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        g_s(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        g_s(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);

        // Diagonal step
        g_s(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        g_s(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        g_s(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        g_s(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }

    // Finalize: XOR the two halves of v back into the chaining value.
    let mut result = [0u32; 8];
    for i in 0..8 {
        result[i] = h[i] ^ v[i] ^ v[i + 8];
    }
    result
}

/// Decode a slice of bytes into an array of `u32` words (little-endian).
pub fn bytes_to_words_s(block: &[u8]) -> [u32; 16] {
    let mut m = [0u32; 16];
    for i in 0..16 {
        let base = i * 4;
        if base + 4 <= block.len() {
            m[i] = u32::from_le_bytes([
                block[base],
                block[base + 1],
                block[base + 2],
                block[base + 3],
            ]);
        } else {
            let mut buf = [0u8; 4];
            for j in 0..4 {
                if base + j < block.len() {
                    buf[j] = block[base + j];
                }
            }
            m[i] = u32::from_le_bytes(buf);
        }
    }
    m
}

/// BLAKE2s hash function (RFC 7693).
///
/// - `msg`: input message (arbitrary length).
/// - `key`: optional key (0 to 32 bytes). Pass `&[]` for unkeyed hashing.
/// - `out_len`: desired output length in bytes (1 to 32).
///
/// Returns the hash as a `Vec<u8>` of length `out_len`.
///
/// # Panics
///
/// Panics if `out_len` is not in 1..=32 or `key.len()` exceeds 32.
pub fn blake2s(msg: &[u8], key: &[u8], out_len: usize) -> Vec<u8> {
    assert!(out_len >= 1 && out_len <= 32, "blake2s: out_len must be 1..32");
    assert!(key.len() <= 32, "blake2s: key length must be 0..32");

    let key_len = key.len();

    // Initialize chaining value with parameter block.
    let mut h = IV_S;
    h[0] ^= 0x01010000 ^ ((key_len as u32) << 8) ^ (out_len as u32);

    // If keyed, the first block is the key padded to BLOCK_S bytes.
    let mut data: Vec<u8> = if key_len > 0 {
        let mut d = Vec::with_capacity(BLOCK_S + msg.len());
        d.extend_from_slice(key);
        d.resize(BLOCK_S, 0);
        d.extend_from_slice(msg);
        d
    } else {
        msg.to_vec()
    };

    // If the data is empty (unkeyed, empty message), we still compress one block of zeros.
    if data.is_empty() {
        let block = [0u8; BLOCK_S];
        let m = bytes_to_words_s(&block);
        h = compress_s(h, m, 0, true);
    } else {
        let total = data.len();
        let mut offset = 0;

        while offset < total {
            let remaining = total - offset;
            let take = if remaining > BLOCK_S { BLOCK_S } else { remaining };
            let last = remaining <= BLOCK_S;

            let mut block = [0u8; BLOCK_S];
            for i in 0..take {
                block[i] = data[offset + i];
            }

            let bytes_compressed = offset + take;
            let t = bytes_compressed as u64;

            let m = bytes_to_words_s(&block);
            h = compress_s(h, m, t, last);

            offset += take;
        }
    }

    // Produce output: first out_len bytes of h (little-endian).
    let mut out = Vec::with_capacity(out_len);
    for i in 0..8 {
        let word_bytes = h[i].to_le_bytes();
        for &b in &word_bytes {
            if out.len() < out_len {
                out.push(b);
            }
        }
    }
    out
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // RFC 7693 Appendix A: BLAKE2b test vector
    // Input: "abc" (3 bytes), no key, 64-byte output
    #[test]
    fn test_blake2b_abc() {
        let expected: [u8; 64] = [
            0xBA, 0x80, 0xA5, 0x3F, 0x98, 0x1C, 0x4D, 0x0D,
            0x6A, 0x27, 0x97, 0xB6, 0x9F, 0x12, 0xF6, 0xE9,
            0x4C, 0x21, 0x2F, 0x14, 0x68, 0x5A, 0xC4, 0xB7,
            0x4B, 0x12, 0xBB, 0x6F, 0xDB, 0xFF, 0xA2, 0xD1,
            0x7D, 0x87, 0xC5, 0x39, 0x2A, 0xAB, 0x79, 0x2D,
            0xC2, 0x52, 0xD5, 0xDE, 0x45, 0x33, 0xCC, 0x95,
            0x18, 0xD3, 0x8A, 0xA8, 0xDB, 0xF1, 0x92, 0x5A,
            0xB9, 0x23, 0x86, 0xED, 0xD4, 0x00, 0x99, 0x23,
        ];
        let result = blake2b(b"abc", &[], 64);
        assert_eq!(result, expected.to_vec());
    }

    // RFC 7693 Appendix A: BLAKE2s test vector
    // Input: "abc" (3 bytes), no key, 32-byte output
    #[test]
    fn test_blake2s_abc() {
        let expected: [u8; 32] = [
            0x50, 0x8C, 0x5E, 0x8C, 0x32, 0x7C, 0x14, 0xE2,
            0xE1, 0xA7, 0x2B, 0xA3, 0x4E, 0xEB, 0x45, 0x2F,
            0x37, 0x45, 0x8B, 0x20, 0x9E, 0xD6, 0x3A, 0x29,
            0x4D, 0x99, 0x9B, 0x4C, 0x86, 0x67, 0x59, 0x82,
        ];
        let result = blake2s(b"abc", &[], 32);
        assert_eq!(result, expected.to_vec());
    }

    // Empty message, no key, full output
    #[test]
    fn test_blake2b_empty() {
        // Known BLAKE2b("", 64) hash
        let expected: [u8; 64] = [
            0x78, 0x6A, 0x02, 0xF7, 0x42, 0x01, 0x59, 0x03,
            0xC6, 0xC6, 0xFD, 0x85, 0x25, 0x52, 0xD2, 0x72,
            0x91, 0x2F, 0x47, 0x40, 0xE1, 0x58, 0x47, 0x61,
            0x8A, 0x86, 0xE2, 0x17, 0xF7, 0x1F, 0x54, 0x19,
            0xD2, 0x5E, 0x10, 0x31, 0xAF, 0xEE, 0x58, 0x53,
            0x13, 0x89, 0x64, 0x44, 0x93, 0x4E, 0xB0, 0x4B,
            0x90, 0x3A, 0x68, 0x5B, 0x14, 0x48, 0xB7, 0x55,
            0xD5, 0x6F, 0x70, 0x1A, 0xFE, 0x9B, 0xE2, 0xCE,
        ];
        let result = blake2b(b"", &[], 64);
        assert_eq!(result, expected.to_vec());
    }

    #[test]
    fn test_blake2s_empty() {
        // Known BLAKE2s("", 32) hash
        let expected: [u8; 32] = [
            0x69, 0x21, 0x7A, 0x30, 0x79, 0x90, 0x80, 0x94,
            0xE1, 0x11, 0x21, 0xD0, 0x42, 0x35, 0x4A, 0x7C,
            0x1F, 0x55, 0xB6, 0x48, 0x2C, 0xA1, 0xA5, 0x1E,
            0x1B, 0x25, 0x0D, 0xFD, 0x1E, 0xD0, 0xEE, 0xF9,
        ];
        let result = blake2s(b"", &[], 32);
        assert_eq!(result, expected.to_vec());
    }

    // Test shorter output length
    #[test]
    fn test_blake2b_short_output() {
        let full = blake2b(b"test", &[], 64);
        let short = blake2b(b"test", &[], 32);
        // Short output should NOT be a prefix of full output (different parameter block).
        // Just verify length.
        assert_eq!(short.len(), 32);
        assert_eq!(full.len(), 64);
    }

    #[test]
    fn test_blake2s_short_output() {
        let full = blake2s(b"test", &[], 32);
        let short = blake2s(b"test", &[], 16);
        assert_eq!(short.len(), 16);
        assert_eq!(full.len(), 32);
    }

    // Test keyed hashing
    #[test]
    fn test_blake2b_keyed() {
        let key = b"secret key";
        let result = blake2b(b"message", key, 64);
        let result2 = blake2b(b"message", key, 64);
        let unkeyed = blake2b(b"message", &[], 64);
        // Keyed hash should be deterministic.
        assert_eq!(result, result2);
        // Keyed hash should differ from unkeyed.
        assert_ne!(result, unkeyed);
    }

    #[test]
    fn test_blake2s_keyed() {
        let key = b"secret key";
        let result = blake2s(b"message", key, 32);
        let result2 = blake2s(b"message", key, 32);
        let unkeyed = blake2s(b"message", &[], 32);
        assert_eq!(result, result2);
        assert_ne!(result, unkeyed);
    }

    // Test multi-block message (longer than one block)
    #[test]
    fn test_blake2b_multiblock() {
        let msg = vec![0x61u8; 256]; // 256 bytes of 'a', spans multiple 128-byte blocks
        let result = blake2b(&msg, &[], 64);
        assert_eq!(result.len(), 64);
    }

    #[test]
    fn test_blake2s_multiblock() {
        let msg = vec![0x61u8; 256]; // 256 bytes of 'a', spans multiple 64-byte blocks
        let result = blake2s(&msg, &[], 32);
        assert_eq!(result.len(), 32);
    }
}
