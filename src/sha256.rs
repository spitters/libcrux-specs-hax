//! Pure Rust SHA-256 specification (FIPS 180-4).
//!
//! No external dependencies. All functions are pure and value-passing.

/// SHA-256 round constants (first 32 bits of the fractional parts of the
/// cube roots of the first 64 primes).
#[rustfmt::skip]
pub const K_TABLE: [u32; 64] = [
    0x428a_2f98, 0x7137_4491, 0xb5c0_fbcf, 0xe9b5_dba5,
    0x3956_c25b, 0x59f1_11f1, 0x923f_82a4, 0xab1c_5ed5,
    0xd807_aa98, 0x1283_5b01, 0x2431_85be, 0x550c_7dc3,
    0x72be_5d74, 0x80de_b1fe, 0x9bdc_06a7, 0xc19b_f174,
    0xe49b_69c1, 0xefbe_4786, 0x0fc1_9dc6, 0x240c_a1cc,
    0x2de9_2c6f, 0x4a74_84aa, 0x5cb0_a9dc, 0x76f9_88da,
    0x983e_5152, 0xa831_c66d, 0xb003_27c8, 0xbf59_7fc7,
    0xc6e0_0bf3, 0xd5a7_9147, 0x06ca_6351, 0x1429_2967,
    0x27b7_0a85, 0x2e1b_2138, 0x4d2c_6dfc, 0x5338_0d13,
    0x650a_7354, 0x766a_0abb, 0x81c2_c92e, 0x9272_2c85,
    0xa2bf_e8a1, 0xa81a_664b, 0xc24b_8b70, 0xc76c_51a3,
    0xd192_e819, 0xd699_0624, 0xf40e_3585, 0x106a_a070,
    0x19a4_c116, 0x1e37_6c08, 0x2748_774c, 0x34b0_bcb5,
    0x391c_0cb3, 0x4ed8_aa4a, 0x5b9c_ca4f, 0x682e_6ff3,
    0x748f_82ee, 0x78a5_636f, 0x84c8_7814, 0x8cc7_0208,
    0x90be_fffa, 0xa450_6ceb, 0xbef9_a3f7, 0xc671_78f2,
];

/// Initial hash values (first 32 bits of the fractional parts of the
/// square roots of the first 8 primes).
pub const HASH_INIT: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

// --- Helper functions (FIPS 180-4, Section 4.1.2) ---

/// Ch(x, y, z) = (x AND y) XOR (NOT x AND z)
pub fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ ((!x) & z)
}

/// Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z)
pub fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

/// lowercase sigma_0(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x)
pub fn sigma0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}

/// lowercase sigma_1(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x)
pub fn sigma1(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}

/// uppercase Sigma_0(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x)
pub fn big_sigma0(x: u32) -> u32 {
    x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
}

/// uppercase Sigma_1(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x)
pub fn big_sigma1(x: u32) -> u32 {
    x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
}

// --- Message schedule (FIPS 180-4, Section 6.2.2, step 1) ---

/// Expand a 64-byte block into a 64-word message schedule.
pub fn schedule(block: &[u8; 64]) -> [u32; 64] {
    let mut w = [0u32; 64];

    // W_0..W_15: parse block as 16 big-endian 32-bit words
    for i in 0..16 {
        w[i] = u32::from_be_bytes([
            block[4 * i],
            block[4 * i + 1],
            block[4 * i + 2],
            block[4 * i + 3],
        ]);
    }

    // W_16..W_63: sigma1(W_{t-2}) + W_{t-7} + sigma0(W_{t-15}) + W_{t-16}
    for i in 16..64 {
        w[i] = sigma1(w[i - 2])
            .wrapping_add(w[i - 7])
            .wrapping_add(sigma0(w[i - 15]))
            .wrapping_add(w[i - 16]);
    }

    w
}

// --- Compression function (FIPS 180-4, Section 6.2.2, steps 2-4) ---

/// Compress one 64-byte block into the running hash state.
pub fn compress(block: &[u8; 64], h_in: [u32; 8]) -> [u32; 8] {
    let w = schedule(block);

    // Working variables
    let mut a = h_in[0];
    let mut b = h_in[1];
    let mut c = h_in[2];
    let mut d = h_in[3];
    let mut e = h_in[4];
    let mut f = h_in[5];
    let mut g = h_in[6];
    let mut h = h_in[7];

    // 64 rounds
    for i in 0..64 {
        let t1 = h
            .wrapping_add(big_sigma1(e))
            .wrapping_add(ch(e, f, g))
            .wrapping_add(K_TABLE[i])
            .wrapping_add(w[i]);
        let t2 = big_sigma0(a).wrapping_add(maj(a, b, c));

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }

    // Add the compressed chunk to the current hash value
    [
        h_in[0].wrapping_add(a),
        h_in[1].wrapping_add(b),
        h_in[2].wrapping_add(c),
        h_in[3].wrapping_add(d),
        h_in[4].wrapping_add(e),
        h_in[5].wrapping_add(f),
        h_in[6].wrapping_add(g),
        h_in[7].wrapping_add(h),
    ]
}

// --- Full SHA-256 with padding (FIPS 180-4, Section 5.1.1) ---

/// Compute SHA-256 of an arbitrary-length message.
///
/// Handles Merkle-Damgard padding: append bit `1`, then zeros, then the
/// 64-bit big-endian bit length, so that the padded message length is a
/// multiple of 512 bits (64 bytes).
pub fn sha256(msg: &[u8]) -> [u8; 32] {
    let mut h = HASH_INIT;
    let msg_len = msg.len();
    // Compute in u128 then truncate to u64 to avoid a debug-mode panic on
    // multiplication overflow when msg_len >= 2^61. The truncation matches
    // what u64.to_be_bytes() would have produced under saturating semantics,
    // so the wire format is unchanged for all msg_len < 2^61 (every
    // practical input). For larger inputs the spec defines NIST behaviour
    // as `bit_len mod 2^64` anyway.
    let bit_len = ((msg_len as u128) * 8) as u64;

    // Process complete 64-byte blocks
    let num_full_blocks = msg_len / 64;
    for i in 0..num_full_blocks {
        let mut block = [0u8; 64];
        for j in 0..64 {
            block[j] = msg[i * 64 + j];
        }
        h = compress(&block, h);
    }

    // Handle the final partial block + padding
    let remaining = msg_len % 64;

    // Build the last block: copy remaining bytes, append 0x80
    let mut last_block = [0u8; 64];
    for j in 0..remaining {
        last_block[j] = msg[num_full_blocks * 64 + j];
    }
    last_block[remaining] = 0x80;

    if remaining < 56 {
        // Length fits in this block (bytes 56..63)
        let len_bytes = bit_len.to_be_bytes();
        for j in 0..8 {
            last_block[56 + j] = len_bytes[j];
        }
        h = compress(&last_block, h);
    } else {
        // Need a second padding block for the length
        h = compress(&last_block, h);

        let mut pad_block = [0u8; 64];
        let len_bytes = bit_len.to_be_bytes();
        for j in 0..8 {
            pad_block[56 + j] = len_bytes[j];
        }
        h = compress(&pad_block, h);
    }

    // Produce the 32-byte digest (big-endian serialization of h[0..8])
    let mut digest = [0u8; 32];
    for i in 0..8 {
        let bytes = h[i].to_be_bytes();
        digest[4 * i] = bytes[0];
        digest[4 * i + 1] = bytes[1];
        digest[4 * i + 2] = bytes[2];
        digest[4 * i + 3] = bytes[3];
    }
    digest
}

/// Fixed-length wrapper: SHA-256 on a 32-byte input.
pub fn sha256_32(msg: [u8; 32]) -> [u8; 32] {
    sha256(&msg)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// NIST FIPS 180-4 example: SHA-256("abc")
    #[test]
    fn test_abc() {
        let digest = sha256(b"abc");
        let expected: [u8; 32] = [
            0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
            0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
            0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
            0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
        ];
        assert_eq!(digest, expected);
    }

    /// NIST FIPS 180-4 example: SHA-256("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
    /// This is a two-block message (448 bits of data triggers double-block padding).
    #[test]
    fn test_two_block() {
        let msg = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        let digest = sha256(msg);
        let expected: [u8; 32] = [
            0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8,
            0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39,
            0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff, 0x21, 0x67,
            0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1,
        ];
        assert_eq!(digest, expected);
    }

    /// SHA-256 of the empty string.
    #[test]
    fn test_empty() {
        let digest = sha256(b"");
        let expected: [u8; 32] = [
            0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
            0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
            0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
            0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55,
        ];
        assert_eq!(digest, expected);
    }

    /// Exactly 55 bytes: last block has room for padding + length in one block.
    #[test]
    fn test_55_bytes() {
        let msg = [0x61u8; 55]; // 55 'a's
        let digest = sha256(&msg);
        let expected: [u8; 32] = [
            0x9f, 0x43, 0x90, 0xf8, 0xd3, 0x0c, 0x2d, 0xd9,
            0x2e, 0xc9, 0xf0, 0x95, 0xb6, 0x5e, 0x2b, 0x9a,
            0xe9, 0xb0, 0xa9, 0x25, 0xa5, 0x25, 0x8e, 0x24,
            0x1c, 0x9f, 0x1e, 0x91, 0x0f, 0x73, 0x43, 0x18,
        ];
        assert_eq!(digest, expected);
    }

    /// Exactly 56 bytes: triggers double-block padding (remaining >= 56).
    #[test]
    fn test_56_bytes() {
        let msg = [0x61u8; 56]; // 56 'a's
        let digest = sha256(&msg);
        let expected: [u8; 32] = [
            0xb3, 0x54, 0x39, 0xa4, 0xac, 0x6f, 0x09, 0x48,
            0xb6, 0xd6, 0xf9, 0xe3, 0xc6, 0xaf, 0x0f, 0x5f,
            0x59, 0x0c, 0xe2, 0x0f, 0x1b, 0xde, 0x70, 0x90,
            0xef, 0x79, 0x70, 0x68, 0x6e, 0xc6, 0x73, 0x8a,
        ];
        assert_eq!(digest, expected);
    }

    /// Exactly 64 bytes: one full block, then padding is entirely in the next block.
    #[test]
    fn test_64_bytes() {
        let msg = [0x61u8; 64]; // 64 'a's
        let digest = sha256(&msg);
        let expected: [u8; 32] = [
            0xff, 0xe0, 0x54, 0xfe, 0x7a, 0xe0, 0xcb, 0x6d,
            0xc6, 0x5c, 0x3a, 0xf9, 0xb6, 0x1d, 0x52, 0x09,
            0xf4, 0x39, 0x85, 0x1d, 0xb4, 0x3d, 0x0b, 0xa5,
            0x99, 0x73, 0x37, 0xdf, 0x15, 0x46, 0x68, 0xeb,
        ];
        assert_eq!(digest, expected);
    }
}
