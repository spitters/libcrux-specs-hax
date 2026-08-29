//! SHA-3 and SHAKE specification (FIPS 202).
//!
//! Pure value-passing implementation with the `Keccak-f[1600]` permutation
//! inlined. Copied from `rust-specs/src/sha3.rs` in
//! <https://github.com/spitters/libcrux-lean-specs> (MIT, Bas Spitters).
//!
//! No external dependencies. All functions are `pub`.

// ---------------------------------------------------------------------------
// Keccak-f[1600] permutation (FIPS 202)
// ---------------------------------------------------------------------------

/// Keccak round constants (FIPS 202, Section 3.2.5).
const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082,
    0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088,
    0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b,
    0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080,
    0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080,
    0x0000000080000001, 0x8000000080008008,
];

/// Rotation offsets for the rho step (FIPS 202, Table 2).
/// Indexed as `x + 5*y` where `(x,y)` is the lane coordinate.
const ROT_OFFSETS: [u32; 25] = [
     0,  1, 62, 28, 27,
    36, 44,  6, 55, 20,
     3, 10, 43, 25, 39,
    41, 45, 15, 21,  8,
    18,  2, 61, 56, 14,
];

/// Rotate a u64 left by `n` bits.
#[inline]
pub fn rotl64(x: u64, n: u32) -> u64 {
    if n == 0 || n == 64 {
        x
    } else {
        (x << n) | (x >> (64 - n))
    }
}

/// Theta step: column parity diffusion (FIPS 202, Section 3.2.1).
pub fn theta(state: [u64; 25]) -> [u64; 25] {
    let mut c = [0u64; 5];
    let mut x = 0;
    while x < 5 {
        c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        x += 1;
    }

    let mut d = [0u64; 5];
    x = 0;
    while x < 5 {
        d[x] = c[(x + 4) % 5] ^ rotl64(c[(x + 1) % 5], 1);
        x += 1;
    }

    let mut result = [0u64; 25];
    let mut i = 0;
    while i < 25 {
        result[i] = state[i] ^ d[i % 5];
        i += 1;
    }
    result
}

/// Rho step: bitwise rotation (FIPS 202, Section 3.2.2).
pub fn rho(state: [u64; 25]) -> [u64; 25] {
    let mut result = [0u64; 25];
    let mut i = 0;
    while i < 25 {
        result[i] = rotl64(state[i], ROT_OFFSETS[i]);
        i += 1;
    }
    result
}

/// Pi step: lane transposition (FIPS 202, Section 3.2.3).
/// `A'[x, y] = A[(x + 3y) mod 5, x]`.
pub fn pi(state: [u64; 25]) -> [u64; 25] {
    let mut result = [0u64; 25];
    let mut y = 0;
    while y < 5 {
        let mut x = 0;
        while x < 5 {
            result[x + 5 * y] = state[((x + 3 * y) % 5) + 5 * x];
            x += 1;
        }
        y += 1;
    }
    result
}

/// Chi step: non-linear row mixing (FIPS 202, Section 3.2.4).
pub fn chi(state: [u64; 25]) -> [u64; 25] {
    let mut result = [0u64; 25];
    let mut y = 0;
    while y < 5 {
        let mut x = 0;
        while x < 5 {
            result[x + 5 * y] = state[x + 5 * y]
                ^ ((!state[(x + 1) % 5 + 5 * y]) & state[(x + 2) % 5 + 5 * y]);
            x += 1;
        }
        y += 1;
    }
    result
}

/// Iota step: round constant addition (FIPS 202, Section 3.2.5).
pub fn iota(state: [u64; 25], round: usize) -> [u64; 25] {
    let mut result = state;
    result[0] ^= RC[round];
    result
}

/// `Keccak-f[1600]` permutation: 24 rounds of theta, rho, pi, chi, iota.
pub fn keccak_f1600(state: [u64; 25]) -> [u64; 25] {
    let mut s = state;
    let mut round = 0;
    while round < 24 {
        s = theta(s);
        s = rho(s);
        s = pi(s);
        s = chi(s);
        s = iota(s, round);
        round += 1;
    }
    s
}

/// Convert a byte slice (up to 200 bytes) to the Keccak u64 lane array.
///
/// Lanes are in `x + 5*y` order. Byte order within each lane is little-endian.
/// Bytes beyond the slice length are treated as zero.
pub fn bytes_to_state(bytes: &[u8]) -> [u64; 25] {
    let mut state = [0u64; 25];
    let mut i = 0;
    while i < 25 && i * 8 < bytes.len() {
        let mut lane = 0u64;
        let mut j = 0;
        while j < 8 {
            if i * 8 + j < bytes.len() {
                lane |= (bytes[i * 8 + j] as u64) << (j * 8);
            }
            j += 1;
        }
        state[i] = lane;
        i += 1;
    }
    state
}

/// Convert the Keccak u64 lane array back to 200 bytes (little-endian).
pub fn state_to_bytes(state: [u64; 25]) -> [u8; 200] {
    let mut bytes = [0u8; 200];
    let mut i = 0;
    while i < 25 {
        let mut j = 0;
        while j < 8 {
            bytes[i * 8 + j] = (state[i] >> (j * 8)) as u8;
            j += 1;
        }
        i += 1;
    }
    bytes
}

// ---------------------------------------------------------------------------
// Sponge construction (FIPS 202, Section 4)
// ---------------------------------------------------------------------------

/// XOR a byte into the Keccak state at byte position `pos`.
///
/// Position `pos` maps to lane `pos / 8`, byte offset `pos % 8` (little-endian).
fn xor_byte_into_state(state: &mut [u64; 25], pos: usize, byte: u8) {
    let lane = pos / 8;
    let offset = pos % 8;
    state[lane] ^= (byte as u64) << (offset * 8);
}

/// Keccak sponge absorb phase.
///
/// Absorbs `data` into `state` at the given `rate` (in bytes), using `domain_sep`
/// as the domain separation byte. Applies multi-rate padding (FIPS 202, Section 5.1):
///   - XOR `domain_sep` at position `len(data) mod rate`
///   - XOR `0x80` at position `rate - 1`
///
/// Returns the state after absorption and final permutation.
pub fn keccak_absorb(
    state: [u64; 25],
    rate: usize,
    data: &[u8],
    domain_sep: u8,
) -> [u64; 25] {
    let mut s = state;
    let mut offset = 0;

    // Absorb full blocks: XOR rate bytes into state, then permute.
    while offset + rate <= data.len() {
        let mut i = 0;
        while i < rate {
            xor_byte_into_state(&mut s, i, data[offset + i]);
            i += 1;
        }
        s = keccak_f1600(s);
        offset += rate;
    }

    // Absorb remaining bytes (partial block).
    let remaining = data.len() - offset;
    let mut i = 0;
    while i < remaining {
        xor_byte_into_state(&mut s, i, data[offset + i]);
        i += 1;
    }

    // Padding: domain separation byte at position `remaining`, 0x80 at `rate - 1`.
    // If remaining == rate - 1, both land on the same byte and are XORed together.
    xor_byte_into_state(&mut s, remaining, domain_sep);
    xor_byte_into_state(&mut s, rate - 1, 0x80);

    // Final permutation after padding.
    s = keccak_f1600(s);
    s
}

/// Keccak sponge squeeze phase.
///
/// Extracts `output_len` bytes from the sponge state, permuting between
/// rate-sized output blocks as needed.
pub fn keccak_squeeze(
    state: [u64; 25],
    rate: usize,
    output_len: usize,
) -> Vec<u8> {
    let mut s = state;
    let mut output = Vec::with_capacity(output_len);
    let mut squeezed = 0;

    while squeezed < output_len {
        let block = state_to_bytes(s);
        let available = if output_len - squeezed < rate {
            output_len - squeezed
        } else {
            rate
        };

        let mut i = 0;
        while i < available {
            output.push(block[i]);
            i += 1;
        }
        squeezed += available;

        // Permute for the next block if more output is needed.
        if squeezed < output_len {
            s = keccak_f1600(s);
        }
    }

    output
}

// ---------------------------------------------------------------------------
// SHA-3 fixed-output hash functions (FIPS 202, Section 6.1)
// ---------------------------------------------------------------------------

/// SHA3-224: 224-bit hash. Rate = 144 bytes, domain separation = 0x06.
pub fn sha3_224(msg: &[u8]) -> [u8; 28] {
    let state = [0u64; 25];
    let state = keccak_absorb(state, 144, msg, 0x06);
    let output = keccak_squeeze(state, 144, 28);
    let mut result = [0u8; 28];
    let mut i = 0;
    while i < 28 {
        result[i] = output[i];
        i += 1;
    }
    result
}

/// SHA3-256: 256-bit hash. Rate = 136 bytes, domain separation = 0x06.
pub fn sha3_256(msg: &[u8]) -> [u8; 32] {
    let state = [0u64; 25];
    let state = keccak_absorb(state, 136, msg, 0x06);
    let output = keccak_squeeze(state, 136, 32);
    let mut result = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        result[i] = output[i];
        i += 1;
    }
    result
}

/// SHA3-384: 384-bit hash. Rate = 104 bytes, domain separation = 0x06.
pub fn sha3_384(msg: &[u8]) -> [u8; 48] {
    let state = [0u64; 25];
    let state = keccak_absorb(state, 104, msg, 0x06);
    let output = keccak_squeeze(state, 104, 48);
    let mut result = [0u8; 48];
    let mut i = 0;
    while i < 48 {
        result[i] = output[i];
        i += 1;
    }
    result
}

/// SHA3-512: 512-bit hash. Rate = 72 bytes, domain separation = 0x06.
pub fn sha3_512(msg: &[u8]) -> [u8; 64] {
    let state = [0u64; 25];
    let state = keccak_absorb(state, 72, msg, 0x06);
    let output = keccak_squeeze(state, 72, 64);
    let mut result = [0u8; 64];
    let mut i = 0;
    while i < 64 {
        result[i] = output[i];
        i += 1;
    }
    result
}

// ---------------------------------------------------------------------------
// SHAKE extendable-output functions (FIPS 202, Section 6.2)
// ---------------------------------------------------------------------------

/// SHAKE128: extendable-output function. Rate = 168 bytes, domain separation = 0x1F.
pub fn shake128(msg: &[u8], output_len: usize) -> Vec<u8> {
    let state = [0u64; 25];
    let state = keccak_absorb(state, 168, msg, 0x1F);
    keccak_squeeze(state, 168, output_len)
}

/// SHAKE256: extendable-output function. Rate = 136 bytes, domain separation = 0x1F.
pub fn shake256(msg: &[u8], output_len: usize) -> Vec<u8> {
    let state = [0u64; 25];
    let state = keccak_absorb(state, 136, msg, 0x1F);
    keccak_squeeze(state, 136, output_len)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// NIST FIPS 202 test: SHA3-256 of empty string.
    /// Expected: a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a
    #[test]
    fn test_sha3_256_empty() {
        let hash = sha3_256(b"");
        let expected: [u8; 32] = [
            0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66,
            0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61, 0xd6, 0x62,
            0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa,
            0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8, 0x43, 0x4a,
        ];
        assert_eq!(hash, expected);
    }

    /// NIST FIPS 202 test: SHA3-256 of "abc".
    /// Expected: 3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532
    #[test]
    fn test_sha3_256_abc() {
        let hash = sha3_256(b"abc");
        let expected: [u8; 32] = [
            0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2,
            0x04, 0x5c, 0x17, 0x2d, 0x6b, 0xd3, 0x90, 0xbd,
            0x85, 0x5f, 0x08, 0x6e, 0x3e, 0x9d, 0x52, 0x5b,
            0x46, 0xbf, 0xe2, 0x45, 0x11, 0x43, 0x15, 0x32,
        ];
        assert_eq!(hash, expected);
    }

    /// NIST FIPS 202 test: SHA3-512 of empty string.
    /// Expected: a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a6
    ///           15b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26
    #[test]
    fn test_sha3_512_empty() {
        let hash = sha3_512(b"");
        let expected: [u8; 64] = [
            0xa6, 0x9f, 0x73, 0xcc, 0xa2, 0x3a, 0x9a, 0xc5,
            0xc8, 0xb5, 0x67, 0xdc, 0x18, 0x5a, 0x75, 0x6e,
            0x97, 0xc9, 0x82, 0x16, 0x4f, 0xe2, 0x58, 0x59,
            0xe0, 0xd1, 0xdc, 0xc1, 0x47, 0x5c, 0x80, 0xa6,
            0x15, 0xb2, 0x12, 0x3a, 0xf1, 0xf5, 0xf9, 0x4c,
            0x11, 0xe3, 0xe9, 0x40, 0x2c, 0x3a, 0xc5, 0x58,
            0xf5, 0x00, 0x19, 0x9d, 0x95, 0xb6, 0xd3, 0xe3,
            0x01, 0x75, 0x85, 0x86, 0x28, 0x1d, 0xcd, 0x26,
        ];
        assert_eq!(hash, expected);
    }

    /// NIST FIPS 202 test: SHA3-224 of empty string.
    /// Expected: 6b4e03423667dbb73b6e15454f0eb1abd4597f9a1b078e3f5b5a6bc7
    #[test]
    fn test_sha3_224_empty() {
        let hash = sha3_224(b"");
        let expected: [u8; 28] = [
            0x6b, 0x4e, 0x03, 0x42, 0x36, 0x67, 0xdb, 0xb7,
            0x3b, 0x6e, 0x15, 0x45, 0x4f, 0x0e, 0xb1, 0xab,
            0xd4, 0x59, 0x7f, 0x9a, 0x1b, 0x07, 0x8e, 0x3f,
            0x5b, 0x5a, 0x6b, 0xc7,
        ];
        assert_eq!(hash, expected);
    }

    /// NIST FIPS 202 test: SHA3-384 of empty string.
    /// Expected: 0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2a
    ///           c3713831264adb47fb6bd1e058d5f004
    #[test]
    fn test_sha3_384_empty() {
        let hash = sha3_384(b"");
        let expected: [u8; 48] = [
            0x0c, 0x63, 0xa7, 0x5b, 0x84, 0x5e, 0x4f, 0x7d,
            0x01, 0x10, 0x7d, 0x85, 0x2e, 0x4c, 0x24, 0x85,
            0xc5, 0x1a, 0x50, 0xaa, 0xaa, 0x94, 0xfc, 0x61,
            0x99, 0x5e, 0x71, 0xbb, 0xee, 0x98, 0x3a, 0x2a,
            0xc3, 0x71, 0x38, 0x31, 0x26, 0x4a, 0xdb, 0x47,
            0xfb, 0x6b, 0xd1, 0xe0, 0x58, 0xd5, 0xf0, 0x04,
        ];
        assert_eq!(hash, expected);
    }

    /// SHAKE128 of empty string, 32 bytes output.
    /// Expected: 7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26
    #[test]
    fn test_shake128_empty_32() {
        let output = shake128(b"", 32);
        let expected: [u8; 32] = [
            0x7f, 0x9c, 0x2b, 0xa4, 0xe8, 0x8f, 0x82, 0x7d,
            0x61, 0x60, 0x45, 0x50, 0x76, 0x05, 0x85, 0x3e,
            0xd7, 0x3b, 0x80, 0x93, 0xf6, 0xef, 0xbc, 0x88,
            0xeb, 0x1a, 0x6e, 0xac, 0xfa, 0x66, 0xef, 0x26,
        ];
        assert_eq!(&output[..], &expected[..]);
    }

    /// SHAKE256 of empty string, 64 bytes output.
    /// Expected: 46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f
    ///           d75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be
    #[test]
    fn test_shake256_empty_64() {
        let output = shake256(b"", 64);
        let expected: [u8; 64] = [
            0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13,
            0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb, 0x24,
            0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82,
            0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5, 0x76, 0x2f,
            0xd7, 0x5d, 0xc4, 0xdd, 0xd8, 0xc0, 0xf2, 0x00,
            0xcb, 0x05, 0x01, 0x9d, 0x67, 0xb5, 0x92, 0xf6,
            0xfc, 0x82, 0x1c, 0x49, 0x47, 0x9a, 0xb4, 0x86,
            0x40, 0x29, 0x2e, 0xac, 0xb3, 0xb7, 0xc4, 0xbe,
        ];
        assert_eq!(&output[..], &expected[..]);
    }

    /// Test that SHAKE128 produces correct output for longer squeeze (> 1 rate block).
    #[test]
    fn test_shake128_long_squeeze() {
        let output = shake128(b"", 256);
        // First 32 bytes must match the short squeeze.
        let short = shake128(b"", 32);
        assert_eq!(&output[..32], &short[..]);
        assert_eq!(output.len(), 256);
    }

    /// Test SHA3-256 with a message that spans multiple rate blocks.
    /// Input: 200 bytes of 0xa3.
    /// Expected: 79f38adec5c20307a98ef76e8324afbfd46cfd81b22e3973c65fa1bd9de31787
    #[test]
    fn test_sha3_256_200_bytes() {
        let msg = [0xa3u8; 200];
        let hash = sha3_256(&msg);
        let expected: [u8; 32] = [
            0x79, 0xf3, 0x8a, 0xde, 0xc5, 0xc2, 0x03, 0x07,
            0xa9, 0x8e, 0xf7, 0x6e, 0x83, 0x24, 0xaf, 0xbf,
            0xd4, 0x6c, 0xfd, 0x81, 0xb2, 0x2e, 0x39, 0x73,
            0xc6, 0x5f, 0xa1, 0xbd, 0x9d, 0xe3, 0x17, 0x87,
        ];
        assert_eq!(hash, expected);
    }
}
