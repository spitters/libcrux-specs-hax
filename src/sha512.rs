//! Pure SHA-384/SHA-512 specification (FIPS 180-4, Section 6.4).
//!
//! Value-passing implementation using `u64` words and `[u8; 128]` blocks.
//! No external dependencies — suitable for hax extraction.

/// SHA-512 round constants: first 64 bits of the fractional parts of the
/// cube roots of the first 80 primes (FIPS 180-4, Section 4.2.3).
pub const K_TABLE: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

/// SHA-512 initial hash values: first 64 bits of the fractional parts of the
/// square roots of the first 8 primes (FIPS 180-4, Section 5.3.5).
pub const H512_INIT: [u64; 8] = [
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
];

/// SHA-384 initial hash values: first 64 bits of the fractional parts of the
/// square roots of the 9th through 16th primes (FIPS 180-4, Section 5.3.4).
pub const H384_INIT: [u64; 8] = [
    0xcbbb9d5dc1059ed8, 0x629a292a367cd507,
    0x9159015a3070dd17, 0x152fecd8f70e5939,
    0x67332667ffc00b31, 0x8eb44a8768581511,
    0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4,
];

/// Ch(x, y, z) = (x AND y) XOR (NOT x AND z) (FIPS 180-4, Section 4.1.3).
pub fn ch(x: u64, y: u64, z: u64) -> u64 {
    (x & y) ^ (!x & z)
}

/// Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z) (FIPS 180-4, Section 4.1.3).
pub fn maj(x: u64, y: u64, z: u64) -> u64 {
    (x & y) ^ (x & z) ^ (y & z)
}

/// Big Sigma 0: ROTR^28(x) XOR ROTR^34(x) XOR ROTR^39(x) (FIPS 180-4, Section 4.1.3).
pub fn big_sigma0(x: u64) -> u64 {
    x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39)
}

/// Big Sigma 1: ROTR^14(x) XOR ROTR^18(x) XOR ROTR^41(x) (FIPS 180-4, Section 4.1.3).
pub fn big_sigma1(x: u64) -> u64 {
    x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41)
}

/// Small sigma 0: ROTR^1(x) XOR ROTR^8(x) XOR SHR^7(x) (FIPS 180-4, Section 4.1.3).
pub fn sigma0(x: u64) -> u64 {
    x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7)
}

/// Small sigma 1: ROTR^19(x) XOR ROTR^61(x) XOR SHR^6(x) (FIPS 180-4, Section 4.1.3).
pub fn sigma1(x: u64) -> u64 {
    x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6)
}

/// Prepare the 80-word message schedule from a 128-byte block (FIPS 180-4, Section 6.4.2).
///
/// Words 0..15 are parsed as big-endian u64 from the block.
/// Words 16..79 are computed: W_t = sigma1(W_{t-2}) + W_{t-7} + sigma0(W_{t-15}) + W_{t-16}.
pub fn schedule(block: &[u8; 128]) -> [u64; 80] {
    let mut w = [0u64; 80];

    // Parse block into 16 big-endian u64 words
    let mut i = 0;
    while i < 16 {
        let base = i * 8;
        w[i] = (block[base] as u64) << 56
            | (block[base + 1] as u64) << 48
            | (block[base + 2] as u64) << 40
            | (block[base + 3] as u64) << 32
            | (block[base + 4] as u64) << 24
            | (block[base + 5] as u64) << 16
            | (block[base + 6] as u64) << 8
            | (block[base + 7] as u64);
        i += 1;
    }

    // Extend to 80 words
    while i < 80 {
        w[i] = sigma1(w[i - 2])
            .wrapping_add(w[i - 7])
            .wrapping_add(sigma0(w[i - 15]))
            .wrapping_add(w[i - 16]);
        i += 1;
    }

    w
}

/// Compress one 128-byte block into the hash state (FIPS 180-4, Section 6.4.2).
pub fn compress(block: &[u8; 128], h: [u64; 8]) -> [u64; 8] {
    let w = schedule(block);

    let mut a = h[0];
    let mut b = h[1];
    let mut c = h[2];
    let mut d = h[3];
    let mut e = h[4];
    let mut f = h[5];
    let mut g = h[6];
    let mut hh = h[7];

    let mut t = 0;
    while t < 80 {
        let t1 = hh
            .wrapping_add(big_sigma1(e))
            .wrapping_add(ch(e, f, g))
            .wrapping_add(K_TABLE[t])
            .wrapping_add(w[t]);
        let t2 = big_sigma0(a).wrapping_add(maj(a, b, c));

        hh = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);

        t += 1;
    }

    [
        h[0].wrapping_add(a),
        h[1].wrapping_add(b),
        h[2].wrapping_add(c),
        h[3].wrapping_add(d),
        h[4].wrapping_add(e),
        h[5].wrapping_add(f),
        h[6].wrapping_add(g),
        h[7].wrapping_add(hh),
    ]
}

/// SHA-512 hash (FIPS 180-4, Section 6.4).
///
/// Pads the message to a multiple of 128 bytes (1024 bits) using
/// Merkle-Damgard strengthening with a 128-bit big-endian length field.
pub fn sha512(msg: &[u8]) -> [u8; 64] {
    let mut h = H512_INIT;
    let msg_len = msg.len();
    let bit_len = (msg_len as u128) * 8;

    // Process complete 128-byte blocks
    let mut offset = 0;
    while offset + 128 <= msg_len {
        let mut block = [0u8; 128];
        let mut i = 0;
        while i < 128 {
            block[i] = msg[offset + i];
            i += 1;
        }
        h = compress(&block, h);
        offset += 128;
    }

    // Remaining bytes + padding
    let remaining = msg_len - offset;
    let mut block = [0u8; 128];
    let mut i = 0;
    while i < remaining {
        block[i] = msg[offset + i];
        i += 1;
    }

    // Append the 0x80 byte
    block[remaining] = 0x80;

    if remaining >= 112 {
        // Not enough room for the 16-byte length field; compress and start a new block
        h = compress(&block, h);
        block = [0u8; 128];
    }

    // Append 128-bit big-endian message length in the last 16 bytes
    let len_bytes = bit_len.to_be_bytes();
    let mut j = 0;
    while j < 16 {
        block[112 + j] = len_bytes[j];
        j += 1;
    }
    h = compress(&block, h);

    // Serialize hash state as 64 big-endian bytes
    let mut output = [0u8; 64];
    let mut k = 0;
    while k < 8 {
        let bytes = h[k].to_be_bytes();
        let mut b = 0;
        while b < 8 {
            output[k * 8 + b] = bytes[b];
            b += 1;
        }
        k += 1;
    }

    output
}

/// SHA-384 hash (FIPS 180-4, Section 6.5).
///
/// Same algorithm as SHA-512 but with a different initial hash value
/// and the output truncated to 48 bytes (384 bits).
pub fn sha384(msg: &[u8]) -> [u8; 48] {
    let mut h = H384_INIT;
    let msg_len = msg.len();
    let bit_len = (msg_len as u128) * 8;

    // Process complete 128-byte blocks
    let mut offset = 0;
    while offset + 128 <= msg_len {
        let mut block = [0u8; 128];
        let mut i = 0;
        while i < 128 {
            block[i] = msg[offset + i];
            i += 1;
        }
        h = compress(&block, h);
        offset += 128;
    }

    // Remaining bytes + padding
    let remaining = msg_len - offset;
    let mut block = [0u8; 128];
    let mut i = 0;
    while i < remaining {
        block[i] = msg[offset + i];
        i += 1;
    }

    // Append the 0x80 byte
    block[remaining] = 0x80;

    if remaining >= 112 {
        // Not enough room for the 16-byte length field; compress and start a new block
        h = compress(&block, h);
        block = [0u8; 128];
    }

    // Append 128-bit big-endian message length in the last 16 bytes
    let len_bytes = bit_len.to_be_bytes();
    let mut j = 0;
    while j < 16 {
        block[112 + j] = len_bytes[j];
        j += 1;
    }
    h = compress(&block, h);

    // Serialize first 6 hash words as 48 big-endian bytes (truncated output)
    let mut output = [0u8; 48];
    let mut k = 0;
    while k < 6 {
        let bytes = h[k].to_be_bytes();
        let mut b = 0;
        while b < 8 {
            output[k * 8 + b] = bytes[b];
            b += 1;
        }
        k += 1;
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    // FIPS 180-4 / NIST CAVP one-block test: SHA-512("abc")
    #[test]
    fn test_sha512_abc() {
        let expected: [u8; 64] = [
            0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba,
            0xcc, 0x41, 0x73, 0x49, 0xae, 0x20, 0x41, 0x31,
            0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9, 0x7e, 0xa2,
            0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a,
            0x21, 0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8,
            0x36, 0xba, 0x3c, 0x23, 0xa3, 0xfe, 0xeb, 0xbd,
            0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8, 0x0e,
            0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f,
        ];
        assert_eq!(sha512(b"abc"), expected);
    }

    // FIPS 180-4 two-block test: SHA-512 of the 112-byte message
    // "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno
    //  ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
    #[test]
    fn test_sha512_two_blocks() {
        let msg = b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
        let expected: [u8; 64] = [
            0x8e, 0x95, 0x9b, 0x75, 0xda, 0xe3, 0x13, 0xda,
            0x8c, 0xf4, 0xf7, 0x28, 0x14, 0xfc, 0x14, 0x3f,
            0x8f, 0x77, 0x79, 0xc6, 0xeb, 0x9f, 0x7f, 0xa1,
            0x72, 0x99, 0xae, 0xad, 0xb6, 0x88, 0x90, 0x18,
            0x50, 0x1d, 0x28, 0x9e, 0x49, 0x00, 0xf7, 0xe4,
            0x33, 0x1b, 0x99, 0xde, 0xc4, 0xb5, 0x43, 0x3a,
            0xc7, 0xd3, 0x29, 0xee, 0xb6, 0xdd, 0x26, 0x54,
            0x5e, 0x96, 0xe5, 0x5b, 0x87, 0x4b, 0xe9, 0x09,
        ];
        assert_eq!(sha512(msg), expected);
    }

    // SHA-512 of empty message
    #[test]
    fn test_sha512_empty() {
        let expected: [u8; 64] = [
            0xcf, 0x83, 0xe1, 0x35, 0x7e, 0xef, 0xb8, 0xbd,
            0xf1, 0x54, 0x28, 0x50, 0xd6, 0x6d, 0x80, 0x07,
            0xd6, 0x20, 0xe4, 0x05, 0x0b, 0x57, 0x15, 0xdc,
            0x83, 0xf4, 0xa9, 0x21, 0xd3, 0x6c, 0xe9, 0xce,
            0x47, 0xd0, 0xd1, 0x3c, 0x5d, 0x85, 0xf2, 0xb0,
            0xff, 0x83, 0x18, 0xd2, 0x87, 0x7e, 0xec, 0x2f,
            0x63, 0xb9, 0x31, 0xbd, 0x47, 0x41, 0x7a, 0x81,
            0xa5, 0x38, 0x32, 0x7a, 0xf9, 0x27, 0xda, 0x3e,
        ];
        assert_eq!(sha512(b""), expected);
    }

    // FIPS 180-4 one-block test: SHA-384("abc")
    #[test]
    fn test_sha384_abc() {
        let expected: [u8; 48] = [
            0xcb, 0x00, 0x75, 0x3f, 0x45, 0xa3, 0x5e, 0x8b,
            0xb5, 0xa0, 0x3d, 0x69, 0x9a, 0xc6, 0x50, 0x07,
            0x27, 0x2c, 0x32, 0xab, 0x0e, 0xde, 0xd1, 0x63,
            0x1a, 0x8b, 0x60, 0x5a, 0x43, 0xff, 0x5b, 0xed,
            0x80, 0x86, 0x07, 0x2b, 0xa1, 0xe7, 0xcc, 0x23,
            0x58, 0xba, 0xec, 0xa1, 0x34, 0xc8, 0x25, 0xa7,
        ];
        assert_eq!(sha384(b"abc"), expected);
    }

    // SHA-384 of empty message
    #[test]
    fn test_sha384_empty() {
        let expected: [u8; 48] = [
            0x38, 0xb0, 0x60, 0xa7, 0x51, 0xac, 0x96, 0x38,
            0x4c, 0xd9, 0x32, 0x7e, 0xb1, 0xb1, 0xe3, 0x6a,
            0x21, 0xfd, 0xb7, 0x11, 0x14, 0xbe, 0x07, 0x43,
            0x4c, 0x0c, 0xc7, 0xbf, 0x63, 0xf6, 0xe1, 0xda,
            0x27, 0x4e, 0xde, 0xbf, 0xe7, 0x6f, 0x65, 0xfb,
            0xd5, 0x1a, 0xd2, 0xf1, 0x48, 0x98, 0xb9, 0x5b,
        ];
        assert_eq!(sha384(b""), expected);
    }
}
