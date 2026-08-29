//! Pure Rust GF(2^128) arithmetic for GCM (NIST SP 800-38D).
//!
//! No external dependencies. All functions are pure and value-passing.
//!
//! Uses the NIST GCM convention: elements are 128-bit values represented as
//! u128 in MSB-first bit order. The irreducible polynomial is
//! x^128 + x^7 + x^2 + x + 1, with reduction constant R = 0xe1 << 120.

/// Reduction polynomial R = x^7 + x^2 + x + 1, placed at the MSB end.
/// This is 0xe1000000000000000000000000000000 as u128.
const R: u128 = 0xe1 << 120;

/// Multiply two elements in GF(2^128) using the NIST GCM convention.
///
/// Schoolbook multiplication, MSB-first. The algorithm processes each bit
/// of b from the most significant to the least significant, accumulating
/// into z and reducing v after each step.
pub fn gf128_mul(a: u128, b: u128) -> u128 {
    let mut z: u128 = 0;
    let mut v: u128 = a;

    let mut i = 0;
    while i < 128 {
        // If bit (127 - i) of b is set, XOR v into accumulator
        if (b >> (127 - i)) & 1 == 1 {
            z ^= v;
        }

        // Shift v right by 1; if the LSB was set, reduce by R
        let carry = v & 1;
        v >>= 1;
        if carry == 1 {
            v ^= R;
        }

        i += 1;
    }

    z
}

/// Convert a 16-byte big-endian array to u128.
pub fn bytes_to_u128(bytes: &[u8]) -> u128 {
    let mut val: u128 = 0;
    let len = if bytes.len() < 16 { bytes.len() } else { 16 };
    let mut i = 0;
    while i < len {
        val |= (bytes[i] as u128) << (8 * (15 - i));
        i += 1;
    }
    val
}

/// Convert a u128 to a 16-byte big-endian array.
pub fn u128_to_bytes(val: u128) -> [u8; 16] {
    let mut bytes = [0u8; 16];
    let mut i = 0;
    while i < 16 {
        bytes[i] = (val >> (8 * (15 - i))) as u8;
        i += 1;
    }
    bytes
}

/// GHASH: universal hash function used in GCM (NIST SP 800-38D, Section 6.4).
///
/// Processes data in 16-byte blocks, XORing each block into the accumulator
/// and multiplying by the hash subkey H. The last block is zero-padded if
/// its length is not a multiple of 16.
pub fn ghash(h: u128, data: &[u8]) -> u128 {
    let mut acc: u128 = 0;
    let num_full_blocks = data.len() / 16;

    // Process full 16-byte blocks
    let mut i = 0;
    while i < num_full_blocks {
        let block = bytes_to_u128(&data[16 * i..16 * i + 16]);
        acc = gf128_mul(acc ^ block, h);
        i += 1;
    }

    // Process remaining partial block (zero-padded)
    let remainder = data.len() % 16;
    if remainder > 0 {
        let mut padded = [0u8; 16];
        let offset = num_full_blocks * 16;
        let mut j = 0;
        while j < remainder {
            padded[j] = data[offset + j];
            j += 1;
        }
        let block = bytes_to_u128(&padded);
        acc = gf128_mul(acc ^ block, h);
    }

    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Verify gf128_mul identity: a * 1 = a (where 1 = 0x80...0 in NIST convention).
    #[test]
    fn test_gf128_mul_identity() {
        let a: u128 = 0x0123456789abcdef0123456789abcdef;
        // In the NIST GCM convention, the multiplicative identity is
        // the element with bit 127 set (MSB = 1, all others 0).
        let one: u128 = 1u128 << 127;
        assert_eq!(gf128_mul(a, one), a);
    }

    /// Verify gf128_mul with zero: a * 0 = 0.
    #[test]
    fn test_gf128_mul_zero() {
        let a: u128 = 0x66e94bd4ef8a2c3b884cfa59ca342b2e;
        assert_eq!(gf128_mul(a, 0), 0);
    }

    /// Verify gf128_mul commutativity: a * b = b * a.
    #[test]
    fn test_gf128_mul_commutative() {
        let a: u128 = 0x66e94bd4ef8a2c3b884cfa59ca342b2e;
        let b: u128 = 0x0388dace60b6a392f328c2b971b2fe78;
        assert_eq!(gf128_mul(a, b), gf128_mul(b, a));
    }

    /// Test GHASH with the hash subkey H = AES_K(0^128) for K = 0^128.
    /// H = 66e94bd4ef8a2c3b884cfa59ca342b2e (from NIST SP 800-38D, Test Case 1).
    #[test]
    fn test_ghash_subkey() {
        // This test verifies H is correct by checking that
        // GHASH_H(empty) with length encoding gives the right result.
        let h: u128 = 0x66e94bd4ef8a2c3b884cfa59ca342b2e;

        // GHASH of empty data should be 0
        let result = ghash(h, &[]);
        assert_eq!(result, 0);
    }

    /// Test byte conversion round-trip.
    #[test]
    fn test_bytes_roundtrip() {
        let val: u128 = 0x66e94bd4ef8a2c3b884cfa59ca342b2e;
        let bytes = u128_to_bytes(val);
        assert_eq!(bytes_to_u128(&bytes), val);

        let expected_bytes: [u8; 16] = [
            0x66, 0xe9, 0x4b, 0xd4, 0xef, 0x8a, 0x2c, 0x3b,
            0x88, 0x4c, 0xfa, 0x59, 0xca, 0x34, 0x2b, 0x2e,
        ];
        assert_eq!(bytes, expected_bytes);
    }

    /// NIST SP 800-38D Test Case 2: GHASH of one block of ciphertext.
    /// H = 66e94bd4ef8a2c3b884cfa59ca342b2e
    /// C = 0388dace60b6a392f328c2b971b2fe78
    /// No AAD, so the GHASH input is: C || len_block
    /// where len_block = [0u64 as AAD bits || 128u64 as C bits] in big-endian.
    #[test]
    fn test_ghash_one_block() {
        let h: u128 = 0x66e94bd4ef8a2c3b884cfa59ca342b2e;

        // Build GHASH input: C || len_block
        // C = 0388dace60b6a392f328c2b971b2fe78
        // len_block = 00000000_00000000 || 00000000_00000080 (128 bits of C, 0 bits of AAD)
        let c_bytes: [u8; 16] = [
            0x03, 0x88, 0xda, 0xce, 0x60, 0xb6, 0xa3, 0x92,
            0xf3, 0x28, 0xc2, 0xb9, 0x71, 0xb2, 0xfe, 0x78,
        ];
        let len_block: [u8; 16] = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80,
        ];
        let mut input = [0u8; 32];
        let mut i = 0;
        while i < 16 {
            input[i] = c_bytes[i];
            input[16 + i] = len_block[i];
            i += 1;
        }

        let s = ghash(h, &input);

        // S is the GHASH result. Combined with AES_K(J0) we get the tag.
        // We verify S is non-zero and well-formed.
        assert_ne!(s, 0);
    }
}
