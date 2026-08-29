//! Pure Rust Poly1305 MAC specification (RFC 8439, Section 2.5).
//!
//! Poly1305 computes a 16-byte authentication tag from a variable-length message
//! and a 32-byte one-time key. The tag is computed as:
//!
//! ```text
//!   r = clamp(key[0..16])
//!   s = le_num(key[16..32])
//!   accumulator = 0
//!   for each 16-byte block:
//!     n = le_num(block) + 2^(8*block_len)
//!     accumulator = (accumulator + n) * r  mod  (2^130 - 5)
//!   tag = (accumulator + s) mod 2^128
//! ```
//!
//! Arithmetic is in GF(2^130-5). Since values can be up to 131 bits, we
//! represent them as `(lo: u128, hi: u8)` where value = lo + hi * 2^128.
//! Products require up to 256 bits, represented as `(lo: u128, hi: u128)`.
//!
//! No external dependencies.

/// A 130-bit number represented as (low 128 bits, high 2 bits).
/// Value = lo + (hi as u128) * 2^128.
/// hi is at most 7 (3 bits) before reduction, at most 3 (2 bits) after.
#[derive(Clone, Copy, Debug)]
pub struct U130 {
    pub lo: u128,
    pub hi: u8,
}

/// A 256-bit number represented as two u128 halves.
/// Value = lo + hi * 2^128.
#[derive(Clone, Copy, Debug)]
pub struct U256 {
    pub lo: u128,
    pub hi: u128,
}

/// The prime modulus p = 2^130 - 5.
/// We store this symbolically and reduce using the identity: 2^130 = 5 (mod p).
pub const P_LO: u128 = u128::MAX - 4; // 2^128 - 5
pub const P_HI: u8 = 3; // 2^130 - 5 = (2^128 - 5) + 3 * 2^128

/// Clamp the r value per RFC 8439, Section 2.5.
///
/// Certain bits of r must be cleared to ensure the key is in the correct form:
/// - Clear top 4 bits of bytes 3, 7, 11, 15 (i.e., `r[3], r[7], r[11], r[15] &= 0x0f`)
/// - Clear bottom 2 bits of bytes 4, 8, 12 (i.e., `r[4], r[8], r[12] &= 0xfc`)
pub fn poly1305_clamp(r: &[u8; 16]) -> [u8; 16] {
    let mut clamped = *r;
    clamped[3] &= 0x0f;
    clamped[7] &= 0x0f;
    clamped[11] &= 0x0f;
    clamped[15] &= 0x0f;
    clamped[4] &= 0xfc;
    clamped[8] &= 0xfc;
    clamped[12] &= 0xfc;
    clamped
}

/// Decode a little-endian byte slice (up to 17 bytes) into a U130.
///
/// For Poly1305, this handles blocks up to 16 bytes plus the "high bit"
/// (2^(8*len)) which makes the result up to 129 bits.
pub fn le_bytes_to_u130(bytes: &[u8]) -> U130 {
    let mut lo: u128 = 0;
    let mut hi: u8 = 0;
    for i in 0..bytes.len() {
        if i < 16 {
            lo |= (bytes[i] as u128) << (8 * i);
        } else {
            // byte 16 goes into hi
            hi |= bytes[i];
        }
    }
    U130 { lo, hi }
}

/// Decode a little-endian byte slice (up to 16 bytes) into a u128.
pub fn le_bytes_to_num(bytes: &[u8]) -> u128 {
    let mut result: u128 = 0;
    for i in 0..bytes.len() {
        if i < 16 {
            result |= (bytes[i] as u128) << (8 * i);
        }
    }
    result
}

/// Encode a u128 as 16 little-endian bytes.
pub fn num_to_le_bytes(value: u128) -> [u8; 16] {
    let mut out = [0u8; 16];
    for i in 0..16 {
        out[i] = (value >> (8 * i)) as u8;
    }
    out
}

/// Add a U130 value to the accumulator.
/// Result may have hi up to 7 (3 bits).
pub fn u130_add(a: U130, b: U130) -> U130 {
    let (lo, carry) = a.lo.overflowing_add(b.lo);
    let hi = a.hi + b.hi + (carry as u8);
    U130 { lo, hi }
}

/// Multiply two u128 values, returning a U256 (256-bit result).
///
/// Uses schoolbook multiplication with 64-bit limbs:
/// a = a_lo + a_hi * 2^64
/// b = b_lo + b_hi * 2^64
/// a*b = a_lo*b_lo + (a_lo*b_hi + a_hi*b_lo)*2^64 + a_hi*b_hi*2^128
fn u128_mul(a: u128, b: u128) -> U256 {
    let a_lo = a as u64 as u128;
    let a_hi = (a >> 64) as u64 as u128;
    let b_lo = b as u64 as u128;
    let b_hi = (b >> 64) as u64 as u128;

    let ll = a_lo * b_lo;
    let lh = a_lo * b_hi;
    let hl = a_hi * b_lo;
    let hh = a_hi * b_hi;

    // Combine: lo128 gets ll + low64(lh+hl)<<64, hi128 gets hh + high64(lh+hl) + carries
    let (mid_sum, mid_carry) = lh.overflowing_add(hl);
    let mid_lo = (mid_sum as u64 as u128) << 64;
    let mid_hi = (mid_sum >> 64) as u64 as u128;

    let (lo, carry1) = ll.overflowing_add(mid_lo);
    let hi = hh
        .wrapping_add(mid_hi)
        .wrapping_add(carry1 as u128)
        .wrapping_add(if mid_carry { 1u128 << 64 } else { 0 });

    U256 { lo, hi }
}

/// Multiply a U130 accumulator by a u128 r value, returning up to 258 bits.
///
/// acc = acc_lo + acc_hi * 2^128   (acc_hi <= 7)
/// r is at most 124 bits (after clamping)
///
/// result = acc_lo * r + acc_hi * r * 2^128
///
/// Then reduce modulo 2^130 - 5.
pub fn u130_mul_mod(acc: U130, r: u128) -> U130 {
    // acc_lo * r: up to 256 bits
    let prod_lo = u128_mul(acc.lo, r);

    // acc_hi * r: up to 128 + 3 = 131 bits, fits in u128 since acc_hi <= 7 and r < 2^124
    let prod_hi_val = (acc.hi as u128) * r;

    // Full product = prod_lo.lo + (prod_lo.hi + prod_hi_val) * 2^128
    let (upper, carry) = prod_lo.hi.overflowing_add(prod_hi_val);

    // Reduce mod 2^130 - 5.
    // total = prod_lo.lo + upper * 2^128 + carry * 2^256
    // Split total at bit 130:
    //   bits [0..129]:  prod_lo.lo + (upper & 3) * 2^128
    //   bits [130..]:   (upper >> 2) + carry * 2^126
    // Since 2^130 ≡ 5 (mod p), high_part * 2^130 ≡ high_part * 5.

    let upper_lo2 = (upper & 3) as u8; // low 2 bits of upper
    let upper_hi = upper >> 2; // remaining bits

    // low 130 bits = prod_lo.lo + upper_lo2 * 2^128
    // This fits since prod_lo.lo < 2^128 and upper_lo2 * 2^128 < 2^130, sum < 2^131
    let base_lo = prod_lo.lo;
    let base_hi = upper_lo2; // value = base_lo + base_hi * 2^128, < 2^131

    // high part (above bit 130) = upper_hi + carry * 2^126
    // Multiply by 5 and add to base
    let high_times_5 = upper_hi
        .wrapping_mul(5)
        .wrapping_add(if carry { 5u128 << 126 } else { 0 });

    // Add high_times_5 to (base_lo, base_hi)
    let (sum_lo, c) = base_lo.overflowing_add(high_times_5);
    let sum_hi = base_hi + (c as u8);

    // One more partial reduction if sum_hi >= 4 (i.e., value >= 2^130)
    let extra = sum_hi >> 2; // how many times 2^130
    let final_hi = sum_hi & 3;
    let (final_lo, c2) = sum_lo.overflowing_add((extra as u128) * 5);
    let final_hi2 = final_hi + (c2 as u8);

    U130 {
        lo: final_lo,
        hi: final_hi2,
    }
}

/// Final reduction: ensure value is in [0, 2^130-5).
///
/// After all block processing, the accumulator is at most slightly above p.
/// We check if acc >= p, and if so subtract p.
fn final_reduce(acc: U130) -> u128 {
    // p = 2^130 - 5 = 3 * 2^128 + (2^128 - 5)
    // Check if acc >= p: acc.hi > 3, or (acc.hi == 3 and acc.lo >= 2^128-5)
    // But acc.hi <= 3 after partial reduction.
    // If acc.hi == 3 and acc.lo >= (2^128 - 5), then acc >= p.
    // If acc.hi < 3, then acc < p (since 3 * 2^128 > acc).
    // Actually we also need acc.hi == 4 case: value exactly 2^130 maps to 5.

    // Add 5 and check if it overflows past 2^130
    let (test_lo, c) = acc.lo.overflowing_add(5);
    let test_hi = acc.hi + (c as u8);

    if test_hi >= 4 {
        // acc + 5 >= 2^130, so acc >= 2^130 - 5 = p
        // Result = acc - p = acc + 5 - 2^130
        // = (test_lo, test_hi - 4) as a 130-bit number
        // Since test_hi is at most 4 or 5, test_hi & 3 gives the right bits
        // But we only want the low 128 bits since result < 2^130 - 5 < 2^128
        // Actually result could be up to 2^130-6 - (2^130-5) = ... no.
        // If acc was exactly 2^130 - 1, then acc - p = 4, so result fits in u128.
        // The hi bits after subtracting are (test_hi - 4), which is 0 or 1.
        // If 1, that means 2^128 + test_lo, but that can't happen since acc < 2p.
        // After partial reduction acc < 2^131 and after adding at most 2^131 + n < 2*p + p = 3p,
        // so acc < 2p. Thus result = acc - p < p < 2^130, and since p < 2^130, fine.
        // But we want mod 2^128 for the final tag, so just return test_lo.
        test_lo
    } else {
        acc.lo
    }
}

/// Compute the Poly1305 MAC tag (RFC 8439, Section 2.5.1).
///
/// 1. Split key into r (first 16 bytes, clamped) and s (last 16 bytes).
/// 2. Process each 16-byte block: add high bit, accumulate (acc + n) * r mod p.
/// 3. Final tag = (acc + s) mod 2^128, as 16 little-endian bytes.
pub fn poly1305(msg: &[u8], key: &[u8; 32]) -> [u8; 16] {
    // Split key
    let mut r_bytes = [0u8; 16];
    for i in 0..16 {
        r_bytes[i] = key[i];
    }
    r_bytes = poly1305_clamp(&r_bytes);
    let r = le_bytes_to_num(&r_bytes);

    let mut s_bytes = [0u8; 16];
    for i in 0..16 {
        s_bytes[i] = key[16 + i];
    }
    let s = le_bytes_to_num(&s_bytes);

    // Process message in 16-byte blocks
    let mut acc = U130 { lo: 0, hi: 0 };
    let num_full_blocks = msg.len() / 16;

    for i in 0..num_full_blocks {
        let mut block = [0u8; 16];
        for j in 0..16 {
            block[j] = msg[i * 16 + j];
        }
        // n = le_num(block) + 2^128
        let n = U130 {
            lo: le_bytes_to_num(&block),
            hi: 1,
        };
        acc = u130_add(acc, n);
        acc = u130_mul_mod(acc, r);
    }

    // Handle final partial block (if any)
    let remainder = msg.len() % 16;
    if remainder > 0 {
        let offset = num_full_blocks * 16;
        let mut block = [0u8; 17];
        for j in 0..remainder {
            block[j] = msg[offset + j];
        }
        // Add high bit at position 8*remainder
        block[remainder] = 0x01;
        // n = le_num(block[0..remainder]) + 2^(8*remainder)
        let n = le_bytes_to_u130(&block[..remainder + 1]);
        acc = u130_add(acc, n);
        acc = u130_mul_mod(acc, r);
    }

    // Final: tag = (acc + s) mod 2^128
    let acc_reduced = final_reduce(acc);
    let tag_full = acc_reduced.wrapping_add(s);
    // mod 2^128 is automatic since u128 wraps

    num_to_le_bytes(tag_full)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// RFC 8439, Section 2.5.2: Poly1305 test vector.
    /// Key (r||s):
    ///   r = 85:d6:be:78:57:55:6d:33:7f:44:52:fe:42:d5:06:a8
    ///   s = 01:03:80:8a:fb:0d:b2:fd:4a:bf:f6:af:41:49:f5:1b
    /// Message: "Cryptographic Forum Research Group"
    #[test]
    fn test_rfc8439_poly1305() {
        #[rustfmt::skip]
        let key: [u8; 32] = [
            0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33,
            0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06, 0xa8,
            0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd,
            0x4a, 0xbf, 0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b,
        ];
        let msg = b"Cryptographic Forum Research Group";
        let tag = poly1305(msg, &key);
        #[rustfmt::skip]
        let expected: [u8; 16] = [
            0xa8, 0x06, 0x1d, 0xc1, 0x30, 0x51, 0x36, 0xc6,
            0xc2, 0x2b, 0x8b, 0xaf, 0x0c, 0x01, 0x27, 0xa9,
        ];
        assert_eq!(tag, expected);
    }

    /// RFC 8439, Section 2.5: Poly1305 clamping test.
    ///
    /// r[3], r[7], r[11], r[15] &= 0x0f
    /// r[4], r[8], r[12] &= 0xfc
    #[test]
    fn test_poly1305_clamp() {
        #[rustfmt::skip]
        let r: [u8; 16] = [
            0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33,
            0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06, 0xa8,
        ];
        let clamped = poly1305_clamp(&r);
        // r[3]: 0x78 & 0x0f = 0x08
        // r[4]: 0x57 & 0xfc = 0x54
        // r[7]: 0x33 & 0x0f = 0x03
        // r[8]: 0x7f & 0xfc = 0x7c
        // r[11]: 0xfe & 0x0f = 0x0e
        // r[12]: 0x42 & 0xfc = 0x40
        // r[15]: 0xa8 & 0x0f = 0x08
        #[rustfmt::skip]
        let expected: [u8; 16] = [
            0x85, 0xd6, 0xbe, 0x08, 0x54, 0x55, 0x6d, 0x03,
            0x7c, 0x44, 0x52, 0x0e, 0x40, 0xd5, 0x06, 0x08,
        ];
        assert_eq!(clamped, expected);
    }

    /// RFC 8439, Section 2.8.2: Poly1305 over the AEAD MAC data.
    ///
    /// This tests poly1305 with the one-time key and the full AEAD MAC input
    /// (padded AAD || padded ciphertext || le64(aad_len) || le64(ct_len)).
    /// One-time key (from chacha20_block with key=80..9f, nonce, counter=0):
    ///   7b ac 2b 25 2d b4 47 af 09 b6 7a 55 a4 e9 55 84
    ///   0a e1 d6 73 10 75 d9 eb 2a 93 75 78 3e d5 53 ff
    #[test]
    fn test_rfc8439_aead_mac_data() {
        #[rustfmt::skip]
        let key: [u8; 32] = [
            0x7b, 0xac, 0x2b, 0x25, 0x2d, 0xb4, 0x47, 0xaf,
            0x09, 0xb6, 0x7a, 0x55, 0xa4, 0xe9, 0x55, 0x84,
            0x0a, 0xe1, 0xd6, 0x73, 0x10, 0x75, 0xd9, 0xeb,
            0x2a, 0x93, 0x75, 0x78, 0x3e, 0xd5, 0x53, 0xff,
        ];
        // Build the AEAD MAC data:
        // pad16(aad) || pad16(ciphertext) || le64(12) || le64(114)
        #[rustfmt::skip]
        let aad: [u8; 12] = [
            0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3,
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
        // Build mac_data: pad16(aad) || pad16(ct) || le64(aad_len) || le64(ct_len)
        let mut mac_data = Vec::new();
        // pad16(aad): 12 bytes + 4 zeros
        for b in &aad { mac_data.push(*b); }
        for _ in 0..4 { mac_data.push(0); }
        // pad16(ct): 114 bytes + 14 zeros (114 % 16 = 2, pad = 14)
        for b in &ciphertext { mac_data.push(*b); }
        for _ in 0..14 { mac_data.push(0); }
        // le64(12)
        for b in &(12u64).to_le_bytes() { mac_data.push(*b); }
        // le64(114)
        for b in &(114u64).to_le_bytes() { mac_data.push(*b); }

        let tag = poly1305(&mac_data, &key);
        #[rustfmt::skip]
        let expected: [u8; 16] = [
            0x1a, 0xe1, 0x0b, 0x59, 0x4f, 0x09, 0xe2, 0x6a,
            0x7e, 0x90, 0x2e, 0xcb, 0xd0, 0x60, 0x06, 0x91,
        ];
        assert_eq!(tag, expected);
    }

    /// Empty message test: poly1305("", key) should just return s (since accumulator stays 0).
    #[test]
    fn test_poly1305_empty() {
        #[rustfmt::skip]
        let key: [u8; 32] = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
            0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10,
            0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
            0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20,
        ];
        let tag = poly1305(b"", &key);
        // acc = 0, tag = (0 + s) mod 2^128 = s
        // s = le_bytes_to_num(key[16..32]) = 0x201f1e1d1c1b1a191817161514131211
        #[rustfmt::skip]
        let expected: [u8; 16] = [
            0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
            0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20,
        ];
        assert_eq!(tag, expected);
    }
}
