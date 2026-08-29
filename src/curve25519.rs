//! Pure Rust X25519 Diffie-Hellman specification (RFC 7748).
//!
//! Field: GF(2^255 - 19). Field elements are represented as `[u64; 5]` with
//! 51-bit limbs:
//! `value = limbs[0] + limbs[1]*2^51 + limbs[2]*2^102 + limbs[3]*2^153 + limbs[4]*2^204`.
//!
//! No external dependencies. All functions are pure and value-passing.

/// Bitmask for 51-bit limbs.
pub const MASK51: u64 = (1u64 << 51) - 1;

/// a24 = 121665 (the constant (A-2)/4 for curve25519, where A = 486662).
/// See RFC 7748, Section 5.
const A24: u64 = 121665;

// --- Field element operations ---

/// The zero field element.
pub fn fe_zero() -> [u64; 5] {
    [0, 0, 0, 0, 0]
}

/// The one field element.
pub fn fe_one() -> [u64; 5] {
    [1, 0, 0, 0, 0]
}

/// Propagate carries across limbs, reducing mod p = 2^255 - 19.
/// After this, each limb is at most 51 bits.
pub fn fe_carry(a: [u64; 5]) -> [u64; 5] {
    let mut r = a;

    let mut carry: u64 = r[0] >> 51;
    r[0] &= MASK51;
    r[1] += carry;

    carry = r[1] >> 51;
    r[1] &= MASK51;
    r[2] += carry;

    carry = r[2] >> 51;
    r[2] &= MASK51;
    r[3] += carry;

    carry = r[3] >> 51;
    r[3] &= MASK51;
    r[4] += carry;

    carry = r[4] >> 51;
    r[4] &= MASK51;
    // 2^255 = 19 mod p, so top carry wraps with factor 19.
    r[0] += carry * 19;

    // One more pass for the possible carry from r[0].
    carry = r[0] >> 51;
    r[0] &= MASK51;
    r[1] += carry;

    r
}

/// Field addition with carry propagation.
pub fn fe_add(a: [u64; 5], b: [u64; 5]) -> [u64; 5] {
    fe_carry([
        a[0] + b[0],
        a[1] + b[1],
        a[2] + b[2],
        a[3] + b[3],
        a[4] + b[4],
    ])
}

/// Field subtraction with carry propagation.
///
/// We add 2*p as a bias before subtracting to keep values positive.
/// 2*p = 2*(2^255 - 19) in 51-bit limbs =
///   [2*(2^51-19), 2*(2^51-1), 2*(2^51-1), 2*(2^51-1), 2*(2^51-1)]
/// = [2^52 - 38,   2^52 - 2,   2^52 - 2,   2^52 - 2,   2^52 - 2]
pub fn fe_sub(a: [u64; 5], b: [u64; 5]) -> [u64; 5] {
    fe_carry([
        a[0] + 0xFFFFFFFFFFFDA - b[0], // + 2^52 - 38
        a[1] + 0xFFFFFFFFFFFFE - b[1], // + 2^52 - 2
        a[2] + 0xFFFFFFFFFFFFE - b[2],
        a[3] + 0xFFFFFFFFFFFFE - b[3],
        a[4] + 0xFFFFFFFFFFFFE - b[4],
    ])
}

/// Field multiplication using schoolbook with u128 intermediates.
///
/// Reduction uses 2^255 = 19 (mod p): when a product lands in limb >= 5,
/// it wraps to limb (i-5) with a factor of 19.
pub fn fe_mul(a: [u64; 5], b: [u64; 5]) -> [u64; 5] {
    let b1_19 = 19u128 * (b[1] as u128);
    let b2_19 = 19u128 * (b[2] as u128);
    let b3_19 = 19u128 * (b[3] as u128);
    let b4_19 = 19u128 * (b[4] as u128);

    let a0 = a[0] as u128;
    let a1 = a[1] as u128;
    let a2 = a[2] as u128;
    let a3 = a[3] as u128;
    let a4 = a[4] as u128;
    let b0 = b[0] as u128;
    let b1 = b[1] as u128;
    let b2 = b[2] as u128;
    let b3 = b[3] as u128;
    let b4 = b[4] as u128;

    let r0 = a0 * b0 + a1 * b4_19 + a2 * b3_19 + a3 * b2_19 + a4 * b1_19;
    let r1 = a0 * b1 + a1 * b0 + a2 * b4_19 + a3 * b3_19 + a4 * b2_19;
    let r2 = a0 * b2 + a1 * b1 + a2 * b0 + a3 * b4_19 + a4 * b3_19;
    let r3 = a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + a4 * b4_19;
    let r4 = a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0;

    // Carry propagation through u128 intermediates.
    let mut out = [0u64; 5];

    out[0] = (r0 as u64) & MASK51;
    let mut carry: u128 = r0 >> 51;

    let s1 = r1 + carry;
    out[1] = (s1 as u64) & MASK51;
    carry = s1 >> 51;

    let s2 = r2 + carry;
    out[2] = (s2 as u64) & MASK51;
    carry = s2 >> 51;

    let s3 = r3 + carry;
    out[3] = (s3 as u64) & MASK51;
    carry = s3 >> 51;

    let s4 = r4 + carry;
    out[4] = (s4 as u64) & MASK51;
    carry = s4 >> 51;

    // Top carry wraps with factor 19.
    out[0] += (carry as u64) * 19;
    let c = out[0] >> 51;
    out[0] &= MASK51;
    out[1] += c;

    out
}

/// Field squaring.
pub fn fe_sq(a: [u64; 5]) -> [u64; 5] {
    fe_mul(a, a)
}

/// Compute a^(2^n) by repeated squaring.
fn fe_sq_n(a: [u64; 5], n: u32) -> [u64; 5] {
    let mut r = a;
    let mut i = 0u32;
    while i < n {
        r = fe_sq(r);
        i += 1;
    }
    r
}

/// Field inversion: a^(p-2) mod p, using the standard addition chain
/// for the exponent 2^255 - 21.
pub fn fe_inv(a: [u64; 5]) -> [u64; 5] {
    // z2 = a^2
    let z2 = fe_sq(a);
    // t = a^8
    let t = fe_sq(fe_sq(z2));
    // z9 = a^9
    let z9 = fe_mul(a, t);
    // z11 = a^11
    let z11 = fe_mul(z2, z9);
    // t = a^22
    let t = fe_sq(z11);
    // z_5_0 = a^31 = a^(2^5 - 1)
    let z_5_0 = fe_mul(z9, t);

    let z_10_0 = fe_mul(fe_sq_n(z_5_0, 5), z_5_0);
    let z_20_0 = fe_mul(fe_sq_n(z_10_0, 10), z_10_0);
    let z_40_0 = fe_mul(fe_sq_n(z_20_0, 20), z_20_0);
    let z_50_0 = fe_mul(fe_sq_n(z_40_0, 10), z_10_0);
    let z_100_0 = fe_mul(fe_sq_n(z_50_0, 50), z_50_0);
    let z_200_0 = fe_mul(fe_sq_n(z_100_0, 100), z_100_0);
    let z_250_0 = fe_mul(fe_sq_n(z_200_0, 50), z_50_0);
    let z_255_5 = fe_sq_n(z_250_0, 5);
    fe_mul(z_255_5, z11)
}

/// Canonical reduction mod p = 2^255 - 19.
pub fn fe_reduce(a: [u64; 5]) -> [u64; 5] {
    let mut r = fe_carry(a);
    r = fe_carry(r);

    // Check if r >= p by testing whether r + 19 overflows 255 bits.
    let mut s = [0u64; 5];
    s[0] = r[0] + 19;
    let c0 = s[0] >> 51; s[0] &= MASK51;
    s[1] = r[1] + c0;
    let c1 = s[1] >> 51; s[1] &= MASK51;
    s[2] = r[2] + c1;
    let c2 = s[2] >> 51; s[2] &= MASK51;
    s[3] = r[3] + c2;
    let c3 = s[3] >> 51; s[3] &= MASK51;
    s[4] = r[4] + c3;
    let c4 = s[4] >> 51; s[4] &= MASK51;

    // If c4 == 1, r >= p, use s (= r - p). Otherwise keep r.
    let mask = (c4 as u64).wrapping_neg();
    [
        (s[0] & mask) | (r[0] & !mask),
        (s[1] & mask) | (r[1] & !mask),
        (s[2] & mask) | (r[2] & !mask),
        (s[3] & mask) | (r[3] & !mask),
        (s[4] & mask) | (r[4] & !mask),
    ]
}

/// Deserialise 32 bytes (little-endian) into a field element.
/// Clears bit 255 per RFC 7748.
pub fn fe_from_bytes(b: &[u8; 32]) -> [u64; 5] {
    let mut raw = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        raw[i] = b[i];
        i += 1;
    }
    raw[31] &= 127;

    let load8 = |buf: &[u8], off: usize| -> u64 {
        let mut v = 0u64;
        let mut j = 0;
        while j < 8 && off + j < buf.len() {
            v |= (buf[off + j] as u64) << (8 * j);
            j += 1;
        }
        v
    };

    [
        load8(&raw, 0) & MASK51,
        (load8(&raw, 6) >> 3) & MASK51,
        (load8(&raw, 12) >> 6) & MASK51,
        (load8(&raw, 19) >> 1) & MASK51,
        (load8(&raw, 24) >> 12) & MASK51,
    ]
}

/// Serialise a field element to 32 bytes (little-endian).
pub fn fe_to_bytes(a: [u64; 5]) -> [u8; 32] {
    let r = fe_reduce(a);

    let mut words = [0u64; 4];
    words[0] = r[0] | (r[1] << 51);
    words[1] = (r[1] >> 13) | (r[2] << 38);
    words[2] = (r[2] >> 26) | (r[3] << 25);
    words[3] = (r[3] >> 39) | (r[4] << 12);

    let mut val = [0u8; 32];
    let mut k = 0;
    while k < 4 {
        let b = words[k].to_le_bytes();
        let mut j = 0;
        while j < 8 {
            val[k * 8 + j] = b[j];
            j += 1;
        }
        k += 1;
    }
    val
}

// --- X25519 ---

/// Constant-time conditional swap. If swap == 1, exchange a and b.
pub fn cswap(swap: u64, a: [u64; 5], b: [u64; 5]) -> ([u64; 5], [u64; 5]) {
    let mask = swap.wrapping_neg();
    let mut ra = [0u64; 5];
    let mut rb = [0u64; 5];
    let mut i = 0;
    while i < 5 {
        let diff = mask & (a[i] ^ b[i]);
        ra[i] = a[i] ^ diff;
        rb[i] = b[i] ^ diff;
        i += 1;
    }
    (ra, rb)
}

/// Multiply a field element by the small constant 121666.
fn fe_mul_121666(a: [u64; 5]) -> [u64; 5] {
    let c = A24 as u128;
    let mut r = [0u64; 5];

    let mut t: u128 = (a[0] as u128) * c;
    r[0] = (t as u64) & MASK51;
    let mut carry: u128 = t >> 51;

    t = (a[1] as u128) * c + carry;
    r[1] = (t as u64) & MASK51;
    carry = t >> 51;

    t = (a[2] as u128) * c + carry;
    r[2] = (t as u64) & MASK51;
    carry = t >> 51;

    t = (a[3] as u128) * c + carry;
    r[3] = (t as u64) & MASK51;
    carry = t >> 51;

    t = (a[4] as u128) * c + carry;
    r[4] = (t as u64) & MASK51;
    carry = t >> 51;

    r[0] += (carry as u64) * 19;
    let c2 = r[0] >> 51;
    r[0] &= MASK51;
    r[1] += c2;

    r
}

/// X25519 scalar multiplication (RFC 7748).
///
/// Clamps the scalar, then performs a Montgomery ladder.
pub fn x25519_scalarmult(k: &[u8; 32], u: &[u8; 32]) -> [u8; 32] {
    let mut scalar = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        scalar[i] = k[i];
        i += 1;
    }
    scalar[0] &= 248;
    scalar[31] &= 127;
    scalar[31] |= 64;

    let x_1 = fe_from_bytes(u);
    let mut x_2 = fe_one();
    let mut z_2 = fe_zero();
    let mut x_3 = x_1;
    let mut z_3 = fe_one();

    let mut swap: u64 = 0;

    let mut pos: i32 = 254;
    while pos >= 0 {
        let byte_idx = (pos >> 3) as usize;
        let bit_idx = (pos & 7) as u32;
        let k_t = ((scalar[byte_idx] >> bit_idx) & 1) as u64;

        swap ^= k_t;
        let (a, b) = cswap(swap, x_2, x_3);
        x_2 = a; x_3 = b;
        let (a, b) = cswap(swap, z_2, z_3);
        z_2 = a; z_3 = b;
        swap = k_t;

        let aa = fe_add(x_2, z_2);
        let bb = fe_sub(x_2, z_2);
        let aa_sq = fe_sq(aa);
        let bb_sq = fe_sq(bb);
        let e = fe_sub(aa_sq, bb_sq);

        let cc = fe_add(x_3, z_3);
        let dd = fe_sub(x_3, z_3);
        let da = fe_mul(dd, aa);
        let cb = fe_mul(cc, bb);

        x_3 = fe_sq(fe_add(da, cb));
        z_3 = fe_mul(x_1, fe_sq(fe_sub(da, cb)));

        x_2 = fe_mul(aa_sq, bb_sq);
        z_2 = fe_mul(e, fe_add(aa_sq, fe_mul_121666(e)));

        pos -= 1;
    }

    let (a, _) = cswap(swap, x_2, x_3);
    x_2 = a;
    let (a, _) = cswap(swap, z_2, z_3);
    z_2 = a;

    let result = fe_mul(x_2, fe_inv(z_2));
    fe_to_bytes(result)
}

/// X25519 with the standard base point u = 9.
pub fn x25519_base(k: &[u8; 32]) -> [u8; 32] {
    let mut base = [0u8; 32];
    base[0] = 9;
    x25519_scalarmult(k, &base)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex_to_32(hex: &str) -> [u8; 32] {
        let mut out = [0u8; 32];
        let mut i = 0;
        while i < 32 {
            let hi = u8::from_str_radix(&hex[2 * i..2 * i + 1], 16).unwrap();
            let lo = u8::from_str_radix(&hex[2 * i + 1..2 * i + 2], 16).unwrap();
            out[i] = (hi << 4) | lo;
            i += 1;
        }
        out
    }

    /// RFC 7748, Section 6.1 -- Test Vector 1.
    #[test]
    fn test_rfc7748_vector1() {
        let scalar = hex_to_32(
            "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
        );
        let u_coord = hex_to_32(
            "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c",
        );
        let expected = hex_to_32(
            "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552",
        );
        assert_eq!(x25519_scalarmult(&scalar, &u_coord), expected);
    }

    /// RFC 7748, Section 6.1 -- Test Vector 2.
    #[test]
    fn test_rfc7748_vector2() {
        let scalar = hex_to_32(
            "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d",
        );
        let u_coord = hex_to_32(
            "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493",
        );
        let expected = hex_to_32(
            "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957",
        );
        assert_eq!(x25519_scalarmult(&scalar, &u_coord), expected);
    }

    /// RFC 7748, Section 5.2 -- one iteration with k = u = 9.
    #[test]
    fn test_base_mult() {
        let mut k = [0u8; 32];
        k[0] = 9;
        let mut u = [0u8; 32];
        u[0] = 9;
        let result = x25519_scalarmult(&k, &u);
        let expected = hex_to_32(
            "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079",
        );
        assert_eq!(result, expected);
    }

    /// Field element serialisation round-trip.
    #[test]
    fn test_fe_roundtrip() {
        let mut b = [0u8; 32];
        b[0] = 42;
        b[15] = 0xFF;
        let fe = fe_from_bytes(&b);
        let out = fe_to_bytes(fe);
        assert_eq!(out[0], 42);
        assert_eq!(out[15], 0xFF);
    }

    /// x25519_base is consistent with x25519_scalarmult(k, 9).
    #[test]
    fn test_base_consistency() {
        let scalar = hex_to_32(
            "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
        );
        let result = x25519_base(&scalar);
        let mut base = [0u8; 32];
        base[0] = 9;
        let expected = x25519_scalarmult(&scalar, &base);
        assert_eq!(result, expected);
    }
}
