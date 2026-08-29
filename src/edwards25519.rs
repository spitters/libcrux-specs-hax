//! Pure Rust Edwards25519 curve specification (RFC 8032).
//!
//! Curve: -x^2 + y^2 = 1 + d*x^2*y^2 over GF(2^255 - 19)
//! where d = -121665/121666 mod p.
//!
//! Uses extended coordinates (X, Y, Z, T) where x = X/Z, y = Y/Z, T = X*Y/Z.
//! Imports field arithmetic from `crate::curve25519`.
//!
//! No external dependencies. All functions are pure and value-passing.

use crate::curve25519::{
    fe_add, fe_from_bytes, fe_inv, fe_mul, fe_one, fe_reduce, fe_sq, fe_sub, fe_to_bytes,
    fe_zero,
};

/// A point on the Edwards25519 curve in extended coordinates.
#[derive(Clone, Copy, Debug)]
pub struct EdPoint {
    pub x: [u64; 5],
    pub y: [u64; 5],
    pub z: [u64; 5],
    pub t: [u64; 5],
}

/// The curve parameter d = -121665/121666 mod p.
///
/// d = 37095705934669439343138083508754565189542113879843219016388785533085940283555
///
/// In 51-bit limbs:
pub fn ed_d() -> [u64; 5] {
    // d as a byte string (little-endian), then convert via fe_from_bytes.
    // d = 0x52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3
    // In little-endian bytes:
    let d_bytes: [u8; 32] = [
        0xa3, 0x78, 0x59, 0x13, 0xca, 0x4d, 0xeb, 0x75,
        0xab, 0xd8, 0x41, 0x41, 0x4d, 0x0a, 0x70, 0x00,
        0x98, 0xe8, 0x79, 0x77, 0x79, 0x40, 0xc7, 0x8c,
        0x73, 0xfe, 0x6f, 0x2b, 0xee, 0x6c, 0x03, 0x52,
    ];
    fe_from_bytes(&d_bytes)
}

/// 2*d, precomputed for the addition formula.
pub fn ed_2d() -> [u64; 5] {
    let d = ed_d();
    fe_add(d, d)
}

/// The identity point (neutral element): (0, 1, 1, 0).
pub fn point_identity() -> EdPoint {
    EdPoint {
        x: fe_zero(),
        y: fe_one(),
        z: fe_one(),
        t: fe_zero(),
    }
}

/// The Edwards25519 base point B.
///
/// Bx = 15112221349535807912866137220509078750507884956996801397853916694561507378526
/// By = 46316835694926478169428394003475163141307993866256225615783033890098355573398
pub fn ed25519_base_point() -> EdPoint {
    // Bx in little-endian bytes:
    // 0x216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a
    let bx_bytes: [u8; 32] = [
        0x1a, 0xd5, 0x25, 0x8f, 0x60, 0x2d, 0x56, 0xc9,
        0xb2, 0xa7, 0x25, 0x95, 0x60, 0xc7, 0x2c, 0x69,
        0x5c, 0xdc, 0xd6, 0xfd, 0x31, 0xe2, 0xa4, 0xc0,
        0xfe, 0x53, 0x6e, 0xcd, 0xd3, 0x36, 0x69, 0x21,
    ];
    // By in little-endian bytes:
    // 0x6666666666666666666666666666666666666666666666666666666666666658
    let by_bytes: [u8; 32] = [
        0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    ];

    let x = fe_from_bytes(&bx_bytes);
    let y = fe_from_bytes(&by_bytes);
    let z = fe_one();
    let t = fe_mul(x, y);

    EdPoint { x, y, z, t }
}

/// Unified point addition for extended coordinates (RFC 8032 / EFD).
///
/// Input: P1 = (X1, Y1, Z1, T1), P2 = (X2, Y2, Z2, T2)
/// Output: P1 + P2 = (X3, Y3, Z3, T3)
///
/// Using the formula from Hisil et al. (2008):
///   A = (Y1 - X1) * (Y2 - X2)
///   B = (Y1 + X1) * (Y2 + X2)
///   C = T1 * 2*d * T2
///   D = Z1 * 2 * Z2
///   E = B - A
///   F = D - C
///   G = D + C
///   H = B + A
///   X3 = E * F
///   Y3 = G * H
///   T3 = E * H
///   Z3 = F * G
pub fn point_add(p1: &EdPoint, p2: &EdPoint) -> EdPoint {
    let two_d = ed_2d();

    let a = fe_mul(fe_sub(p1.y, p1.x), fe_sub(p2.y, p2.x));
    let b = fe_mul(fe_add(p1.y, p1.x), fe_add(p2.y, p2.x));
    let c = fe_mul(fe_mul(p1.t, two_d), p2.t);
    let d = fe_mul(fe_add(p1.z, p1.z), p2.z);

    let e = fe_sub(b, a);
    let f = fe_sub(d, c);
    let g = fe_add(d, c);
    let h = fe_add(b, a);

    let x3 = fe_mul(e, f);
    let y3 = fe_mul(g, h);
    let t3 = fe_mul(e, h);
    let z3 = fe_mul(f, g);

    EdPoint {
        x: x3,
        y: y3,
        z: z3,
        t: t3,
    }
}

/// Point doubling for extended coordinates (dbl-2008-hwcd with a = -1).
///
///   A = X1^2
///   B = Y1^2
///   C = 2 * Z1^2
///   D = a * A = -A  (since a = -1 for Ed25519)
///   E = (X1 + Y1)^2 - A - B
///   G = D + B
///   F = G - C
///   H = D - B
///   X3 = E * F
///   Y3 = G * H
///   T3 = E * H
///   Z3 = F * G
pub fn point_double(p: &EdPoint) -> EdPoint {
    let aa = fe_sq(p.x);        // A = X1^2
    let b = fe_sq(p.y);         // B = Y1^2
    let c = fe_add(fe_sq(p.z), fe_sq(p.z)); // C = 2 * Z1^2
    let d = fe_sub(fe_zero(), aa); // D = -A (since a = -1)
    let xy_sum = fe_add(p.x, p.y);
    let e = fe_sub(fe_sub(fe_sq(xy_sum), aa), b); // E = (X1+Y1)^2 - A - B
    let g = fe_add(d, b);       // G = D + B
    let f = fe_sub(g, c);       // F = G - C
    let h = fe_sub(d, b);       // H = D - B

    let x3 = fe_mul(e, f);
    let y3 = fe_mul(g, h);
    let t3 = fe_mul(e, h);
    let z3 = fe_mul(f, g);

    EdPoint {
        x: x3,
        y: y3,
        z: z3,
        t: t3,
    }
}

/// Scalar multiplication: scalar * point using double-and-add.
/// The scalar is a 256-bit little-endian byte string.
pub fn scalar_mult(scalar: &[u8; 32], point: &EdPoint) -> EdPoint {
    let mut result = point_identity();

    // Process from the most significant bit down to 0.
    let mut i: i32 = 255;
    while i >= 0 {
        result = point_double(&result);
        let byte_idx = (i / 8) as usize;
        let bit_idx = (i % 8) as u32;
        if (scalar[byte_idx] >> bit_idx) & 1 == 1 {
            result = point_add(&result, point);
        }
        i -= 1;
    }

    result
}

/// Encode a point to 32 bytes per RFC 8032.
///
/// The encoding is the y-coordinate (little-endian, 255 bits) with the
/// sign bit of x stored in the top bit (bit 255).
pub fn point_encode(p: &EdPoint) -> [u8; 32] {
    let z_inv = fe_inv(p.z);
    let x = fe_reduce(fe_mul(p.x, z_inv));
    let y = fe_mul(p.y, z_inv);

    let mut enc = fe_to_bytes(y);
    // Set the top bit to the low bit of x.
    let x_bytes = fe_to_bytes(x);
    enc[31] |= (x_bytes[0] & 1) << 7;

    enc
}

/// Decode a 32-byte encoding to a point per RFC 8032.
///
/// 1. Extract y from bits 0..254, the sign bit from bit 255.
/// 2. Compute x^2 = (y^2 - 1) / (d*y^2 + 1) mod p.
/// 3. Compute x = sqrt(x^2) using x = (x^2)^((p+3)/8) mod p.
/// 4. Adjust sign of x.
///
/// Returns None if the encoding is invalid (no square root exists).
pub fn point_decode(bytes: &[u8; 32]) -> Option<EdPoint> {
    // Extract sign bit.
    let x_sign = (bytes[31] >> 7) & 1;

    // Extract y (clear top bit).
    let mut y_bytes = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        y_bytes[i] = bytes[i];
        i += 1;
    }
    y_bytes[31] &= 0x7F;

    let y = fe_from_bytes(&y_bytes);
    let y_sq = fe_sq(y);
    let d = ed_d();

    // u = y^2 - 1
    let u = fe_sub(y_sq, fe_one());
    // v = d*y^2 + 1
    let v = fe_add(fe_mul(d, y_sq), fe_one());

    // x^2 = u * v^(-1)  (but we use the sqrt formula instead)
    // x = u * v^3 * (u * v^7)^((p-5)/8)
    let v_sq = fe_sq(v);
    let v_cu = fe_mul(v_sq, v);
    let v4 = fe_sq(v_sq);
    let v7 = fe_mul(v4, v_cu);
    let uv7 = fe_mul(u, v7);

    // (p-5)/8 = (2^255 - 19 - 5)/8 = (2^255 - 24)/8 = 2^252 - 3
    let exp = pow252m3(uv7);
    let mut x = fe_mul(fe_mul(u, v_cu), exp);

    // Check: v * x^2 == u ?
    let vx_sq = fe_mul(v, fe_sq(x));
    let check = fe_reduce(fe_sub(vx_sq, u));
    let check_neg = fe_reduce(fe_sub(vx_sq, fe_sub(fe_zero(), u)));

    // sqrt(-1) = 2^((p-1)/4) mod p
    let sqrt_m1 = fe_from_bytes(&[
        0xb0, 0xa0, 0x0e, 0x4a, 0x27, 0x1b, 0xee, 0xc4,
        0x78, 0xe4, 0x2f, 0xad, 0x06, 0x18, 0x43, 0x2f,
        0xa7, 0xd7, 0xfb, 0x3d, 0x99, 0x00, 0x4d, 0x2b,
        0x0b, 0xdf, 0xc1, 0x4f, 0x80, 0x24, 0x83, 0x2b,
    ]);

    let is_zero = |a: [u64; 5]| -> bool {
        let r = fe_reduce(a);
        r[0] == 0 && r[1] == 0 && r[2] == 0 && r[3] == 0 && r[4] == 0
    };

    if is_zero(check) {
        // x is correct
    } else if is_zero(check_neg) {
        // x = x * sqrt(-1)
        x = fe_mul(x, sqrt_m1);
    } else {
        return None; // no square root
    }

    // Adjust sign.
    let x_reduced = fe_reduce(x);
    let x_bytes = fe_to_bytes(x_reduced);
    let x_low_bit = x_bytes[0] & 1;
    if x_low_bit != x_sign {
        x = fe_sub(fe_zero(), x);
    }

    // Check that x is not zero when the sign bit is 1.
    let x_red = fe_reduce(x);
    if x_sign == 1 && is_zero(x_red) {
        return None;
    }

    let z = fe_one();
    let t = fe_mul(x, y);

    Some(EdPoint { x, y, z, t })
}

/// Compute a^((p-5)/8) = a^(2^252 - 3) using a standard addition chain.
fn pow252m3(z: [u64; 5]) -> [u64; 5] {
    // z^1
    let z1 = z;
    // z^2
    let z2 = fe_sq(z1);
    // z^(2^2) = z^4
    let t = fe_sq(z2);
    // z^(2^3) = z^8
    let t = fe_sq(t);
    // z^9
    let z9 = fe_mul(t, z1);
    // z^11
    let z11 = fe_mul(z9, z2);
    // z^22
    let t = fe_sq(z11);
    // z^(2^5 - 2^0) = z^31
    let z_5_0 = fe_mul(t, z9);

    // z^(2^10 - 2^5)
    let z_10_5 = fe_sq_n(z_5_0, 5);
    // z^(2^10 - 2^0)
    let z_10_0 = fe_mul(z_10_5, z_5_0);

    // z^(2^20 - 2^10)
    let z_20_10 = fe_sq_n(z_10_0, 10);
    // z^(2^20 - 2^0)
    let z_20_0 = fe_mul(z_20_10, z_10_0);

    // z^(2^40 - 2^20)
    let z_40_20 = fe_sq_n(z_20_0, 20);
    // z^(2^40 - 2^0)
    let z_40_0 = fe_mul(z_40_20, z_20_0);

    // z^(2^50 - 2^10)
    let z_50_10 = fe_sq_n(z_40_0, 10);
    // z^(2^50 - 2^0)
    let z_50_0 = fe_mul(z_50_10, z_10_0);

    // z^(2^100 - 2^50)
    let z_100_50 = fe_sq_n(z_50_0, 50);
    // z^(2^100 - 2^0)
    let z_100_0 = fe_mul(z_100_50, z_50_0);

    // z^(2^200 - 2^100)
    let z_200_100 = fe_sq_n(z_100_0, 100);
    // z^(2^200 - 2^0)
    let z_200_0 = fe_mul(z_200_100, z_100_0);

    // z^(2^250 - 2^50)
    let z_250_50 = fe_sq_n(z_200_0, 50);
    // z^(2^250 - 2^0)
    let z_250_0 = fe_mul(z_250_50, z_50_0);

    // z^(2^252 - 2^2)
    let z_252_2 = fe_sq_n(z_250_0, 2);
    // z^(2^252 - 3)
    let z_252_3 = fe_mul(z_252_2, z1);

    z_252_3
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

/// Reduce a 512-bit little-endian scalar mod L, where
/// L = 2^252 + 27742317777372353535851937790883648493.
///
/// Input: 64-byte little-endian integer.
/// Output: 32-byte little-endian integer in [0, L).
pub fn scalar_reduce(s: &[u8; 64]) -> [u8; 32] {
    // L = 2^252 + 27742317777372353535851937790883648493
    // L in little-endian bytes:
    // 0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
    // 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    // 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    // 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10

    // For Barrett reduction of a 512-bit number mod a 253-bit modulus,
    // we use a simple schoolbook approach since this is a spec.
    // We work with a big-integer representation.

    // Convert 64-byte little-endian to 512-bit number.
    // We do long division bit by bit.

    // L as 32 bytes (little-endian):
    let l_bytes: [u8; 32] = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
        0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
    ];

    // Use a simple approach: interpret s as a number and reduce mod L.
    // We represent the accumulator as [u64; 5] (320 bits, enough for 253-bit L).
    // Process the input from MSB to LSB.

    // Actually, let's just use a big array of u64 and do schoolbook reduction.
    // Convert s to a [u64; 8] little-endian representation.
    let mut s_words = [0u64; 8];
    let mut i = 0;
    while i < 8 {
        let base = i * 8;
        let mut w = 0u64;
        let mut j = 0;
        while j < 8 {
            w |= (s[base + j] as u64) << (8 * j);
            j += 1;
        }
        s_words[i] = w;
        i += 1;
    }

    // Convert L to [u64; 4] little-endian.
    let mut l_words = [0u64; 4];
    i = 0;
    while i < 4 {
        let base = i * 8;
        let mut w = 0u64;
        let mut j = 0;
        while j < 8 {
            w |= (l_bytes[base + j] as u64) << (8 * j);
            j += 1;
        }
        l_words[i] = w;
        i += 1;
    }

    // Simple reduction: accumulator, process each bit from MSB.
    // We use a 4-word (256-bit) accumulator and process 512 bits.
    let mut acc = [0u64; 5]; // extra word for overflow

    let mut bit: i32 = 511;
    while bit >= 0 {
        // Shift acc left by 1.
        let mut carry: u64 = 0;
        let mut k = 0;
        while k < 5 {
            let new_carry = acc[k] >> 63;
            acc[k] = (acc[k] << 1) | carry;
            carry = new_carry;
            k += 1;
        }

        // Add current bit of s.
        let word_idx = (bit / 64) as usize;
        let bit_idx = (bit % 64) as u32;
        let b = (s_words[word_idx] >> bit_idx) & 1;
        acc[0] = acc[0].wrapping_add(b);
        if acc[0] < b {
            acc[1] = acc[1].wrapping_add(1);
        }

        // If acc >= L, subtract L.
        if ge_l(&acc, &l_words) {
            sub_l(&mut acc, &l_words);
        }

        bit -= 1;
    }

    // Convert acc[0..4] to 32 bytes little-endian.
    let mut result = [0u8; 32];
    i = 0;
    while i < 4 {
        let bytes = acc[i].to_le_bytes();
        let mut j = 0;
        while j < 8 {
            result[i * 8 + j] = bytes[j];
            j += 1;
        }
        i += 1;
    }

    result
}

/// Check if acc >= L (acc is 5 words, L is 4 words, both little-endian).
fn ge_l(acc: &[u64; 5], l: &[u64; 4]) -> bool {
    // If acc[4] > 0, definitely >=.
    if acc[4] > 0 {
        return true;
    }
    // Compare acc[3..0] with l[3..0] from MSW.
    let mut i: usize = 4;
    while i > 0 {
        i -= 1;
        if acc[i] > l[i] {
            return true;
        }
        if acc[i] < l[i] {
            return false;
        }
    }
    true // equal
}

/// Subtract L from acc (acc -= L). acc is 5 words, L is 4 words (little-endian).
fn sub_l(acc: &mut [u64; 5], l: &[u64; 4]) {
    let mut borrow: u64 = 0;
    let mut i = 0;
    while i < 4 {
        let (r, b1) = acc[i].overflowing_sub(l[i]);
        let (r2, b2) = r.overflowing_sub(borrow);
        acc[i] = r2;
        borrow = (b1 as u64) + (b2 as u64);
        i += 1;
    }
    acc[4] = acc[4].wrapping_sub(borrow);
}

/// Scalar addition mod L. Both inputs and output are 32-byte little-endian.
pub fn scalar_add(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    // Add a + b as 256-bit integers, then reduce mod L.
    let mut sum = [0u8; 64];
    let mut carry: u16 = 0;
    let mut i = 0;
    while i < 32 {
        let s = (a[i] as u16) + (b[i] as u16) + carry;
        sum[i] = s as u8;
        carry = s >> 8;
        i += 1;
    }
    if carry > 0 {
        sum[32] = carry as u8;
    }
    scalar_reduce(&sum)
}

/// Scalar multiplication mod L (schoolbook). Both inputs are 32-byte LE.
pub fn scalar_mul_mod_l(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    // Schoolbook multiplication producing a 64-byte result, then reduce.
    // Use u32 accumulators since u16 overflows with 32 accumulated products.
    let mut product = [0u32; 64];
    let mut i = 0;
    while i < 32 {
        let mut j = 0;
        while j < 32 {
            product[i + j] += (a[i] as u32) * (b[j] as u32);
            j += 1;
        }
        i += 1;
    }

    // Propagate carries.
    let mut result = [0u8; 64];
    let mut carry: u32 = 0;
    i = 0;
    while i < 64 {
        let s = product[i] + carry;
        result[i] = s as u8;
        carry = s >> 8;
        i += 1;
    }

    scalar_reduce(&result)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The encoding of the base point B should be the known value.
    /// Expected: 5866666666666666666666666666666666666666666666666666666666666666 (hex)
    #[test]
    fn test_base_point_encoding() {
        let b = ed25519_base_point();
        let enc = point_encode(&b);
        let expected: [u8; 32] = [
            0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
            0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
            0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
            0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        ];
        assert_eq!(enc, expected);
    }

    /// Decode then re-encode the base point.
    #[test]
    fn test_decode_encode_roundtrip() {
        let enc: [u8; 32] = [
            0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
            0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
            0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
            0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        ];
        let p = point_decode(&enc).expect("decode should succeed");
        let re_enc = point_encode(&p);
        assert_eq!(re_enc, enc);
    }

    /// Verify that identity + B = B.
    #[test]
    fn test_add_identity() {
        let id = point_identity();
        let b = ed25519_base_point();
        let sum = point_add(&id, &b);
        let enc_sum = point_encode(&sum);
        let enc_b = point_encode(&b);
        assert_eq!(enc_sum, enc_b);
    }

    /// Verify that B + B == 2*B (doubling via addition equals point_double).
    #[test]
    fn test_double_equals_add() {
        let b = ed25519_base_point();
        let sum = point_add(&b, &b);
        let dbl = point_double(&b);
        let enc_sum = point_encode(&sum);
        let enc_dbl = point_encode(&dbl);
        assert_eq!(enc_sum, enc_dbl);
    }

    /// Scalar multiplication by 1 should give the base point.
    #[test]
    fn test_scalar_mult_by_one() {
        let mut scalar = [0u8; 32];
        scalar[0] = 1;
        let b = ed25519_base_point();
        let result = scalar_mult(&scalar, &b);
        let enc_result = point_encode(&result);
        let enc_b = point_encode(&b);
        assert_eq!(enc_result, enc_b);
    }

    /// Test scalar_reduce with a known value.
    /// L itself should reduce to 0.
    #[test]
    fn test_scalar_reduce_l() {
        let mut l_64 = [0u8; 64];
        let l_bytes: [u8; 32] = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
            0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
        ];
        let mut i = 0;
        while i < 32 {
            l_64[i] = l_bytes[i];
            i += 1;
        }
        let result = scalar_reduce(&l_64);
        assert_eq!(result, [0u8; 32]);
    }
}
