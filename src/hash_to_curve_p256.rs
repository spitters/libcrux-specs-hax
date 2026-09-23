//! Pure Rust hash-to-curve specification for NIST P-256
//! (RFC 9380, Section 8.2).
//!
//! Suites:
//! - `P256_XMD:SHA-256_SSWU_RO_` (`hash_to_curve_p256`);
//! - `P256_XMD:SHA-256_SSWU_NU_` (`encode_to_curve_p256`).
//!
//! Both use the curve y^2 = x^3 + A * x + B with A = -3 and B the P-256
//! coefficient b, F = GF(p) with p = 2^256 - 2^224 + 2^192 + 2^96 - 1, m = 1,
//! L = 48, k = 128, expand_message = `expand_message_xmd` with SHA-256,
//! the Simplified SWU method with Z = -10, and h_eff = 1.
//!
//! - `h2c_p256_sgn0`, `h2c_p256_inv0`, `h2c_p256_select`: the functions sgn0,
//!   inv0 and CMOV of RFC 9380, Section 4 and Section 4.1.
//! - `sqrt_ratio_3mod4`: RFC 9380, Appendix F.2.1.2.
//! - `map_to_curve_simple_swu`: RFC 9380, Appendix F.2, the straight-line
//!   form of the Simplified SWU method of Section 6.6.2.
//! - `h2c_p256_point_add_complete`: the point addition of step 4 of
//!   `hash_to_curve`, by the complete formulas of Renes, Costello and Batina.
//! - `clear_cofactor_p256`: RFC 9380, Section 7, with h_eff = 1.
//! - `encode_to_curve_p256` / `hash_to_curve_p256`: RFC 9380, Section 3.
//!
//! Field arithmetic over GF(p) comes from `crate::p256` (`[u64; 4]`,
//! big-endian limb order, canonical representatives). `fp_inv` computes
//! a^(p - 2), which is the inv0 of RFC 9380, Section 4: it sends 0 to 0.
//!
//! Booleans of the straight-line programs are `u64` values in {0, 1}, and
//! CMOV(a, b, c) of RFC 9380, Section 4 is `h2c_p256_select(c, b, a)`. The
//! input of hash-to-curve can be secret (RFC 9380, Section 10.3), so every
//! function applied to the output of `hash_to_field` is a straight-line
//! program over the field operations of `crate::p256`: a value that depends
//! on the message reaches a result through `h2c_p256_select` and never
//! through a branch of this module. The only branch is the one of
//! `h2c_p256_pow_public`, on the bits of a public exponent.
//!
//! No external dependencies. All functions are pure and value-passing.

use crate::hash_to_field::hash_to_field_p256_sha256;
use crate::p256::{fp_add, fp_inv, fp_mul, fp_sq, fp_sub, P256FieldElement, P256Point, P256_B};

// --- Constants ---

/// The field element 0.
pub const H2C_P256_ZERO: P256FieldElement = [0, 0, 0, 0];

/// The field element 1.
pub const H2C_P256_ONE: P256FieldElement = [0, 0, 0, 1];

/// A = -3 = p - 3, the coefficient of x of the P-256 curve
/// (RFC 9380, Section 8.2).
///
/// A = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc
pub const H2C_P256_A: P256FieldElement = [
    0xFFFFFFFF00000001,
    0x0000000000000000,
    0x00000000FFFFFFFF,
    0xFFFFFFFFFFFFFFFC,
];

/// Z = -10 = p - 10, the constant of the Simplified SWU method for P-256
/// (RFC 9380, Section 8.2). Z is not a square in GF(p), Z is not -1, and
/// g(B / (Z * A)) is a square for g(x) = x^3 + A * x + B
/// (RFC 9380, Appendix H.2, criteria 1, 2 and 4).
///
/// Z = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffff5
pub const H2C_P256_Z: P256FieldElement = [
    0xFFFFFFFF00000001,
    0x0000000000000000,
    0x00000000FFFFFFFF,
    0xFFFFFFFFFFFFFFF5,
];

/// c1 = (q - 3) / 4, an integer (RFC 9380, Appendix F.2.1.2, constant 1),
/// for q = p. p = 3 mod 4, and 4 * c1 + 3 = p.
///
/// c1 = 0x3fffffffc00000004000000000000000000000003fffffffffffffffffffffff
///
/// The limbs are those of the integer in big-endian order; c1 is an exponent
/// and not a field element.
pub const H2C_P256_C1: [u64; 4] = [
    0x3FFFFFFFC0000000,
    0x4000000000000000,
    0x000000003FFFFFFF,
    0xFFFFFFFFFFFFFFFF,
];

/// c2 = sqrt(-Z) = sqrt(10) (RFC 9380, Appendix F.2.1.2, constant 2): the
/// square root with sgn0(c2) = 0.
///
/// c2 = 0x25ac71c31e27646736870398ae7f554d8472e008b3aa2a49d332cbd81bcc3b80
///
/// Both square roots of -Z give the same `map_to_curve_simple_swu`: c2 enters
/// only the sign of y, which step 24 of Appendix F.2 sets from sgn0(u).
pub const H2C_P256_C2: P256FieldElement = [
    0x25AC71C31E276467,
    0x36870398AE7F554D,
    0x8472E008B3AA2A49,
    0xD332CBD81BCC3B80,
];

// --- Field helpers (RFC 9380, Section 4) ---

/// 1 if the canonical field elements `a` and `b` are equal, 0 otherwise.
pub fn h2c_p256_ct_eq(a: P256FieldElement, b: P256FieldElement) -> u64 {
    let mut acc: u64 = 0;
    for i in 0..4 {
        acc |= a[i] ^ b[i];
    }
    // acc = 0 gives acc | -acc = 0, whose top bit is 0;
    // acc != 0 gives acc >= 2^63 or 2^64 - acc > 2^63, so the top bit is 1.
    1 - ((acc | acc.wrapping_neg()) >> 63)
}

/// 1 if the canonical field element `a` is zero, 0 otherwise.
pub fn h2c_p256_is_zero(a: P256FieldElement) -> u64 {
    h2c_p256_ct_eq(a, H2C_P256_ZERO)
}

/// `then_v` if `cond` is 1, `else_v` if `cond` is 0, by a mask.
/// CMOV(a, b, c) of RFC 9380, Section 4 is `h2c_p256_select(c, b, a)`.
pub fn h2c_p256_select(
    cond: u64,
    then_v: P256FieldElement,
    else_v: P256FieldElement,
) -> P256FieldElement {
    let mask = cond.wrapping_neg();
    let mut r = [0u64; 4];
    for i in 0..4 {
        r[i] = (then_v[i] & mask) | (else_v[i] & !mask);
    }
    r
}

/// -a in GF(p), as 0 - a. `fp_sub` sends (0, 0) to 0, so the result is
/// canonical for every canonical `a`.
pub fn h2c_p256_negate(a: P256FieldElement) -> P256FieldElement {
    fp_sub(H2C_P256_ZERO, a)
}

/// sgn0(x) for m = 1 (RFC 9380, Section 4.1): x mod 2, where x is the least
/// nonnegative integer representing the field element. `x` is canonical, so
/// this is the lowest bit of the least significant limb.
pub fn h2c_p256_sgn0(x: P256FieldElement) -> u64 {
    x[3] & 1
}

/// inv0(x) (RFC 9380, Section 4): the multiplicative inverse of x, extended
/// by inv0(0) = 0. It is x^(q - 2), which `fp_inv` computes.
pub fn h2c_p256_inv0(x: P256FieldElement) -> P256FieldElement {
    fp_inv(x)
}

/// a^e in GF(p) for a PUBLIC exponent `e`, a 256-bit integer in big-endian
/// limb order, by left-to-right square-and-multiply.
///
/// The loop branches on the bits of `e`. Every exponent this module passes
/// is a constant of the suite, so the branch does not depend on a secret;
/// `a` is only squared and multiplied. `e` must not be derived from a secret.
pub fn h2c_p256_pow_public(a: P256FieldElement, e: [u64; 4]) -> P256FieldElement {
    let mut r = H2C_P256_ONE;
    for i in 0..256 {
        r = fp_sq(r);
        let word_idx = i / 64;
        let bit_idx = (63 - (i % 64)) as u32;
        if (e[word_idx] >> bit_idx) & 1 == 1 {
            r = fp_mul(r, a);
        }
    }
    r
}

// --- Appendix F.2.1.2: sqrt_ratio for q = 3 mod 4 ---

/// `sqrt_ratio_3mod4(u, v)` (RFC 9380, Appendix F.2.1.2), for v != 0.
///
/// Returns `(b, y)` with b = 1 and y = sqrt(u / v) if u / v is a square in
/// GF(p), and b = 0 and y = sqrt(Z * (u / v)) otherwise.
///
/// The exponentiation of step 4 is `h2c_p256_pow_public` with the constant
/// exponent c1 = (p - 3) / 4.
pub fn sqrt_ratio_3mod4(u: P256FieldElement, v: P256FieldElement) -> (u64, P256FieldElement) {
    // Step 1: tv1 = v^2.
    let tv1 = fp_sq(v);
    // Step 2: tv2 = u * v.
    let tv2 = fp_mul(u, v);
    // Step 3: tv1 = tv1 * tv2.
    let tv1 = fp_mul(tv1, tv2);
    // Step 4: y1 = tv1^c1.
    let y1 = h2c_p256_pow_public(tv1, H2C_P256_C1);
    // Step 5: y1 = y1 * tv2.
    let y1 = fp_mul(y1, tv2);
    // Step 6: y2 = y1 * c2.
    let y2 = fp_mul(y1, H2C_P256_C2);
    // Step 7: tv3 = y1^2.
    let tv3 = fp_sq(y1);
    // Step 8: tv3 = tv3 * v.
    let tv3 = fp_mul(tv3, v);
    // Step 9: isQR = tv3 == u.
    let is_qr = h2c_p256_ct_eq(tv3, u);
    // Step 10: y = CMOV(y2, y1, isQR).
    let y = h2c_p256_select(is_qr, y1, y2);
    // Step 11.
    (is_qr, y)
}

// --- Appendix F.2: Simplified SWU ---

/// `map_to_curve_simple_swu(u)` (RFC 9380, Appendix F.2) for P-256:
/// A = -3, B = `P256_B`, Z = -10, and sqrt_ratio = `sqrt_ratio_3mod4`.
///
/// Returns the affine coordinates `(x, y)` of a point of the curve, both
/// canonical. The denominator tv4 of step 25 is nonzero for every u, and the
/// division is a multiplication by `h2c_p256_inv0(tv4)`.
pub fn map_to_curve_simple_swu(u: P256FieldElement) -> (P256FieldElement, P256FieldElement) {
    // Step 1: tv1 = u^2.
    let tv1 = fp_sq(u);
    // Step 2: tv1 = Z * tv1.
    let tv1 = fp_mul(H2C_P256_Z, tv1);
    // Step 3: tv2 = tv1^2.
    let tv2 = fp_sq(tv1);
    // Step 4: tv2 = tv2 + tv1.
    let tv2 = fp_add(tv2, tv1);
    // Step 5: tv3 = tv2 + 1.
    let tv3 = fp_add(tv2, H2C_P256_ONE);
    // Step 6: tv3 = B * tv3.
    let tv3 = fp_mul(P256_B, tv3);
    // Step 7: tv4 = CMOV(Z, -tv2, tv2 != 0).
    let tv4 = h2c_p256_select(h2c_p256_is_zero(tv2), H2C_P256_Z, h2c_p256_negate(tv2));
    // Step 8: tv4 = A * tv4.
    let tv4 = fp_mul(H2C_P256_A, tv4);
    // Step 9: tv2 = tv3^2.
    let tv2 = fp_sq(tv3);
    // Step 10: tv6 = tv4^2.
    let tv6 = fp_sq(tv4);
    // Step 11: tv5 = A * tv6.
    let tv5 = fp_mul(H2C_P256_A, tv6);
    // Step 12: tv2 = tv2 + tv5.
    let tv2 = fp_add(tv2, tv5);
    // Step 13: tv2 = tv2 * tv3.
    let tv2 = fp_mul(tv2, tv3);
    // Step 14: tv6 = tv6 * tv4.
    let tv6 = fp_mul(tv6, tv4);
    // Step 15: tv5 = B * tv6.
    let tv5 = fp_mul(P256_B, tv6);
    // Step 16: tv2 = tv2 + tv5.
    let tv2 = fp_add(tv2, tv5);
    // Step 17: x = tv1 * tv3.
    let x = fp_mul(tv1, tv3);
    // Step 18: (is_gx1_square, y1) = sqrt_ratio(tv2, tv6).
    let (is_gx1_square, y1) = sqrt_ratio_3mod4(tv2, tv6);
    // Step 19: y = tv1 * u.
    let y = fp_mul(tv1, u);
    // Step 20: y = y * y1.
    let y = fp_mul(y, y1);
    // Step 21: x = CMOV(x, tv3, is_gx1_square).
    let x = h2c_p256_select(is_gx1_square, tv3, x);
    // Step 22: y = CMOV(y, y1, is_gx1_square).
    let y = h2c_p256_select(is_gx1_square, y1, y);
    // Step 23: e1 = sgn0(u) == sgn0(y).
    let e1 = 1 ^ (h2c_p256_sgn0(u) ^ h2c_p256_sgn0(y));
    // Step 24: y = CMOV(-y, y, e1).
    let y = h2c_p256_select(e1, y, h2c_p256_negate(y));
    // Step 25: x = x / tv4.
    let x = fp_mul(x, h2c_p256_inv0(tv4));
    // Step 26.
    (x, y)
}

/// `map_to_curve(u)` for the P-256 suites, as a `P256Point` with Z = 1.
/// The Simplified SWU method never returns the point at infinity.
pub fn map_to_curve_p256(u: P256FieldElement) -> P256Point {
    let (x, y) = map_to_curve_simple_swu(u);
    P256Point {
        x,
        y,
        z: H2C_P256_ONE,
    }
}

// --- Point addition ---

/// P + Q on P-256 for Jacobian points, by the complete addition formulas of
/// Renes, Costello and Batina, "Complete addition formulas for prime order
/// elliptic curves" (EUROCRYPT 2016), Algorithm 4 (a = -3), in homogeneous
/// projective coordinates.
///
/// The formulas hold for every pair of points of the curve, including
/// P = Q, P = -Q and the point at infinity, so the function is a
/// straight-line program; `crate::p256::point_add` computes the same group
/// law with a case distinction on its arguments.
///
/// The Jacobian point (X, Y, Z) is the homogeneous point (X * Z, Y, Z^3), and
/// the homogeneous result (X3, Y3, Z3) is the Jacobian point
/// (X3 * Z3, Y3 * Z3^2, Z3). The point at infinity must have Y != 0 on input,
/// as in `crate::p256::point_identity`, and is returned as (0, 1, 0).
pub fn h2c_p256_point_add_complete(p: &P256Point, q: &P256Point) -> P256Point {
    let b = P256_B;
    // Jacobian to homogeneous coordinates.
    let x1 = fp_mul(p.x, p.z);
    let y1 = p.y;
    let z1 = fp_mul(fp_sq(p.z), p.z);
    let x2 = fp_mul(q.x, q.z);
    let y2 = q.y;
    let z2 = fp_mul(fp_sq(q.z), q.z);

    // Steps 1 to 3.
    let t0 = fp_mul(x1, x2);
    let t1 = fp_mul(y1, y2);
    let t2 = fp_mul(z1, z2);
    // Steps 4 to 6.
    let t3 = fp_add(x1, y1);
    let t4 = fp_add(x2, y2);
    let t3 = fp_mul(t3, t4);
    // Steps 7 to 9.
    let t4 = fp_add(t0, t1);
    let t3 = fp_sub(t3, t4);
    let t4 = fp_add(y1, z1);
    // Steps 10 to 12.
    let x3 = fp_add(y2, z2);
    let t4 = fp_mul(t4, x3);
    let x3 = fp_add(t1, t2);
    // Steps 13 to 15.
    let t4 = fp_sub(t4, x3);
    let x3 = fp_add(x1, z1);
    let y3 = fp_add(x2, z2);
    // Steps 16 to 18.
    let x3 = fp_mul(x3, y3);
    let y3 = fp_add(t0, t2);
    let y3 = fp_sub(x3, y3);
    // Steps 19 to 21.
    let z3 = fp_mul(b, t2);
    let x3 = fp_sub(y3, z3);
    let z3 = fp_add(x3, x3);
    // Steps 22 to 24.
    let x3 = fp_add(x3, z3);
    let z3 = fp_sub(t1, x3);
    let x3 = fp_add(t1, x3);
    // Steps 25 to 27.
    let y3 = fp_mul(b, y3);
    let t1 = fp_add(t2, t2);
    let t2 = fp_add(t1, t2);
    // Steps 28 to 30.
    let y3 = fp_sub(y3, t2);
    let y3 = fp_sub(y3, t0);
    let t1 = fp_add(y3, y3);
    // Steps 31 to 33.
    let y3 = fp_add(t1, y3);
    let t1 = fp_add(t0, t0);
    let t0 = fp_add(t1, t0);
    // Steps 34 to 36.
    let t0 = fp_sub(t0, t2);
    let t1 = fp_mul(t4, y3);
    let t2 = fp_mul(t0, y3);
    // Steps 37 to 39.
    let y3 = fp_mul(x3, z3);
    let y3 = fp_add(y3, t2);
    let x3 = fp_mul(t3, x3);
    // Steps 40 to 43.
    let x3 = fp_sub(x3, t1);
    let z3 = fp_mul(t4, z3);
    let t1 = fp_mul(t3, t0);
    let z3 = fp_add(z3, t1);

    // Homogeneous to Jacobian coordinates.
    let is_inf = h2c_p256_is_zero(z3);
    let xj = fp_mul(x3, z3);
    let yj = fp_mul(y3, fp_sq(z3));
    P256Point {
        x: xj,
        y: h2c_p256_select(is_inf, H2C_P256_ONE, yj),
        z: z3,
    }
}

// --- Section 7: clearing the cofactor ---

/// `clear_cofactor(P)` for P-256 (RFC 9380, Section 7): h_eff * P with
/// h_eff = 1, the identity map. P-256 has prime order.
pub fn clear_cofactor_p256(p: &P256Point) -> P256Point {
    P256Point {
        x: p.x,
        y: p.y,
        z: p.z,
    }
}

// --- Section 3: encoding byte strings to the curve ---

/// `encode_to_curve(msg)` of RFC 9380, Section 3, for the suite
/// `P256_XMD:SHA-256_SSWU_NU_` with domain separation tag `dst`.
///
/// Returns `None` exactly when `hash_to_field_p256_sha256(msg, dst, 1)`
/// does, that is when `len(dst) > 255`.
pub fn encode_to_curve_p256(msg: &[u8], dst: &[u8]) -> Option<P256Point> {
    // Step 1: u = hash_to_field(msg, 1).
    match hash_to_field_p256_sha256(msg, dst, 1) {
        None => None,
        Some(u) => {
            // Step 2: Q = map_to_curve(u[0]).
            let q = map_to_curve_p256(u[0]);
            // Step 3: P = clear_cofactor(Q).
            Some(clear_cofactor_p256(&q))
        }
    }
}

/// `hash_to_curve(msg)` of RFC 9380, Section 3, for the suite
/// `P256_XMD:SHA-256_SSWU_RO_` with domain separation tag `dst`.
///
/// The addition of step 4 is `h2c_p256_point_add_complete`; the result is a
/// Jacobian point, and it is the point at infinity when Q0 = -Q1.
///
/// Returns `None` exactly when `hash_to_field_p256_sha256(msg, dst, 2)`
/// does, that is when `len(dst) > 255`.
pub fn hash_to_curve_p256(msg: &[u8], dst: &[u8]) -> Option<P256Point> {
    // Step 1: u = hash_to_field(msg, 2).
    match hash_to_field_p256_sha256(msg, dst, 2) {
        None => None,
        Some(u) => {
            // Step 2: Q0 = map_to_curve(u[0]).
            let q0 = map_to_curve_p256(u[0]);
            // Step 3: Q1 = map_to_curve(u[1]).
            let q1 = map_to_curve_p256(u[1]);
            // Step 4: R = Q0 + Q1.
            let r = h2c_p256_point_add_complete(&q0, &q1);
            // Step 5: P = clear_cofactor(R).
            Some(clear_cofactor_p256(&r))
        }
    }
}
