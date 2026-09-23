//! Pure Rust ristretto255 prime-order group specification (RFC 9496, Section 4).
//!
//! A group element is represented internally by a point of edwards25519 in
//! extended coordinates (`EdPoint`, with x = X/Z, y = Y/Z, T = X*Y/Z). Several
//! internal representations stand for the same group element; they are
//! compared only with `equals` and serialised only with `encode`.
//!
//! Field arithmetic over GF(2^255 - 19) comes from `crate::curve25519`
//! (radix 2^51, `[u64; 5]`); the curve operations come from
//! `crate::edwards25519`.
//!
//! Booleans produced by the constant-time operations of RFC 9496,
//! Section 2.2 are `u64` values in {0, 1}. `decode` and `equals` convert
//! them to `Option` / `bool` at the API boundary.
//!
//! No external dependencies. All functions are pure and value-passing.
//!
//! The function layout (`sqrt_ratio_m1`, the map, `encode`, `decode`,
//! `equals`, `add`, `neg`, `sub`, `double`, `mul`) follows the hacspec
//! ristretto specification, <https://github.com/hacspec/specs>
//! (`ristretto/src/ristretto.rs`, Apache-2.0), which transcribes
//! draft-irtf-cfrg-ristretto255-00. Every function body here transcribes the
//! pseudocode of RFC 9496.

use crate::secret::Scalar;
use crate::curve25519::{
    fe_add, fe_from_bytes, fe_mul, fe_one, fe_sq, fe_sub, fe_to_bytes, fe_zero,
};
use crate::edwards25519::{
    ed25519_base_point, ed_d, point_add, point_double, point_identity, scalar_mult, EdPoint,
};

// --- Implementation constants (RFC 9496, Section 4.1) ---

/// D, the Edwards d parameter of Curve25519 (RFC 9496, Section 4.1).
///
/// D = 37095705934669439343138083508754565189542113879843219016388785533085940283555
pub fn d() -> [u64; 5] {
    ed_d()
}

/// SQRT_M1, a square root of -1 (RFC 9496, Section 4.1).
///
/// SQRT_M1 = 19681161376707505956807079304988542015446066515923890162744021073123829784752
///         = 0x2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0
pub fn sqrt_m1() -> [u64; 5] {
    let bytes: [u8; 32] = [
        0xb0, 0xa0, 0x0e, 0x4a, 0x27, 0x1b, 0xee, 0xc4,
        0x78, 0xe4, 0x2f, 0xad, 0x06, 0x18, 0x43, 0x2f,
        0xa7, 0xd7, 0xfb, 0x3d, 0x99, 0x00, 0x4d, 0x2b,
        0x0b, 0xdf, 0xc1, 0x4f, 0x80, 0x24, 0x83, 0x2b,
    ];
    fe_from_bytes(&bytes)
}

/// SQRT_AD_MINUS_ONE, a square root of a*d - 1 with a = -1 (RFC 9496, Section 4.1).
///
/// SQRT_AD_MINUS_ONE = 25063068953384623474111414158702152701244531502492656460079210482610430750235
///                   = 0x376931bf2b8348ac0f3cfcc931f5d1fdaf9d8e0c1b7854bd7e97f6a0497b2e1b
pub fn sqrt_ad_minus_one() -> [u64; 5] {
    let bytes: [u8; 32] = [
        0x1b, 0x2e, 0x7b, 0x49, 0xa0, 0xf6, 0x97, 0x7e,
        0xbd, 0x54, 0x78, 0x1b, 0x0c, 0x8e, 0x9d, 0xaf,
        0xfd, 0xd1, 0xf5, 0x31, 0xc9, 0xfc, 0x3c, 0x0f,
        0xac, 0x48, 0x83, 0x2b, 0xbf, 0x31, 0x69, 0x37,
    ];
    fe_from_bytes(&bytes)
}

/// INVSQRT_A_MINUS_D, an inverse square root of a - d with a = -1
/// (RFC 9496, Section 4.1).
///
/// INVSQRT_A_MINUS_D = 54469307008909316920995813868745141605393597292927456921205312896311721017578
///                   = 0x786c8905cfaffca216c27b91fe01d8409d2f16175a4172be99c8fdaa805d40ea
pub fn invsqrt_a_minus_d() -> [u64; 5] {
    let bytes: [u8; 32] = [
        0xea, 0x40, 0x5d, 0x80, 0xaa, 0xfd, 0xc8, 0x99,
        0xbe, 0x72, 0x41, 0x5a, 0x17, 0x16, 0x2f, 0x9d,
        0x40, 0xd8, 0x01, 0xfe, 0x91, 0x7b, 0xc2, 0x16,
        0xa2, 0xfc, 0xaf, 0xcf, 0x05, 0x89, 0x6c, 0x78,
    ];
    fe_from_bytes(&bytes)
}

/// ONE_MINUS_D_SQ = 1 - d^2 (RFC 9496, Section 4.1).
///
/// ONE_MINUS_D_SQ = 1159843021668779879193775521855586647937357759715417654439879720876111806838
///                = 0x029072a8b2b3e0d79994abddbe70dfe42c81a138cd5e350fe27c09c1945fc176
pub fn one_minus_d_sq() -> [u64; 5] {
    let bytes: [u8; 32] = [
        0x76, 0xc1, 0x5f, 0x94, 0xc1, 0x09, 0x7c, 0xe2,
        0x0f, 0x35, 0x5e, 0xcd, 0x38, 0xa1, 0x81, 0x2c,
        0xe4, 0xdf, 0x70, 0xbe, 0xdd, 0xab, 0x94, 0x99,
        0xd7, 0xe0, 0xb3, 0xb2, 0xa8, 0x72, 0x90, 0x02,
    ];
    fe_from_bytes(&bytes)
}

/// D_MINUS_ONE_SQ = (d - 1)^2 (RFC 9496, Section 4.1).
///
/// D_MINUS_ONE_SQ = 40440834346308536858101042469323190826248399146238708352240133220865137265952
///                = 0x5968b37af66c22414cdcd32f529b4eebd29e4a2cb01e199931ad5aaa44ed4d20
pub fn d_minus_one_sq() -> [u64; 5] {
    let bytes: [u8; 32] = [
        0x20, 0x4d, 0xed, 0x44, 0xaa, 0x5a, 0xad, 0x31,
        0x99, 0x19, 0x1e, 0xb0, 0x2c, 0x4a, 0x9e, 0xd2,
        0xeb, 0x4e, 0x9b, 0x52, 0x2f, 0xd3, 0xdc, 0x4c,
        0x41, 0x22, 0x6c, 0xf6, 0x7a, 0xb3, 0x68, 0x59,
    ];
    fe_from_bytes(&bytes)
}

// --- Field helpers (RFC 9496, Sections 2.1 and 2.2) ---

/// Field negation: -a mod p.
pub fn fe_neg(a: [u64; 5]) -> [u64; 5] {
    fe_sub(fe_zero(), a)
}

/// IS_NEGATIVE (RFC 9496, Section 2.1): 1 if the least nonnegative integer
/// representing `a` is odd, 0 if it is even.
pub fn fe_is_negative(a: [u64; 5]) -> u64 {
    let bytes = fe_to_bytes(a);
    (bytes[0] & 1) as u64
}

/// CT_EQ (RFC 9496, Section 2.2): 1 if a = b in the field, 0 otherwise.
///
/// Compares the canonical 32-byte encodings without branching.
pub fn fe_ct_eq(a: [u64; 5], b: [u64; 5]) -> u64 {
    let a_bytes = fe_to_bytes(a);
    let b_bytes = fe_to_bytes(b);
    let mut acc: u8 = 0;
    for i in 0..32 {
        acc |= a_bytes[i] ^ b_bytes[i];
    }
    // acc = 0 gives 0 - 1 = 2^64 - 1, whose top bit is 1;
    // 1 <= acc <= 255 gives acc - 1 < 2^63, whose top bit is 0.
    (acc as u64).wrapping_sub(1) >> 63
}

/// 1 if `a` is zero in the field, 0 otherwise.
pub fn fe_is_zero(a: [u64; 5]) -> u64 {
    fe_ct_eq(a, fe_zero())
}

/// CT_SELECT (RFC 9496, Section 2.2): `then_v` if `cond` is 1, `else_v` if
/// `cond` is 0. Reads `CT_SELECT(then_v IF cond ELSE else_v)`.
pub fn fe_select(cond: u64, then_v: [u64; 5], else_v: [u64; 5]) -> [u64; 5] {
    let mask = cond.wrapping_neg();
    let mut r = [0u64; 5];
    for i in 0..5 {
        r[i] = (then_v[i] & mask) | (else_v[i] & !mask);
    }
    r
}

/// CT_ABS (RFC 9496, Section 2.2): -a if IS_NEGATIVE(a), else a.
pub fn fe_abs(a: [u64; 5]) -> [u64; 5] {
    fe_select(fe_is_negative(a), fe_neg(a), a)
}

/// Compute a^(2^n) by n squarings.
fn fe_sq_n(a: [u64; 5], n: usize) -> [u64; 5] {
    let mut r = a;
    for _i in 0..n {
        r = fe_sq(r);
    }
    r
}

/// Compute z^((p-5)/8) = z^(2^252 - 3), the exponent of RFC 9496,
/// Section 4.2, by a fixed addition chain.
pub fn fe_pow22523(z: [u64; 5]) -> [u64; 5] {
    // z^2
    let z2 = fe_sq(z);
    // z^8
    let z8 = fe_sq_n(z2, 2);
    // z^9
    let z9 = fe_mul(z8, z);
    // z^11
    let z11 = fe_mul(z9, z2);
    // z^22
    let z22 = fe_sq(z11);
    // z^(2^5 - 1)
    let z_5_0 = fe_mul(z22, z9);
    // z^(2^10 - 1)
    let z_10_0 = fe_mul(fe_sq_n(z_5_0, 5), z_5_0);
    // z^(2^20 - 1)
    let z_20_0 = fe_mul(fe_sq_n(z_10_0, 10), z_10_0);
    // z^(2^40 - 1)
    let z_40_0 = fe_mul(fe_sq_n(z_20_0, 20), z_20_0);
    // z^(2^50 - 1)
    let z_50_0 = fe_mul(fe_sq_n(z_40_0, 10), z_10_0);
    // z^(2^100 - 1)
    let z_100_0 = fe_mul(fe_sq_n(z_50_0, 50), z_50_0);
    // z^(2^200 - 1)
    let z_200_0 = fe_mul(fe_sq_n(z_100_0, 100), z_100_0);
    // z^(2^250 - 1)
    let z_250_0 = fe_mul(fe_sq_n(z_200_0, 50), z_50_0);
    // z^(2^252 - 4)
    let z_252_2 = fe_sq_n(z_250_0, 2);
    // z^(2^252 - 3)
    fe_mul(z_252_2, z)
}

// --- Square root of a ratio of field elements (RFC 9496, Section 4.2) ---

/// SQRT_RATIO_M1(u, v) (RFC 9496, Section 4.2).
///
/// Returns `(was_square, r)` with `was_square` in {0, 1}:
///   * (1, +sqrt(u/v)) if u and v are nonzero and u/v is square;
///   * (1, 0) if u is zero;
///   * (0, 0) if v is zero and u is nonzero;
///   * (0, +sqrt(SQRT_M1 * (u/v))) if u and v are nonzero and u/v is non-square.
///
/// Here +sqrt denotes the nonnegative square root.
pub fn sqrt_ratio_m1(u: [u64; 5], v: [u64; 5]) -> (u64, [u64; 5]) {
    let v2 = fe_sq(v);
    let v3 = fe_mul(v2, v);
    let v7 = fe_mul(fe_sq(v3), v);

    // r = (u * v^3) * (u * v^7)^((p-5)/8)
    let r = fe_mul(fe_mul(u, v3), fe_pow22523(fe_mul(u, v7)));
    // check = v * r^2
    let check = fe_mul(v, fe_sq(r));

    let neg_u = fe_neg(u);
    let correct_sign_sqrt = fe_ct_eq(check, u);
    let flipped_sign_sqrt = fe_ct_eq(check, neg_u);
    let flipped_sign_sqrt_i = fe_ct_eq(check, fe_mul(neg_u, sqrt_m1()));

    let r_prime = fe_mul(sqrt_m1(), r);
    let r = fe_select(flipped_sign_sqrt | flipped_sign_sqrt_i, r_prime, r);

    // Choose the nonnegative square root.
    let r = fe_abs(r);

    let was_square = correct_sign_sqrt | flipped_sign_sqrt;

    (was_square, r)
}

// --- Group operations (RFC 9496, Section 4.3) ---

/// Decode (RFC 9496, Section 4.3.1).
///
/// Returns `None` when the string is not the canonical encoding of a field
/// element, when s is negative, when the ratio is not a square, when t is
/// negative, or when y = 0. Otherwise returns the internal representation
/// (x, y, 1, t).
pub fn decode(bytes: &[u8; 32]) -> Option<EdPoint> {
    // Step 1: s as a field element; the encoding is canonical exactly when
    // re-encoding s gives the input back. `fe_from_bytes` drops bit 255 and
    // accepts values >= p, and `fe_to_bytes` writes the canonical value
    // below p, so an input with bit 255 set or with value >= p differs from
    // its re-encoding.
    let s = fe_from_bytes(bytes);
    let s_bytes = fe_to_bytes(s);
    let mut diff: u8 = 0;
    for i in 0..32 {
        diff |= s_bytes[i] ^ bytes[i];
    }
    let canonical = (diff as u64).wrapping_sub(1) >> 63;

    // Step 2.
    let s_negative = fe_is_negative(s);

    // Step 3.
    let one = fe_one();
    let ss = fe_sq(s);
    let u1 = fe_sub(one, ss);
    let u2 = fe_add(one, ss);
    let u2_sqr = fe_sq(u2);

    // v = -(D * u1^2) - u2_sqr
    let v = fe_sub(fe_neg(fe_mul(d(), fe_sq(u1))), u2_sqr);

    let (was_square, invsqrt) = sqrt_ratio_m1(one, fe_mul(v, u2_sqr));

    let den_x = fe_mul(invsqrt, u2);
    let den_y = fe_mul(fe_mul(invsqrt, den_x), v);

    // x = CT_ABS(2 * s * den_x)
    let x = fe_abs(fe_mul(fe_add(s, s), den_x));
    let y = fe_mul(u1, den_y);
    let t = fe_mul(x, y);

    // Step 4.
    let t_negative = fe_is_negative(t);
    let y_zero = fe_is_zero(y);
    let ok = canonical & (1 - s_negative) & was_square & (1 - t_negative) & (1 - y_zero);

    if ok == 1 {
        Some(EdPoint { x, y, z: one, t })
    } else {
        None
    }
}

/// Encode (RFC 9496, Section 4.3.2): the canonical 32-byte encoding of the
/// group element with internal representation (x0, y0, z0, t0).
pub fn encode(p: &EdPoint) -> [u8; 32] {
    let x0 = p.x;
    let y0 = p.y;
    let z0 = p.z;
    let t0 = p.t;

    let u1 = fe_mul(fe_add(z0, y0), fe_sub(z0, y0));
    let u2 = fe_mul(x0, y0);

    // The ratio is always square, so was_square is not used.
    let (_was_square, invsqrt) = sqrt_ratio_m1(fe_one(), fe_mul(u1, fe_sq(u2)));

    let den1 = fe_mul(invsqrt, u1);
    let den2 = fe_mul(invsqrt, u2);
    let z_inv = fe_mul(fe_mul(den1, den2), t0);

    let ix0 = fe_mul(x0, sqrt_m1());
    let iy0 = fe_mul(y0, sqrt_m1());
    let enchanted_denominator = fe_mul(den1, invsqrt_a_minus_d());

    let rotate = fe_is_negative(fe_mul(t0, z_inv));

    // Conditionally rotate x and y.
    let x = fe_select(rotate, iy0, x0);
    let y = fe_select(rotate, ix0, y0);
    let z = z0;
    let den_inv = fe_select(rotate, enchanted_denominator, den2);

    let y = fe_select(fe_is_negative(fe_mul(x, z_inv)), fe_neg(y), y);

    let s = fe_abs(fe_mul(den_inv, fe_sub(z, y)));

    fe_to_bytes(s)
}

/// Equals (RFC 9496, Section 4.3.3): true exactly when the two internal
/// representations stand for the same group element, that is when
/// x1 * y2 = y1 * x2 or y1 * y2 = x1 * x2.
pub fn equals(p: &EdPoint, q: &EdPoint) -> bool {
    let a = fe_ct_eq(fe_mul(p.x, q.y), fe_mul(p.y, q.x));
    let b = fe_ct_eq(fe_mul(p.y, q.y), fe_mul(p.x, q.x));
    (a | b) == 1
}

/// MAP (RFC 9496, Section 4.3.4): the Elligator-based map from a 32-byte
/// string to an internal representation.
///
/// Step 1 is performed by `fe_from_bytes`, which masks the most significant
/// bit of the final byte and accepts non-canonical values; the limb
/// representation of r stands for t = r mod p.
pub fn elligator_map(bytes: &[u8; 32]) -> EdPoint {
    let t = fe_from_bytes(bytes);

    let one = fe_one();
    let minus_one = fe_neg(one);
    let dd = d();

    // r = SQRT_M1 * t^2
    let r = fe_mul(sqrt_m1(), fe_sq(t));
    // u = (r + 1) * ONE_MINUS_D_SQ
    let u = fe_mul(fe_add(r, one), one_minus_d_sq());
    // v = (-1 - r*D) * (r + D)
    let v = fe_mul(fe_sub(minus_one, fe_mul(r, dd)), fe_add(r, dd));

    let (was_square, s) = sqrt_ratio_m1(u, v);
    // s_prime = -CT_ABS(s*t)
    let s_prime = fe_neg(fe_abs(fe_mul(s, t)));
    let s = fe_select(was_square, s, s_prime);
    let c = fe_select(was_square, minus_one, r);

    // N = c * (r - 1) * D_MINUS_ONE_SQ - v
    let n = fe_sub(fe_mul(fe_mul(c, fe_sub(r, one)), d_minus_one_sq()), v);

    let s_sq = fe_sq(s);
    // w0 = 2 * s * v
    let w0 = fe_mul(fe_add(s, s), v);
    // w1 = N * SQRT_AD_MINUS_ONE
    let w1 = fe_mul(n, sqrt_ad_minus_one());
    // w2 = 1 - s^2
    let w2 = fe_sub(one, s_sq);
    // w3 = 1 + s^2
    let w3 = fe_add(one, s_sq);

    EdPoint {
        x: fe_mul(w0, w3),
        y: fe_mul(w2, w1),
        z: fe_mul(w1, w3),
        t: fe_mul(w0, w2),
    }
}

/// Element derivation (RFC 9496, Section 4.3.4): `MAP(b[0:32]) + MAP(b[32:64])`
/// for a 64-byte string b.
pub fn from_uniform_bytes(b: &[u8; 64]) -> EdPoint {
    let mut b1 = [0u8; 32];
    let mut b2 = [0u8; 32];
    for i in 0..32 {
        b1[i] = b[i];
        b2[i] = b[32 + i];
    }
    let p1 = elligator_map(&b1);
    let p2 = elligator_map(&b2);
    point_add(&p1, &p2)
}

// --- Group law on internal representations (RFC 9496, Section 4) ---

/// The identity element, represented by the edwards25519 neutral point.
pub fn identity() -> EdPoint {
    point_identity()
}

/// The canonical generator (RFC 9496, Section 4), represented by the
/// Curve25519 base point.
pub fn generator() -> EdPoint {
    ed25519_base_point()
}

/// Element addition, applied to the internal representations.
pub fn element_add(p: &EdPoint, q: &EdPoint) -> EdPoint {
    point_add(p, q)
}

/// Element negation: (x, y, z, t) maps to (-x, y, z, -t).
pub fn element_neg(p: &EdPoint) -> EdPoint {
    EdPoint {
        x: fe_neg(p.x),
        y: p.y,
        z: p.z,
        t: fe_neg(p.t),
    }
}

/// Element subtraction: p + (-q).
pub fn element_sub(p: &EdPoint, q: &EdPoint) -> EdPoint {
    point_add(p, &element_neg(q))
}

/// Element doubling, applied to the internal representation.
pub fn element_double(p: &EdPoint) -> EdPoint {
    point_double(p)
}

/// Scalar multiplication by a secret 32-byte little-endian scalar
/// (RFC 9496, Section 4.4).
///
/// `edwards25519::scalar_mult` is a double-and-add that branches on the bits of
/// its scalar, so this function releases the scalar to it. It specifies the
/// value of the product; it is not a constant-time algorithm.
pub fn element_mul(scalar: &Scalar, p: &EdPoint) -> EdPoint {
    scalar_mult(&scalar.declassify(), p)
}

