//! Pure Rust hash-to-curve specification for curve25519 and edwards25519
//! (RFC 9380, Section 8.5).
//!
//! Suites:
//! - `curve25519_XMD:SHA-512_ELL2_RO_` (`hash_to_curve_curve25519`) and
//!   `curve25519_XMD:SHA-512_ELL2_NU_` (`encode_to_curve_curve25519`);
//! - `edwards25519_XMD:SHA-512_ELL2_RO_` (`hash_to_curve_edwards25519`) and
//!   `edwards25519_XMD:SHA-512_ELL2_NU_` (`encode_to_curve_edwards25519`).
//!
//! All four use F = GF(2^255 - 19), m = 1, L = 48, k = 128,
//! expand_message = `expand_message_xmd` with SHA-512, Z = 2 and h_eff = 8.
//!
//! - `map_to_curve_elligator2_curve25519`: RFC 9380, Appendix G.2.1, the
//!   straight-line form of the Elligator 2 method of Section 6.7.1.
//! - `map_to_curve_elligator2_edwards25519`: RFC 9380, Appendix G.2.2, the
//!   straight-line form of Section 6.8.2.
//! - `mont_to_edwards` / `mont_from_edwards`: the birational maps of
//!   RFC 7748, Section 4.1, which RFC 9380, Section 6.8.1 and Appendix D.1
//!   name as the rational map of these suites.
//! - `clear_cofactor_edwards25519` / `clear_cofactor_curve25519`: RFC 9380,
//!   Section 7, with h_eff = 8.
//! - `encode_to_curve_*` / `hash_to_curve_*`: RFC 9380, Section 3.
//!
//! Field arithmetic over GF(2^255 - 19) comes from `crate::curve25519`
//! (radix 2^51, `[u64; 5]`), the edwards25519 group law from
//! `crate::edwards25519`, and the constant-time field helpers and the square
//! root of -1 from `crate::ristretto255`. `fe_inv` computes a^(p - 2), which is
//! the inv0 of RFC 9380, Section 4: it sends 0 to 0.
//!
//! Booleans of the straight-line programs are `u64` values in {0, 1}, and
//! CMOV(a, b, c) of RFC 9380, Section 4 is `fe_select(c, b, a)`.
//!
//! The suite layout follows the hacspec example `edwards25519-hash`
//! (<https://github.com/hacspec/hacspec>, MIT OR Apache-2.0; Malte Thomsen,
//! Marcus Rasmussen, Tobias Vestergaard and the hacspec authors). Every
//! function body here transcribes the pseudocode of RFC 9380.
//!
//! No external dependencies. All functions are pure and value-passing.

use crate::curve25519::{fe_add, fe_from_bytes, fe_inv, fe_mul, fe_one, fe_reduce, fe_sq, fe_sub, fe_zero};
use crate::edwards25519::{point_add, point_double, EdPoint};
use crate::hash_to_field::hash_to_field_25519_sha512;
use crate::ristretto255::{
    fe_ct_eq, fe_is_negative, fe_is_zero, fe_neg, fe_pow22523, fe_select, sqrt_m1,
};

// --- Constants ---

/// J = 486662, the coefficient of the Montgomery curve
/// curve25519: K * t^2 = s^3 + J * s^2 + s with K = 1
/// (RFC 9380, Section 8.5; RFC 7748, Section 4.1).
pub fn mont_j() -> [u64; 5] {
    [486662, 0, 0, 0, 0]
}

/// c2 = 2^c1 with c1 = (q + 3) / 8 = 2^252 - 2 (RFC 9380, Appendix G.2.1,
/// constants 1 and 2).
///
/// c2 = 0x2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b1
///    = 1 + SQRT_M1, and c2^2 = 2 * SQRT_M1.
pub fn elligator2_c2() -> [u64; 5] {
    let bytes: [u8; 32] = [
        0xb1, 0xa0, 0x0e, 0x4a, 0x27, 0x1b, 0xee, 0xc4,
        0x78, 0xe4, 0x2f, 0xad, 0x06, 0x18, 0x43, 0x2f,
        0xa7, 0xd7, 0xfb, 0x3d, 0x99, 0x00, 0x4d, 0x2b,
        0x0b, 0xdf, 0xc1, 0x4f, 0x80, 0x24, 0x83, 0x2b,
    ];
    fe_from_bytes(&bytes)
}

/// c3 = sqrt(-1) (RFC 9380, Appendix G.2.1, constant 3): the SQRT_M1 of
/// `crate::ristretto255`.
pub fn elligator2_c3() -> [u64; 5] {
    sqrt_m1()
}

/// c1 = sqrt(-486664) with sgn0(c1) = 0 (RFC 9380, Appendix G.2.2).
///
/// c1 = 6853475219497561581579357271197624642482790079785650197046958215289687604742
///    = 0x0f26edf460a006bbd27b08dc03fc4f7ec5a1d3d14b7d1a82cc6e04aaff457e06
///
/// With this sign, `mont_from_edwards` sends the edwards25519 base point to
/// the curve25519 base point (9, v) with
/// v = 43114425171068552920764898935933967039370386198203806730763910166200978582548.
pub fn sqrt_neg_486664() -> [u64; 5] {
    let bytes: [u8; 32] = [
        0x06, 0x7e, 0x45, 0xff, 0xaa, 0x04, 0x6e, 0xcc,
        0x82, 0x1a, 0x7d, 0x4b, 0xd1, 0xd3, 0xa1, 0xc5,
        0x7e, 0x4f, 0xfc, 0x03, 0xdc, 0x08, 0x7b, 0xd2,
        0xbb, 0x06, 0xa0, 0x60, 0xf4, 0xed, 0x26, 0x0f,
    ];
    fe_from_bytes(&bytes)
}

// --- Field helpers (RFC 9380, Section 4) ---

/// sgn0(x) for m = 1 (RFC 9380, Section 4.1): x mod 2, where x is the least
/// nonnegative integer representing the field element.
pub fn h2c_sgn0(x: [u64; 5]) -> u64 {
    fe_is_negative(x)
}

// --- Appendix G.2.1: Elligator 2 for curve25519 ---

/// `map_to_curve_elligator2_curve25519(u)` (RFC 9380, Appendix G.2.1).
///
/// Returns `(xn, xd, yn, yd)` such that (xn / xd, yn / yd) is a point of
/// curve25519. `xd` is nonzero and `yd` is 1.
///
/// The exponentiation by c4 = (q - 5) / 8 of step 16 is `fe_pow22523`.
pub fn map_to_curve_elligator2_curve25519(
    u: [u64; 5],
) -> ([u64; 5], [u64; 5], [u64; 5], [u64; 5]) {
    let one = fe_one();
    let j = mont_j();
    let c2 = elligator2_c2();
    let c3 = elligator2_c3();

    // Steps 1 and 2: tv1 = 2 * u^2.
    let tv1 = fe_sq(u);
    let tv1 = fe_add(tv1, tv1);
    // Step 3: xd = tv1 + 1.
    let xd = fe_add(tv1, one);
    // Step 4: x1n = -J.
    let x1n = fe_neg(j);
    // Step 5: tv2 = xd^2.
    let tv2 = fe_sq(xd);
    // Step 6: gxd = xd^3.
    let gxd = fe_mul(tv2, xd);
    // Steps 7 to 10: gx1 = x1n^3 + J * x1n^2 * xd + x1n * xd^2.
    let gx1 = fe_mul(j, tv1);
    let gx1 = fe_mul(gx1, x1n);
    let gx1 = fe_add(gx1, tv2);
    let gx1 = fe_mul(gx1, x1n);
    // Step 11: tv3 = gxd^2.
    let tv3 = fe_sq(gxd);
    // Step 12: tv2 = gxd^4.
    let tv2 = fe_sq(tv3);
    // Step 13: tv3 = gxd^3.
    let tv3 = fe_mul(tv3, gxd);
    // Step 14: tv3 = gx1 * gxd^3.
    let tv3 = fe_mul(tv3, gx1);
    // Step 15: tv2 = gx1 * gxd^7.
    let tv2 = fe_mul(tv2, tv3);
    // Step 16: y11 = tv2^c4.
    let y11 = fe_pow22523(tv2);
    // Step 17: y11 = gx1 * gxd^3 * (gx1 * gxd^7)^((p - 5) / 8).
    let y11 = fe_mul(y11, tv3);
    // Step 18.
    let y12 = fe_mul(y11, c3);
    // Steps 19 and 20: tv2 = y11^2 * gxd.
    let tv2 = fe_sq(y11);
    let tv2 = fe_mul(tv2, gxd);
    // Step 21.
    let e1 = fe_ct_eq(tv2, gx1);
    // Step 22: y1 = CMOV(y12, y11, e1).
    let y1 = fe_select(e1, y11, y12);
    // Step 23: x2n = x1n * tv1.
    let x2n = fe_mul(x1n, tv1);
    // Steps 24 to 26.
    let y21 = fe_mul(y11, u);
    let y21 = fe_mul(y21, c2);
    let y22 = fe_mul(y21, c3);
    // Step 27: gx2 = gx1 * tv1.
    let gx2 = fe_mul(gx1, tv1);
    // Steps 28 and 29: tv2 = y21^2 * gxd.
    let tv2 = fe_sq(y21);
    let tv2 = fe_mul(tv2, gxd);
    // Step 30.
    let e2 = fe_ct_eq(tv2, gx2);
    // Step 31: y2 = CMOV(y22, y21, e2).
    let y2 = fe_select(e2, y21, y22);
    // Steps 32 and 33: tv2 = y1^2 * gxd.
    let tv2 = fe_sq(y1);
    let tv2 = fe_mul(tv2, gxd);
    // Step 34.
    let e3 = fe_ct_eq(tv2, gx1);
    // Step 35: xn = CMOV(x2n, x1n, e3).
    let xn = fe_select(e3, x1n, x2n);
    // Step 36: y = CMOV(y2, y1, e3).
    let y = fe_select(e3, y1, y2);
    // Step 37: e4 = sgn0(y) == 1.
    let e4 = h2c_sgn0(y);
    // Step 38: y = CMOV(y, -y, e3 XOR e4).
    let y = fe_select(e3 ^ e4, fe_neg(y), y);
    // Step 39.
    (xn, xd, y, one)
}

// --- Appendix G.2.2: Elligator 2 for edwards25519 ---

/// Steps 2 to 13 of `map_to_curve_elligator2_edwards25519`
/// (RFC 9380, Appendix G.2.2): the rational map of Section 6.8.1 applied to
/// the curve25519 point (xmn / xmd, ymn / ymd), with both exceptional cases
/// (a zero denominator) sent to the identity (0, 1).
///
/// Returns `(xn, xd, yn, yd)` such that (xn / xd, yn / yd) is a point of
/// edwards25519, with `xd` and `yd` nonzero.
pub fn h2c_rational_map_fractions(
    xmn: [u64; 5],
    xmd: [u64; 5],
    ymn: [u64; 5],
    ymd: [u64; 5],
) -> ([u64; 5], [u64; 5], [u64; 5], [u64; 5]) {
    let zero = fe_zero();
    let one = fe_one();
    let c1 = sqrt_neg_486664();

    // Steps 2 and 3: xn = xMn * yMd * c1.
    let xn = fe_mul(xmn, ymd);
    let xn = fe_mul(xn, c1);
    // Step 4: xd = xMd * yMn.
    let xd = fe_mul(xmd, ymn);
    // Step 5: yn = xMn - xMd.
    let yn = fe_sub(xmn, xmd);
    // Step 6: yd = xMn + xMd.
    let yd = fe_add(xmn, xmd);
    // Step 7: tv1 = xd * yd.
    let tv1 = fe_mul(xd, yd);
    // Step 8: e = tv1 == 0.
    let e = fe_is_zero(tv1);
    // Steps 9 to 12.
    let xn = fe_select(e, zero, xn);
    let xd = fe_select(e, one, xd);
    let yn = fe_select(e, one, yn);
    let yd = fe_select(e, one, yd);
    // Step 13.
    (xn, xd, yn, yd)
}

/// `map_to_curve_elligator2_edwards25519(u)` (RFC 9380, Appendix G.2.2).
///
/// Returns `(xn, xd, yn, yd)` such that (xn / xd, yn / yd) is a point of
/// edwards25519, with `xd` and `yd` nonzero. Step 1 is
/// `map_to_curve_elligator2_curve25519` and steps 2 to 13 are
/// `h2c_rational_map_fractions`.
pub fn map_to_curve_elligator2_edwards25519(
    u: [u64; 5],
) -> ([u64; 5], [u64; 5], [u64; 5], [u64; 5]) {
    // Step 1.
    let (xmn, xmd, ymn, ymd) = map_to_curve_elligator2_curve25519(u);
    // Steps 2 to 13.
    h2c_rational_map_fractions(xmn, xmd, ymn, ymd)
}

/// The edwards25519 point (xn / xd, yn / yd) in extended coordinates, for
/// nonzero `xd` and `yd`: (X, Y, Z, T) = (xn * yd, yn * xd, xd * yd, xn * yn).
pub fn edwards_point_from_fractions(
    xn: [u64; 5],
    xd: [u64; 5],
    yn: [u64; 5],
    yd: [u64; 5],
) -> EdPoint {
    EdPoint {
        x: fe_mul(xn, yd),
        y: fe_mul(yn, xd),
        z: fe_mul(xd, yd),
        t: fe_mul(xn, yn),
    }
}

// --- curve25519 points and the birational maps (RFC 7748, Section 4.1) ---

/// A point of curve25519, v^2 = u^3 + 486662 * u^2 + u, in affine
/// coordinates.
///
/// `infinity` is 1 for the point at infinity, which is then stored with
/// u = v = 0, and 0 for the affine point (u, v). `u` and `v` are canonical
/// field elements in every value returned by this module.
#[derive(Clone, Copy, Debug)]
pub struct MontPoint {
    pub u: [u64; 5],
    pub v: [u64; 5],
    pub infinity: u64,
}

/// The affine curve25519 point (xn / xd, yn / yd), for nonzero `xd` and `yd`.
pub fn mont_point_from_fractions(
    xn: [u64; 5],
    xd: [u64; 5],
    yn: [u64; 5],
    yd: [u64; 5],
) -> MontPoint {
    MontPoint {
        u: fe_reduce(fe_mul(xn, fe_inv(xd))),
        v: fe_reduce(fe_mul(yn, fe_inv(yd))),
        infinity: 0,
    }
}

/// The birational map from curve25519 to edwards25519 (RFC 7748,
/// Section 4.1; RFC 9380, Section 6.8.1 and Appendix D.1), as a group
/// isomorphism:
///
///   (u, v) maps to (x, y) = (sqrt(-486664) * u / v, (u - 1) / (u + 1)),
///
/// the point at infinity maps to the identity (0, 1), and the point (0, 0)
/// of order 2 maps to the point (0, -1) of order 2. No point of curve25519
/// has u = -1, since 486660 is not a square, so v = 0 is the only zero
/// denominator of an affine point.
///
/// This differs from steps 8 to 12 of RFC 9380, Appendix G.2.2 on the single
/// point (0, 0), which those steps send to the identity.
pub fn mont_to_edwards(p: &MontPoint) -> EdPoint {
    let zero = fe_zero();
    let one = fe_one();
    let is_inf = p.infinity;
    // The affine point of order 2.
    let is_two = fe_is_zero(p.v) & (1 - is_inf);
    let special = is_inf | is_two;

    let xn = fe_mul(sqrt_neg_486664(), p.u);
    let xd = p.v;
    let yn = fe_sub(p.u, one);
    let yd = fe_add(p.u, one);

    let xn = fe_select(special, zero, xn);
    let xd = fe_select(special, one, xd);
    let yn = fe_select(is_inf, one, fe_select(is_two, fe_neg(one), yn));
    let yd = fe_select(special, one, yd);

    edwards_point_from_fractions(xn, xd, yn, yd)
}

/// The birational map from edwards25519 to curve25519 (RFC 7748,
/// Section 4.1), inverse to `mont_to_edwards`:
///
///   (x, y) maps to (u, v) = ((1 + y) / (1 - y), sqrt(-486664) * u / x),
///
/// the identity (0, 1) maps to the point at infinity, and (0, -1) maps to
/// (0, 0), which the formula gives with inv0(0) = 0.
pub fn mont_from_edwards(p: &EdPoint) -> MontPoint {
    // u = (Z + Y) / (Z - Y).
    let den = fe_sub(p.z, p.y);
    let is_inf = fe_is_zero(den);
    let u = fe_mul(fe_add(p.z, p.y), fe_inv(den));
    // v = sqrt(-486664) * u * Z / X.
    let v = fe_mul(fe_mul(sqrt_neg_486664(), u), fe_mul(p.z, fe_inv(p.x)));
    MontPoint {
        u: fe_reduce(u),
        v: fe_reduce(v),
        infinity: is_inf,
    }
}

/// Point addition on curve25519: the edwards25519 addition transported along
/// the group isomorphism `mont_to_edwards`.
pub fn mont_point_add(p: &MontPoint, q: &MontPoint) -> MontPoint {
    mont_from_edwards(&point_add(&mont_to_edwards(p), &mont_to_edwards(q)))
}

// --- Section 7: clearing the cofactor ---

/// `clear_cofactor(P)` for edwards25519 (RFC 9380, Section 7): h_eff * P with
/// h_eff = 8, as three doublings.
pub fn clear_cofactor_edwards25519(p: &EdPoint) -> EdPoint {
    point_double(&point_double(&point_double(p)))
}

/// `clear_cofactor(P)` for curve25519 (RFC 9380, Section 7): h_eff * P with
/// h_eff = 8.
///
/// The multiplication is carried out on edwards25519: the result is
/// `mont_from_edwards(8 * mont_to_edwards(P))`. `mont_to_edwards` is a group
/// isomorphism with inverse `mont_from_edwards`, so this is 8 * P on
/// curve25519. RFC 9380, Appendix D.1 allows evaluating a Montgomery suite
/// through the equivalent twisted Edwards curve, and this crate has no
/// Montgomery point addition outside the x-only ladder.
pub fn clear_cofactor_curve25519(p: &MontPoint) -> MontPoint {
    mont_from_edwards(&clear_cofactor_edwards25519(&mont_to_edwards(p)))
}

// --- Section 3: encoding byte strings to the curves ---

/// `map_to_curve(u)` for the edwards25519 suites, as an `EdPoint`.
pub fn map_to_curve_edwards25519(u: [u64; 5]) -> EdPoint {
    let (xn, xd, yn, yd) = map_to_curve_elligator2_edwards25519(u);
    edwards_point_from_fractions(xn, xd, yn, yd)
}

/// `map_to_curve(u)` for the curve25519 suites, as a `MontPoint`.
pub fn map_to_curve_curve25519(u: [u64; 5]) -> MontPoint {
    let (xn, xd, yn, yd) = map_to_curve_elligator2_curve25519(u);
    mont_point_from_fractions(xn, xd, yn, yd)
}

/// `encode_to_curve(msg)` of RFC 9380, Section 3, for the suite
/// `edwards25519_XMD:SHA-512_ELL2_NU_` with domain separation tag `dst`.
///
/// Returns `None` exactly when `hash_to_field_25519_sha512(msg, dst, 1)`
/// does, that is when `len(dst) > 255`.
pub fn encode_to_curve_edwards25519(msg: &[u8], dst: &[u8]) -> Option<EdPoint> {
    // Step 1: u = hash_to_field(msg, 1).
    match hash_to_field_25519_sha512(msg, dst, 1) {
        None => None,
        Some(u) => {
            // Step 2: Q = map_to_curve(u[0]).
            let q = map_to_curve_edwards25519(u[0]);
            // Step 3: P = clear_cofactor(Q).
            Some(clear_cofactor_edwards25519(&q))
        }
    }
}

/// `hash_to_curve(msg)` of RFC 9380, Section 3, for the suite
/// `edwards25519_XMD:SHA-512_ELL2_RO_` with domain separation tag `dst`.
///
/// Returns `None` exactly when `hash_to_field_25519_sha512(msg, dst, 2)`
/// does, that is when `len(dst) > 255`.
pub fn hash_to_curve_edwards25519(msg: &[u8], dst: &[u8]) -> Option<EdPoint> {
    // Step 1: u = hash_to_field(msg, 2).
    match hash_to_field_25519_sha512(msg, dst, 2) {
        None => None,
        Some(u) => {
            // Step 2: Q0 = map_to_curve(u[0]).
            let q0 = map_to_curve_edwards25519(u[0]);
            // Step 3: Q1 = map_to_curve(u[1]).
            let q1 = map_to_curve_edwards25519(u[1]);
            // Step 4: R = Q0 + Q1.
            let r = point_add(&q0, &q1);
            // Step 5: P = clear_cofactor(R).
            Some(clear_cofactor_edwards25519(&r))
        }
    }
}

/// `encode_to_curve(msg)` of RFC 9380, Section 3, for the suite
/// `curve25519_XMD:SHA-512_ELL2_NU_` with domain separation tag `dst`. The
/// result carries both affine coordinates (u, v).
///
/// Returns `None` exactly when `hash_to_field_25519_sha512(msg, dst, 1)`
/// does, that is when `len(dst) > 255`.
pub fn encode_to_curve_curve25519(msg: &[u8], dst: &[u8]) -> Option<MontPoint> {
    // Step 1: u = hash_to_field(msg, 1).
    match hash_to_field_25519_sha512(msg, dst, 1) {
        None => None,
        Some(u) => {
            // Step 2: Q = map_to_curve(u[0]).
            let q = map_to_curve_curve25519(u[0]);
            // Step 3: P = clear_cofactor(Q).
            Some(clear_cofactor_curve25519(&q))
        }
    }
}

/// `hash_to_curve(msg)` of RFC 9380, Section 3, for the suite
/// `curve25519_XMD:SHA-512_ELL2_RO_` with domain separation tag `dst`. The
/// result carries both affine coordinates (u, v).
///
/// Returns `None` exactly when `hash_to_field_25519_sha512(msg, dst, 2)`
/// does, that is when `len(dst) > 255`.
pub fn hash_to_curve_curve25519(msg: &[u8], dst: &[u8]) -> Option<MontPoint> {
    // Step 1: u = hash_to_field(msg, 2).
    match hash_to_field_25519_sha512(msg, dst, 2) {
        None => None,
        Some(u) => {
            // Step 2: Q0 = map_to_curve(u[0]).
            let q0 = map_to_curve_curve25519(u[0]);
            // Step 3: Q1 = map_to_curve(u[1]).
            let q1 = map_to_curve_curve25519(u[1]);
            // Step 4: R = Q0 + Q1.
            let r = mont_point_add(&q0, &q1);
            // Step 5: P = clear_cofactor(R).
            Some(clear_cofactor_curve25519(&r))
        }
    }
}
