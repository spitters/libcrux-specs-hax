//! Pure Rust NIST P-256 elliptic curve specification (FIPS 186-4, NIST SP 800-186).
//!
//! Curve: y^2 = x^3 - 3x + b over GF(p)
//! p = 2^256 - 2^224 + 2^192 + 2^96 - 1
//!
//! Field elements are stored as `[u64; 4]` in big-endian limb order
//! (`limbs[0]` is the most significant 64-bit word).
//! Point representation uses Jacobian coordinates (X, Y, Z) where
//! affine (x, y) = (X/Z^2, Y/Z^3).
//!
//! No external dependencies. All functions are pure and value-passing.

/// The P-256 field element type: [u64; 4], big-endian limb order.
pub type P256FieldElement = [u64; 4];

/// A point on the P-256 curve in Jacobian coordinates.
/// The point at infinity is represented by Z = 0.
#[derive(Clone, Copy, Debug)]
pub struct P256Point {
    pub x: P256FieldElement,
    pub y: P256FieldElement,
    pub z: P256FieldElement,
}

// --- Curve constants ---

/// Prime p = 2^256 - 2^224 + 2^192 + 2^96 - 1
///         = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
pub const P256_P: P256FieldElement = [
    0xFFFFFFFF00000001,
    0x0000000000000000,
    0x00000000FFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
];

/// Curve parameter b.
/// b = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
pub const P256_B: P256FieldElement = [
    0x5AC635D8AA3A93E7,
    0xB3EBBD55769886BC,
    0x651D06B0CC53B0F6,
    0x3BCE3C3E27D2604B,
];

/// Group order n.
/// n = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
pub const P256_N: P256FieldElement = [
    0xFFFFFFFF00000000,
    0xFFFFFFFFFFFFFFFF,
    0xBCE6FAADA7179E84,
    0xF3B9CAC2FC632551,
];

/// Base point x-coordinate (Gx).
/// Gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
pub const P256_GX: P256FieldElement = [
    0x6B17D1F2E12C4247,
    0xF8BCE6E563A440F2,
    0x77037D812DEB33A0,
    0xF4A13945D898C296,
];

/// Base point y-coordinate (Gy).
/// Gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
pub const P256_GY: P256FieldElement = [
    0x4FE342E2FE1A7F9B,
    0x8EE7EB4A7C0F9E16,
    0x2BCE33576B315ECE,
    0xCBB6406837BF51F5,
];

// --- 256-bit and 512-bit arithmetic helpers ---

/// Compare two 256-bit numbers (big-endian limb order).
/// Returns -1 if a < b, 0 if a == b, 1 if a > b.
fn cmp256(a: &P256FieldElement, b: &P256FieldElement) -> i32 {
    let mut i = 0;
    while i < 4 {
        if a[i] < b[i] {
            return -1;
        }
        if a[i] > b[i] {
            return 1;
        }
        i += 1;
    }
    0
}

/// 256-bit addition: a + b, returns (result, carry).
fn add256(a: &P256FieldElement, b: &P256FieldElement) -> (P256FieldElement, u64) {
    let mut r = [0u64; 4];
    let mut carry: u128 = 0;

    let mut i: usize = 4;
    while i > 0 {
        i -= 1;
        let s = (a[i] as u128) + (b[i] as u128) + carry;
        r[i] = s as u64;
        carry = s >> 64;
    }

    (r, carry as u64)
}

/// 256-bit subtraction: a - b, returns (result, borrow).
/// borrow is 1 if a < b.
fn sub256(a: &P256FieldElement, b: &P256FieldElement) -> (P256FieldElement, u64) {
    let mut r = [0u64; 4];
    let mut borrow: u128 = 0;

    let mut i: usize = 4;
    while i > 0 {
        i -= 1;
        let s = (a[i] as u128).wrapping_sub(b[i] as u128).wrapping_sub(borrow);
        r[i] = s as u64;
        borrow = (s >> 127) & 1; // borrow if negative
    }

    (r, borrow as u64)
}

// --- Field arithmetic mod p ---

/// Field addition: (a + b) mod p.
pub fn fp_add(a: P256FieldElement, b: P256FieldElement) -> P256FieldElement {
    let (mut r, carry) = add256(&a, &b);
    // If carry or r >= p, subtract p.
    if carry == 1 || cmp256(&r, &P256_P) >= 0 {
        let (s, _) = sub256(&r, &P256_P);
        r = s;
    }
    r
}

/// Field subtraction: (a - b) mod p.
pub fn fp_sub(a: P256FieldElement, b: P256FieldElement) -> P256FieldElement {
    let (r, borrow) = sub256(&a, &b);
    if borrow == 1 {
        // Add p back
        let (s, _) = add256(&r, &P256_P);
        s
    } else {
        r
    }
}

/// Field negation: (-a) mod p.
pub fn fp_neg(a: P256FieldElement) -> P256FieldElement {
    if a == [0, 0, 0, 0] {
        a
    } else {
        fp_sub([0, 0, 0, 0], a)
    }
}

/// 256x256 -> 512-bit multiplication (schoolbook).
/// Result stored as [u64; 8] in big-endian order.
fn mul256_full(a: &P256FieldElement, b: &P256FieldElement) -> [u64; 8] {
    // Use a [u64; 9] accumulator (little-endian) and propagate carries
    // after each inner-loop iteration to avoid u128 overflow.
    let mut r = [0u64; 9];

    let mut i = 0;
    while i < 4 {
        let mut carry: u128 = 0;
        let mut j = 0;
        while j < 4 {
            let prod = (a[3 - i] as u128) * (b[3 - j] as u128)
                + (r[i + j] as u128) + carry;
            r[i + j] = prod as u64;
            carry = prod >> 64;
            j += 1;
        }
        r[i + 4] = carry as u64;
        i += 1;
    }

    // Convert from little-endian to big-endian [u64; 8].
    let mut out = [0u64; 8];
    let mut k = 0;
    while k < 8 {
        out[7 - k] = r[k];
        k += 1;
    }
    out
}

/// Reduce a 512-bit number mod p using the NIST P-256 fast reduction.
///
/// The 512-bit input c is split into 32-bit words c[0]..c[15] (big-endian).
/// Then the result is:
///   T + S1 + S2 + S3 + S4 - D1 - D2 - D3 - D4  (mod p)
///
/// See NIST SP 800-186 / Solinas reduction for P-256.
fn reduce_mod_p(c: &[u64; 8]) -> P256FieldElement {
    // Split into 32-bit words: c[0] is MSW, c[15] is LSW.
    let mut w = [0u32; 16];
    let mut i = 0;
    while i < 8 {
        w[2 * i] = (c[i] >> 32) as u32;
        w[2 * i + 1] = c[i] as u32;
        i += 1;
    }
    // w[0] = most significant 32-bit word, w[15] = least significant

    // Helper: build a 256-bit number from eight 32-bit words (big-endian)
    // as [u64; 4].
    let build = |a7: u32, a6: u32, a5: u32, a4: u32, a3: u32, a2: u32, a1: u32, a0: u32| -> P256FieldElement {
        [
            ((a7 as u64) << 32) | (a6 as u64),
            ((a5 as u64) << 32) | (a4 as u64),
            ((a3 as u64) << 32) | (a2 as u64),
            ((a1 as u64) << 32) | (a0 as u64),
        ]
    };

    // w indices: w[0]=c15(MSB)...w[15]=c0(LSB) -- wait, we defined w[0]=MSW.
    // Standard notation for NIST reduction uses c0..c15 where c0 is LSW.
    // Let's map: c_i = w[15 - i].
    // So c0 = w[15], c1 = w[14], ..., c15 = w[0].
    let c = |idx: usize| -> u32 { w[15 - idx] };

    // T  = (c7, c6, c5, c4, c3, c2, c1, c0)
    let t = build(c(7), c(6), c(5), c(4), c(3), c(2), c(1), c(0));
    // S1 = (c15, c14, c13, c12, c11, 0, 0, 0) -- doubled
    let s1 = build(c(15), c(14), c(13), c(12), c(11), 0, 0, 0);
    // S2 = (0, c15, c14, c13, c12, 0, 0, 0) -- doubled
    let s2 = build(0, c(15), c(14), c(13), c(12), 0, 0, 0);
    // S3 = (c15, c14, 0, 0, 0, c10, c9, c8)
    let s3 = build(c(15), c(14), 0, 0, 0, c(10), c(9), c(8));
    // S4 = (c8, c13, c15, c14, c13, c11, c10, c9)
    let s4 = build(c(8), c(13), c(15), c(14), c(13), c(11), c(10), c(9));
    // D1 = (c10, c8, 0, 0, 0, c13, c12, c11)
    let d1 = build(c(10), c(8), 0, 0, 0, c(13), c(12), c(11));
    // D2 = (c11, c9, 0, 0, c15, c14, c13, c12)
    let d2 = build(c(11), c(9), 0, 0, c(15), c(14), c(13), c(12));
    // D3 = (c12, 0, c10, c9, c8, c15, c14, c13)
    let d3 = build(c(12), 0, c(10), c(9), c(8), c(15), c(14), c(13));
    // D4 = (c13, 0, c11, c10, c9, 0, c15, c14)
    let d4 = build(c(13), 0, c(11), c(10), c(9), 0, c(15), c(14));

    // Compute: result = T + 2*S1 + 2*S2 + S3 + S4 - D1 - D2 - D3 - D4 (mod p)
    // Use signed arithmetic by tracking borrows.

    // We use a wider representation to handle carries/borrows: [i128; 4]
    // with big-endian limb order.
    let mut acc = [0i128; 4];

    // Add T
    let mut k = 0;
    while k < 4 {
        acc[k] += t[k] as i128;
        k += 1;
    }

    // Add 2*S1
    k = 0;
    while k < 4 {
        acc[k] += 2 * (s1[k] as i128);
        k += 1;
    }

    // Add 2*S2
    k = 0;
    while k < 4 {
        acc[k] += 2 * (s2[k] as i128);
        k += 1;
    }

    // Add S3
    k = 0;
    while k < 4 {
        acc[k] += s3[k] as i128;
        k += 1;
    }

    // Add S4
    k = 0;
    while k < 4 {
        acc[k] += s4[k] as i128;
        k += 1;
    }

    // Subtract D1
    k = 0;
    while k < 4 {
        acc[k] -= d1[k] as i128;
        k += 1;
    }

    // Subtract D2
    k = 0;
    while k < 4 {
        acc[k] -= d2[k] as i128;
        k += 1;
    }

    // Subtract D3
    k = 0;
    while k < 4 {
        acc[k] -= d3[k] as i128;
        k += 1;
    }

    // Subtract D4
    k = 0;
    while k < 4 {
        acc[k] -= d4[k] as i128;
        k += 1;
    }

    // Now propagate carries from LSW (index 3) to MSW (index 0).
    let mut carry: i128 = 0;
    let mut j: usize = 4;
    while j > 0 {
        j -= 1;
        acc[j] += carry;
        carry = acc[j] >> 64;
        acc[j] &= 0xFFFFFFFFFFFFFFFF;
    }

    // Convert to u64 and reduce mod p.
    // The result might be negative or >= p, so we adjust.
    let mut r: P256FieldElement = [
        acc[0] as u64,
        acc[1] as u64,
        acc[2] as u64,
        acc[3] as u64,
    ];

    // The value is r + carry * 2^256. While it is negative, add p: the
    // carry out of the 256-bit addition is what moves into `carry`, so the
    // value grows by exactly p.
    while carry < 0 {
        let (s, carry_out) = add256(&r, &P256_P);
        r = s;
        carry += carry_out as i128;
    }

    // While the value is at least 2^256, subtract p: the borrow out of the
    // 256-bit subtraction is what leaves `carry`, so the value shrinks by
    // exactly p.
    while carry > 0 {
        let (s, borrow_out) = sub256(&r, &P256_P);
        r = s;
        carry -= borrow_out as i128;
    }

    // Final reduction: ensure 0 <= r < p.
    while cmp256(&r, &P256_P) >= 0 {
        let (s, _) = sub256(&r, &P256_P);
        r = s;
    }

    r
}

/// Field multiplication: (a * b) mod p.
pub fn fp_mul(a: P256FieldElement, b: P256FieldElement) -> P256FieldElement {
    let wide = mul256_full(&a, &b);
    reduce_mod_p(&wide)
}

/// Field squaring: a^2 mod p.
pub fn fp_sq(a: P256FieldElement) -> P256FieldElement {
    fp_mul(a, a)
}

/// Field inversion via Fermat's little theorem: a^(p-2) mod p.
pub fn fp_inv(a: P256FieldElement) -> P256FieldElement {
    // p - 2 = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFD
    // Use square-and-multiply (binary method).
    let mut result = [0u64; 4];
    result[3] = 1; // result = 1

    // p - 2 in bits (256 bits, big-endian)
    let exp = [
        0xFFFFFFFF00000001u64,
        0x0000000000000000,
        0x00000000FFFFFFFF,
        0xFFFFFFFFFFFFFFFD,
    ];

    let mut bit_pos: i32 = 255;
    while bit_pos >= 0 {
        result = fp_sq(result);
        let word = (bit_pos / 64) as usize;
        let bit = (bit_pos % 64) as u32;
        if (exp[3 - word] >> bit) & 1 == 1 {
            result = fp_mul(result, a);
        }
        bit_pos -= 1;
    }

    result
}

/// Encode a field element to 32 bytes (big-endian).
pub fn fp_to_bytes(a: P256FieldElement) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 4 {
        let bytes = a[i].to_be_bytes();
        let mut j = 0;
        while j < 8 {
            out[i * 8 + j] = bytes[j];
            j += 1;
        }
        i += 1;
    }
    out
}

/// Decode a field element from 32 bytes (big-endian).
pub fn fp_from_bytes(b: &[u8; 32]) -> P256FieldElement {
    let mut r = [0u64; 4];
    let mut i = 0;
    while i < 4 {
        let mut word = 0u64;
        let mut j = 0;
        while j < 8 {
            word = (word << 8) | (b[i * 8 + j] as u64);
            j += 1;
        }
        r[i] = word;
        i += 1;
    }
    r
}

// --- Scalar field arithmetic (mod n) ---

/// Compare two 256-bit numbers for the scalar field.
fn cmp256_n(a: &P256FieldElement, b: &P256FieldElement) -> i32 {
    cmp256(a, b)
}

/// Scalar addition: (a + b) mod n.
pub fn fn_add(a: P256FieldElement, b: P256FieldElement) -> P256FieldElement {
    let (mut r, carry) = add256(&a, &b);
    if carry == 1 || cmp256_n(&r, &P256_N) >= 0 {
        let (s, _) = sub256(&r, &P256_N);
        r = s;
    }
    r
}

/// Scalar multiplication: (a * b) mod n.
pub fn fn_mul(a: P256FieldElement, b: P256FieldElement) -> P256FieldElement {
    let wide = mul256_full(&a, &b);
    // Simple reduction mod n: repeated subtraction (spec, not optimised).
    reduce_mod_n(&wide)
}

/// Reduce a 512-bit number mod n by trial subtraction.
/// This is a spec-quality implementation — not optimised.
fn reduce_mod_n(c: &[u64; 8]) -> P256FieldElement {
    // Convert 512-bit number to a pair of 256-bit halves and reduce.
    // We use long division: process one bit at a time from MSB.
    // For a spec, we do it simply with a 256-bit accumulator.

    let mut acc = [0u64; 4]; // 256-bit accumulator

    let mut bit_pos: i32 = 511;
    while bit_pos >= 0 {
        // Shift acc left by 1 bit.
        let mut carry_bit: u64 = 0;
        let mut k: usize = 4;
        while k > 0 {
            k -= 1;
            let new_carry = acc[k] >> 63;
            acc[k] = (acc[k] << 1) | carry_bit;
            carry_bit = new_carry;
        }

        // Add the current bit from c.
        let word_idx = (bit_pos / 64) as usize;
        let bit_idx = (bit_pos % 64) as u32;
        let bit_val = (c[7 - word_idx] >> bit_idx) & 1;
        let (s, c1) = add256(&acc, &[0, 0, 0, bit_val]);
        acc = s;

        // Combine carry_bit and c1.
        let total_carry = carry_bit + c1;

        // If acc >= n (or there was a carry), subtract n.
        if total_carry > 0 || cmp256(&acc, &P256_N) >= 0 {
            let (s, _) = sub256(&acc, &P256_N);
            acc = s;
        }

        bit_pos -= 1;
    }

    acc
}

/// Scalar inversion: a^(n-2) mod n via Fermat's little theorem.
pub fn fn_inv(a: P256FieldElement) -> P256FieldElement {
    // n - 2 = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC63254F
    let exp: P256FieldElement = [
        0xFFFFFFFF00000000,
        0xFFFFFFFFFFFFFFFF,
        0xBCE6FAADA7179E84,
        0xF3B9CAC2FC63254F,
    ];

    let mut result: P256FieldElement = [0, 0, 0, 1];

    let mut bit_pos: i32 = 255;
    while bit_pos >= 0 {
        result = fn_mul(result, result);
        let word = (bit_pos / 64) as usize;
        let bit = (bit_pos % 64) as u32;
        if (exp[3 - word] >> bit) & 1 == 1 {
            result = fn_mul(result, a);
        }
        bit_pos -= 1;
    }

    result
}

/// Decode a 32-byte big-endian integer as a scalar mod n.
pub fn fn_from_bytes(b: &[u8; 32]) -> P256FieldElement {
    let v = fp_from_bytes(b);
    // Reduce mod n if needed.
    if cmp256(&v, &P256_N) >= 0 {
        let (s, _) = sub256(&v, &P256_N);
        s
    } else {
        v
    }
}

// --- Point operations (Jacobian coordinates) ---

/// The point at infinity (identity element).
pub fn point_identity() -> P256Point {
    P256Point {
        x: [0, 0, 0, 1],
        y: [0, 0, 0, 1],
        z: [0, 0, 0, 0],
    }
}

/// Check if a point is the identity (Z == 0).
pub fn point_is_identity(p: &P256Point) -> bool {
    p.z == [0, 0, 0, 0]
}

/// The standard base point G.
pub fn base_point() -> P256Point {
    P256Point {
        x: P256_GX,
        y: P256_GY,
        z: [0, 0, 0, 1], // affine, Z = 1
    }
}

/// Point doubling in Jacobian coordinates.
///
/// Using the formula from "Guide to Elliptic Curve Cryptography" (Hankerson et al.),
/// Algorithm 3.21, specialised for a = -3.
///
/// Input: P = (X1, Y1, Z1)
/// Output: 2P = (X3, Y3, Z3)
///
/// If Y1 == 0 or P is identity, return identity.
///
///   S = 4 * X1 * Y1^2
///   M = 3 * X1^2 + a * Z1^4  (with a = -3: M = 3*(X1 - Z1^2)*(X1 + Z1^2))
///   X3 = M^2 - 2*S
///   Y3 = M*(S - X3) - 8*Y1^4
///   Z3 = 2*Y1*Z1
pub fn point_double(p: &P256Point) -> P256Point {
    if point_is_identity(p) {
        return point_identity();
    }

    let x1 = p.x;
    let y1 = p.y;
    let z1 = p.z;

    let y1_sq = fp_sq(y1);
    // s = 4 * X1 * Y1^2
    let four = [0u64, 0, 0, 4];
    let s = fp_mul(four, fp_mul(x1, y1_sq));

    let z1_sq = fp_sq(z1);
    // M = 3*(X1 - Z1^2)*(X1 + Z1^2)   [since a = -3]
    let three = [0u64, 0, 0, 3];
    let m = fp_mul(three, fp_mul(fp_sub(x1, z1_sq), fp_add(x1, z1_sq)));

    // X3 = M^2 - 2*S
    let m_sq = fp_sq(m);
    let two_s = fp_add(s, s);
    let x3 = fp_sub(m_sq, two_s);

    // Y3 = M*(S - X3) - 8*Y1^4
    let eight = [0u64, 0, 0, 8];
    let y1_4 = fp_sq(y1_sq);
    let y3 = fp_sub(fp_mul(m, fp_sub(s, x3)), fp_mul(eight, y1_4));

    // Z3 = 2*Y1*Z1
    let two = [0u64, 0, 0, 2];
    let z3 = fp_mul(two, fp_mul(y1, z1));

    P256Point { x: x3, y: y3, z: z3 }
}

/// Point addition in Jacobian coordinates.
///
/// Using mixed Jacobian addition when one point has Z=1 is a special case;
/// this is the general formula.
///
/// Input: P = (X1,Y1,Z1), Q = (X2,Y2,Z2)
/// Output: P + Q
///
///   U1 = X1*Z2^2, U2 = X2*Z1^2
///   S1 = Y1*Z2^3, S2 = Y2*Z1^3
///   H = U2 - U1, R = S2 - S1
///   If H == 0 and R == 0: return point_double(P)
///   If H == 0 and R != 0: return identity (P = -Q)
///   X3 = R^2 - H^3 - 2*U1*H^2
///   Y3 = R*(U1*H^2 - X3) - S1*H^3
///   Z3 = H*Z1*Z2
pub fn point_add(p: &P256Point, q: &P256Point) -> P256Point {
    if point_is_identity(p) {
        return *q;
    }
    if point_is_identity(q) {
        return *p;
    }

    let z1_sq = fp_sq(p.z);
    let z2_sq = fp_sq(q.z);
    let z1_cu = fp_mul(z1_sq, p.z);
    let z2_cu = fp_mul(z2_sq, q.z);

    let u1 = fp_mul(p.x, z2_sq);
    let u2 = fp_mul(q.x, z1_sq);
    let s1 = fp_mul(p.y, z2_cu);
    let s2 = fp_mul(q.y, z1_cu);

    let h = fp_sub(u2, u1);
    let r = fp_sub(s2, s1);

    // Check if H == 0
    let zero: P256FieldElement = [0, 0, 0, 0];

    if h == zero {
        if r == zero {
            return point_double(p);
        } else {
            return point_identity();
        }
    }

    let h_sq = fp_sq(h);
    let h_cu = fp_mul(h_sq, h);
    let r_sq = fp_sq(r);

    let two = [0u64, 0, 0, 2];
    let u1_h_sq = fp_mul(u1, h_sq);

    // X3 = R^2 - H^3 - 2*U1*H^2
    let x3 = fp_sub(fp_sub(r_sq, h_cu), fp_mul(two, u1_h_sq));

    // Y3 = R*(U1*H^2 - X3) - S1*H^3
    let y3 = fp_sub(fp_mul(r, fp_sub(u1_h_sq, x3)), fp_mul(s1, h_cu));

    // Z3 = H*Z1*Z2
    let z3 = fp_mul(h, fp_mul(p.z, q.z));

    P256Point { x: x3, y: y3, z: z3 }
}

/// Scalar multiplication: k * P using double-and-add (left-to-right binary).
pub fn scalar_mult(k: &[u8; 32], p: &P256Point) -> P256Point {
    let mut result = point_identity();
    let mut i = 0;
    while i < 256 {
        result = point_double(&result);
        let byte_idx = i / 8;
        let bit_idx = 7 - (i % 8);
        if (k[byte_idx] >> bit_idx) & 1 == 1 {
            result = point_add(&result, p);
        }
        i += 1;
    }
    result
}

/// Base point multiplication: k * G.
pub fn base_mult(k: &[u8; 32]) -> P256Point {
    let g = base_point();
    scalar_mult(k, &g)
}

/// Convert Jacobian coordinates to affine (x, y) and encode as uncompressed.
/// Returns 0x04 || x (32 bytes BE) || y (32 bytes BE) = 65 bytes.
pub fn point_to_uncompressed(p: &P256Point) -> [u8; 65] {
    let mut out = [0u8; 65];

    if point_is_identity(p) {
        // Point at infinity: encode as all zeros with 0x04 prefix.
        out[0] = 0x04;
        return out;
    }

    let z_inv = fp_inv(p.z);
    let z_inv_sq = fp_sq(z_inv);
    let z_inv_cu = fp_mul(z_inv_sq, z_inv);

    let x = fp_mul(p.x, z_inv_sq);
    let y = fp_mul(p.y, z_inv_cu);

    out[0] = 0x04;
    let xb = fp_to_bytes(x);
    let yb = fp_to_bytes(y);
    let mut j = 0;
    while j < 32 {
        out[1 + j] = xb[j];
        out[33 + j] = yb[j];
        j += 1;
    }

    out
}

/// Decode a 65-byte uncompressed point (0x04 || x || y).
/// Returns None if the prefix is wrong or the point is not on the curve.
pub fn point_from_uncompressed(bytes: &[u8; 65]) -> Option<P256Point> {
    if bytes[0] != 0x04 {
        return None;
    }

    let mut xb = [0u8; 32];
    let mut yb = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        xb[i] = bytes[1 + i];
        yb[i] = bytes[33 + i];
        i += 1;
    }

    let x = fp_from_bytes(&xb);
    let y = fp_from_bytes(&yb);

    // Check that the point is on the curve: y^2 = x^3 - 3x + b (mod p)
    let y_sq = fp_sq(y);
    let x_sq = fp_sq(x);
    let x_cu = fp_mul(x_sq, x);
    let three_x = fp_mul([0, 0, 0, 3], x);
    let rhs = fp_add(fp_sub(x_cu, three_x), P256_B);

    if y_sq != rhs {
        return None;
    }

    Some(P256Point {
        x,
        y,
        z: [0, 0, 0, 1],
    })
}

/// Get the affine x-coordinate of a point as a field element.
/// Returns `[0,0,0,0]` for the point at infinity.
pub fn point_affine_x(p: &P256Point) -> P256FieldElement {
    if point_is_identity(p) {
        return [0, 0, 0, 0];
    }
    let z_inv = fp_inv(p.z);
    let z_inv_sq = fp_sq(z_inv);
    fp_mul(p.x, z_inv_sq)
}

/// Get the affine y-coordinate of a point as a field element.
pub fn point_affine_y(p: &P256Point) -> P256FieldElement {
    if point_is_identity(p) {
        return [0, 0, 0, 0];
    }
    let z_inv = fp_inv(p.z);
    let z_inv_cu = fp_mul(fp_sq(z_inv), z_inv);
    fp_mul(p.y, z_inv_cu)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Base point times 1 should give the base point.
    #[test]
    fn test_base_mult_by_one() {
        let mut k = [0u8; 32];
        k[31] = 1; // scalar = 1, big-endian

        let result = base_mult(&k);
        let enc = point_to_uncompressed(&result);

        let gx_bytes = fp_to_bytes(P256_GX);
        let gy_bytes = fp_to_bytes(P256_GY);

        assert_eq!(enc[0], 0x04);
        let mut i = 0;
        while i < 32 {
            assert_eq!(enc[1 + i], gx_bytes[i], "x mismatch at byte {}", i);
            assert_eq!(enc[33 + i], gy_bytes[i], "y mismatch at byte {}", i);
            i += 1;
        }
    }

    /// Verify that G + G == 2*G.
    #[test]
    fn test_double_equals_add() {
        let g = base_point();
        let sum = point_add(&g, &g);
        let dbl = point_double(&g);

        let enc_sum = point_to_uncompressed(&sum);
        let enc_dbl = point_to_uncompressed(&dbl);
        assert_eq!(enc_sum, enc_dbl);
    }

    /// Verify 2*G matches known coordinates.
    /// 2*G for P-256 (verified on-curve with Python):
    /// x = 0x7CF27B188D034F7E8A52380304B51AC3C08969E277F21B35A60B48FC47669978
    /// y = 0x07775510DB8ED040293D9AC69F7430DBBA7DADE63CE982299E04B79D227873D1
    #[test]
    fn test_double_base_point() {
        let g = base_point();
        let two_g = point_double(&g);
        let enc = point_to_uncompressed(&two_g);

        let expected_x: [u8; 32] = [
            0x7C, 0xF2, 0x7B, 0x18, 0x8D, 0x03, 0x4F, 0x7E,
            0x8A, 0x52, 0x38, 0x03, 0x04, 0xB5, 0x1A, 0xC3,
            0xC0, 0x89, 0x69, 0xE2, 0x77, 0xF2, 0x1B, 0x35,
            0xA6, 0x0B, 0x48, 0xFC, 0x47, 0x66, 0x99, 0x78,
        ];
        let expected_y: [u8; 32] = [
            0x07, 0x77, 0x55, 0x10, 0xDB, 0x8E, 0xD0, 0x40,
            0x29, 0x3D, 0x9A, 0xC6, 0x9F, 0x74, 0x30, 0xDB,
            0xBA, 0x7D, 0xAD, 0xE6, 0x3C, 0xE9, 0x82, 0x29,
            0x9E, 0x04, 0xB7, 0x9D, 0x22, 0x78, 0x73, 0xD1,
        ];

        assert_eq!(enc[0], 0x04);
        let mut i = 0;
        while i < 32 {
            assert_eq!(enc[1 + i], expected_x[i], "x mismatch at byte {}", i);
            assert_eq!(enc[33 + i], expected_y[i], "y mismatch at byte {}", i);
            i += 1;
        }
    }

    /// Field arithmetic: a * a^(-1) == 1.
    #[test]
    fn test_fp_inv() {
        let a: P256FieldElement = [
            0x1234567890ABCDEF,
            0xFEDCBA0987654321,
            0x0011223344556677,
            0x8899AABBCCDDEEFF,
        ];
        let a_inv = fp_inv(a);
        let prod = fp_mul(a, a_inv);
        assert_eq!(prod, [0, 0, 0, 1]);
    }

    /// Scalar field: a * a^(-1) == 1 mod n.
    #[test]
    fn test_fn_inv() {
        let a: P256FieldElement = [0, 0, 0, 42];
        let a_inv = fn_inv(a);
        let prod = fn_mul(a, a_inv);
        assert_eq!(prod, [0, 0, 0, 1]);
    }

    /// Round-trip: encode then decode.
    #[test]
    fn test_point_roundtrip() {
        let g = base_point();
        let enc = point_to_uncompressed(&g);
        let dec = point_from_uncompressed(&enc).unwrap();
        let re_enc = point_to_uncompressed(&dec);
        assert_eq!(enc, re_enc);
    }

    /// Identity + G = G.
    #[test]
    fn test_add_identity() {
        let g = base_point();
        let id = point_identity();
        let sum = point_add(&id, &g);
        let enc_sum = point_to_uncompressed(&sum);
        let enc_g = point_to_uncompressed(&g);
        assert_eq!(enc_sum, enc_g);
    }

}

#[cfg(test)]
mod reduce_mod_p_carry_tests {
    use super::{fp_from_bytes, fp_mul, fp_to_bytes};

    /// Products for which the reduction's `±p` corrections do not wrap the
    /// 256-bit value, so a correction that changes the top carry by one
    /// regardless of the carry or borrow out is off by `2^256 mod p`.
    const CASES: [(&str, &str, &str); 3] = [
        (
            "0000000000003e3aeb4ae1383562f4b82261d969f7ac94ca4000000000000000",
            "ffffffff00000001000000000000000000000000fffffffffffffffffffffff5",
            "fffffffefffd91b3cf1333cdea2270cea82d81dd534230197fffffffffffffff",
        ),
        (
            "686b95dcf6d5d8c635d93577acc71d72b4586b734e04cc37a32794af9a2f0315",
            "00000000000000000000000000109b608ff6c973d65b7511e36685291eeb9840",
            "ffffffff00000001000000000000000000000000ffffffff61c8864680b583ea",
        ),
        (
            "44e4a1a6f6c8338ac1b05ff7efab0b9acce5dfbdaf9de3f33392548d4e2f0aa1",
            "000000000000000000000000057a6d688fe7a5f3ef14ab2a124e4849b3eeb840",
            "ffffffff00000001000000000000000000000000fffffffbac7babed84f69b6c",
        ),
    ];

    fn nibble(c: u8) -> u8 {
        match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            _ => panic!("hex"),
        }
    }

    fn from_hex(s: &str) -> [u8; 32] {
        let b = s.as_bytes();
        let mut out = [0u8; 32];
        for i in 0..32 {
            out[i] = (nibble(b[2 * i]) << 4) | nibble(b[2 * i + 1]);
        }
        out
    }

    fn to_hex(b: [u8; 32]) -> String {
        b.iter().map(|x| format!("{:02x}", x)).collect()
    }

    #[test]
    fn products_whose_corrections_do_not_wrap() {
        for (a, b, ab) in CASES.iter() {
            let x = fp_from_bytes(&from_hex(a));
            let y = fp_from_bytes(&from_hex(b));
            assert_eq!(to_hex(fp_to_bytes(fp_mul(x, y))), *ab, "a = {a}");
            assert_eq!(to_hex(fp_to_bytes(fp_mul(y, x))), *ab, "a = {a}");
        }
    }
}
