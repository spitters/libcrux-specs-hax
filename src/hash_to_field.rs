//! Pure Rust `expand_message_xmd` and `hash_to_field` specification (RFC 9380).
//!
//! - `expand_message_xmd_sha256` / `expand_message_xmd_sha512`: RFC 9380,
//!   Section 5.3.1, with H = SHA-256 (b_in_bytes = 32, s_in_bytes = 64) and
//!   H = SHA-512 (b_in_bytes = 64, s_in_bytes = 128). The ABORT of step 2 is
//!   the result `None`.
//! - `dst_oversize_sha256` / `dst_oversize_sha512`: the short domain
//!   separation tag of RFC 9380, Section 5.3.3.
//! - `hash_to_field_25519_sha512` / `hash_to_field_p256_sha256`: RFC 9380,
//!   Section 5.2, for extension degree m = 1 and L = 48, over
//!   GF(2^255 - 19) (curve25519 and edwards25519 suites, Section 8.5) and the
//!   P-256 base field (Section 8.2).
//!
//! The text of `expand_message_xmd` and `hash_to_field` is adapted from the
//! hacspec examples `edwards25519-hash` and `bls12-381-hash`
//! (<https://github.com/hacspec/hacspec>, MIT OR Apache-2.0; Malte Thomsen,
//! Marcus Rasmussen, Tobias Vestergaard and the hacspec authors), rewritten
//! over this crate's hash functions and field representations.
//!
//! No external dependencies. All functions are pure and value-passing.

use alloc::vec::Vec;

use crate::curve25519::{fe_add, fe_from_bytes, fe_mul, fe_reduce};
use crate::p256::{fp_add, fp_from_bytes, fp_mul, P256FieldElement};
use crate::sha256::sha256;
use crate::sha512::sha512;

/// Largest DST length accepted by `expand_message_xmd` (RFC 9380, Section 5.3.1, step 2).
pub const MAX_DST_LEN: usize = 255;

/// Largest `len_in_bytes` accepted by `expand_message_xmd` (RFC 9380, Section 5.3.1, step 2).
pub const MAX_LEN_IN_BYTES: usize = 65535;

/// Largest block count `ell` accepted by `expand_message_xmd` (RFC 9380, Section 5.3.1, step 2).
pub const MAX_ELL: usize = 255;

/// SHA-256 output length b_in_bytes.
pub const SHA256_B_IN_BYTES: usize = 32;

/// SHA-256 input block length s_in_bytes.
pub const SHA256_S_IN_BYTES: usize = 64;

/// SHA-512 output length b_in_bytes.
pub const SHA512_B_IN_BYTES: usize = 64;

/// SHA-512 input block length s_in_bytes.
pub const SHA512_S_IN_BYTES: usize = 128;

/// The length L of RFC 9380, Section 5.2, for a 255- or 256-bit prime and
/// k = 128: L = ceil((ceil(log2(p)) + k) / 8) = 48.
pub const L_48: usize = 48;

/// The ASCII string "H2C-OVERSIZE-DST-" (RFC 9380, Section 5.3.3).
pub const OVERSIZE_DST_PREFIX: [u8; 17] = [
    0x48, 0x32, 0x43, 0x2d, 0x4f, 0x56, 0x45, 0x52, 0x53, 0x49, 0x5a, 0x45, 0x2d, 0x44, 0x53,
    0x54, 0x2d,
];

// --- Byte-string helpers ---

/// `v || s`.
fn append(v: Vec<u8>, s: &[u8]) -> Vec<u8> {
    let mut r = v;
    for i in 0..s.len() {
        r.push(s[i]);
    }
    r
}

/// `v || I2OSP(0, n)`.
fn append_zeros(v: Vec<u8>, n: usize) -> Vec<u8> {
    let mut r = v;
    for _i in 0..n {
        r.push(0u8);
    }
    r
}

/// DST_prime = DST || I2OSP(len(DST), 1) (RFC 9380, Section 5.3.1, step 3).
///
/// The length byte is `len(DST) mod 256`; it equals `len(DST)` for a DST of
/// at most `MAX_DST_LEN` bytes.
pub fn build_dst_prime(dst: &[u8]) -> Vec<u8> {
    let mut r = append(Vec::new(), dst);
    r.push((dst.len() & 0xff) as u8);
    r
}

/// msg_prime = Z_pad || msg || I2OSP(len_in_bytes, 2) || I2OSP(0, 1) || DST_prime
/// (RFC 9380, Section 5.3.1, steps 4 to 6), for a hash with input block
/// length `s_in_bytes`.
fn build_msg_prime(s_in_bytes: usize, msg: &[u8], len_in_bytes: usize, dst_prime: &[u8]) -> Vec<u8> {
    let mut r = append_zeros(Vec::new(), s_in_bytes);
    r = append(r, msg);
    r.push(((len_in_bytes >> 8) & 0xff) as u8);
    r.push((len_in_bytes & 0xff) as u8);
    r.push(0u8);
    append(r, dst_prime)
}

// --- Section 5.3.3: domain separation tags longer than 255 bytes ---

/// DST = SHA-256("H2C-OVERSIZE-DST-" || a_very_long_DST) (RFC 9380, Section 5.3.3).
pub fn dst_oversize_sha256(long_dst: &[u8]) -> [u8; 32] {
    let mut input = append(Vec::new(), &OVERSIZE_DST_PREFIX);
    input = append(input, long_dst);
    sha256(&input)
}

/// DST = SHA-512("H2C-OVERSIZE-DST-" || a_very_long_DST) (RFC 9380, Section 5.3.3).
pub fn dst_oversize_sha512(long_dst: &[u8]) -> [u8; 64] {
    let mut input = append(Vec::new(), &OVERSIZE_DST_PREFIX);
    input = append(input, long_dst);
    sha512(&input)
}

// --- Section 5.3.1: expand_message_xmd ---

/// Steps 3 to 12 of `expand_message_xmd` with H = SHA-256, for arguments that
/// pass step 2 and `ell = ceil(len_in_bytes / 32)`.
fn expand_message_xmd_sha256_steps(
    msg: &[u8],
    dst: &[u8],
    len_in_bytes: usize,
    ell: usize,
) -> Vec<u8> {
    // Step 3.
    let dst_prime = build_dst_prime(dst);
    // Steps 4 to 6.
    let msg_prime = build_msg_prime(SHA256_S_IN_BYTES, msg, len_in_bytes, &dst_prime);
    // Step 7: b_0 = H(msg_prime).
    let b_0 = sha256(&msg_prime);
    // Step 8: b_1 = H(b_0 || I2OSP(1, 1) || DST_prime).
    let mut b_1_input = append(Vec::new(), &b_0);
    b_1_input.push(1u8);
    b_1_input = append(b_1_input, &dst_prime);
    let mut b_prev = sha256(&b_1_input);
    let mut uniform_bytes = append(Vec::new(), &b_prev);
    // Steps 9 and 10: b_i = H(strxor(b_0, b_(i - 1)) || I2OSP(i, 1) || DST_prime).
    for i in 2..(ell + 1) {
        let mut b_i_input = Vec::new();
        for j in 0..SHA256_B_IN_BYTES {
            b_i_input.push(b_0[j] ^ b_prev[j]);
        }
        b_i_input.push((i & 0xff) as u8);
        b_i_input = append(b_i_input, &dst_prime);
        b_prev = sha256(&b_i_input);
        // Step 11: uniform_bytes = b_1 || ... || b_ell.
        uniform_bytes = append(uniform_bytes, &b_prev);
    }
    // Step 12: substr(uniform_bytes, 0, len_in_bytes).
    let mut out = Vec::new();
    for i in 0..len_in_bytes {
        out.push(uniform_bytes[i]);
    }
    out
}

/// `expand_message_xmd(msg, DST, len_in_bytes)` with H = SHA-256
/// (RFC 9380, Section 5.3.1).
///
/// Returns `None` exactly when step 2 aborts: `ell > 255`, or
/// `len_in_bytes > 65535`, or `len(DST) > 255`. This function does not apply
/// Section 5.3.3; `expand_message_xmd_sha256_long_dst` does.
pub fn expand_message_xmd_sha256(msg: &[u8], dst: &[u8], len_in_bytes: usize) -> Option<Vec<u8>> {
    if len_in_bytes > MAX_LEN_IN_BYTES || dst.len() > MAX_DST_LEN {
        None
    } else {
        // Step 1: ell = ceil(len_in_bytes / b_in_bytes).
        let ell = (len_in_bytes + SHA256_B_IN_BYTES - 1) / SHA256_B_IN_BYTES;
        if ell > MAX_ELL {
            None
        } else {
            Some(expand_message_xmd_sha256_steps(msg, dst, len_in_bytes, ell))
        }
    }
}

/// `expand_message_xmd` with H = SHA-256 for a DST of any length: a DST
/// longer than 255 bytes is replaced by `dst_oversize_sha256(DST)`
/// (RFC 9380, Section 5.3.3), and a shorter one is used as given.
///
/// Returns `None` exactly when `ell > 255` or `len_in_bytes > 65535`.
pub fn expand_message_xmd_sha256_long_dst(
    msg: &[u8],
    dst: &[u8],
    len_in_bytes: usize,
) -> Option<Vec<u8>> {
    if dst.len() > MAX_DST_LEN {
        let short_dst = dst_oversize_sha256(dst);
        expand_message_xmd_sha256(msg, &short_dst, len_in_bytes)
    } else {
        expand_message_xmd_sha256(msg, dst, len_in_bytes)
    }
}

/// Steps 3 to 12 of `expand_message_xmd` with H = SHA-512, for arguments that
/// pass step 2 and `ell = ceil(len_in_bytes / 64)`.
fn expand_message_xmd_sha512_steps(
    msg: &[u8],
    dst: &[u8],
    len_in_bytes: usize,
    ell: usize,
) -> Vec<u8> {
    // Step 3.
    let dst_prime = build_dst_prime(dst);
    // Steps 4 to 6.
    let msg_prime = build_msg_prime(SHA512_S_IN_BYTES, msg, len_in_bytes, &dst_prime);
    // Step 7: b_0 = H(msg_prime).
    let b_0 = sha512(&msg_prime);
    // Step 8: b_1 = H(b_0 || I2OSP(1, 1) || DST_prime).
    let mut b_1_input = append(Vec::new(), &b_0);
    b_1_input.push(1u8);
    b_1_input = append(b_1_input, &dst_prime);
    let mut b_prev = sha512(&b_1_input);
    let mut uniform_bytes = append(Vec::new(), &b_prev);
    // Steps 9 and 10: b_i = H(strxor(b_0, b_(i - 1)) || I2OSP(i, 1) || DST_prime).
    for i in 2..(ell + 1) {
        let mut b_i_input = Vec::new();
        for j in 0..SHA512_B_IN_BYTES {
            b_i_input.push(b_0[j] ^ b_prev[j]);
        }
        b_i_input.push((i & 0xff) as u8);
        b_i_input = append(b_i_input, &dst_prime);
        b_prev = sha512(&b_i_input);
        // Step 11: uniform_bytes = b_1 || ... || b_ell.
        uniform_bytes = append(uniform_bytes, &b_prev);
    }
    // Step 12: substr(uniform_bytes, 0, len_in_bytes).
    let mut out = Vec::new();
    for i in 0..len_in_bytes {
        out.push(uniform_bytes[i]);
    }
    out
}

/// `expand_message_xmd(msg, DST, len_in_bytes)` with H = SHA-512
/// (RFC 9380, Section 5.3.1).
///
/// Returns `None` exactly when step 2 aborts: `ell > 255`, or
/// `len_in_bytes > 65535`, or `len(DST) > 255`. This function does not apply
/// Section 5.3.3; `expand_message_xmd_sha512_long_dst` does.
pub fn expand_message_xmd_sha512(msg: &[u8], dst: &[u8], len_in_bytes: usize) -> Option<Vec<u8>> {
    if len_in_bytes > MAX_LEN_IN_BYTES || dst.len() > MAX_DST_LEN {
        None
    } else {
        // Step 1: ell = ceil(len_in_bytes / b_in_bytes).
        let ell = (len_in_bytes + SHA512_B_IN_BYTES - 1) / SHA512_B_IN_BYTES;
        if ell > MAX_ELL {
            None
        } else {
            Some(expand_message_xmd_sha512_steps(msg, dst, len_in_bytes, ell))
        }
    }
}

/// `expand_message_xmd` with H = SHA-512 for a DST of any length: a DST
/// longer than 255 bytes is replaced by `dst_oversize_sha512(DST)`
/// (RFC 9380, Section 5.3.3), and a shorter one is used as given.
///
/// Returns `None` exactly when `ell > 255` or `len_in_bytes > 65535`.
pub fn expand_message_xmd_sha512_long_dst(
    msg: &[u8],
    dst: &[u8],
    len_in_bytes: usize,
) -> Option<Vec<u8>> {
    if dst.len() > MAX_DST_LEN {
        let short_dst = dst_oversize_sha512(dst);
        expand_message_xmd_sha512(msg, &short_dst, len_in_bytes)
    } else {
        expand_message_xmd_sha512(msg, dst, len_in_bytes)
    }
}

// --- OS2IP(tv) mod p for L = 48 ---

/// OS2IP(tv) mod (2^255 - 19) for a 48-byte big-endian string `tv`
/// (RFC 9380, Section 5.2, step 7), as a canonical radix-2^51 field element.
///
/// With `hi = OS2IP(tv[0..24])` and `lo = OS2IP(tv[24..48])`, both below
/// 2^192, the value is `hi * 2^192 + lo`; 2^192 = 2^39 * 2^153 is the field
/// element with limb 3 equal to 2^39.
pub fn fe25519_from_be48(tv: &[u8; 48]) -> [u64; 5] {
    let mut hi_le = [0u8; 32];
    let mut lo_le = [0u8; 32];
    for i in 0..24 {
        hi_le[i] = tv[23 - i];
        lo_le[i] = tv[47 - i];
    }
    let hi = fe_from_bytes(&hi_le);
    let lo = fe_from_bytes(&lo_le);
    let two_192: [u64; 5] = [0, 0, 0, 1u64 << 39, 0];
    fe_reduce(fe_add(fe_mul(hi, two_192), lo))
}

/// 2^256 mod p for the P-256 prime p = 2^256 - 2^224 + 2^192 + 2^96 - 1,
/// that is 2^224 - 2^192 - 2^96 + 1, in the big-endian limb order of
/// `P256FieldElement`.
pub const P256_TWO_256: P256FieldElement = [
    0x00000000FFFFFFFE,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFF00000000,
    0x0000000000000001,
];

/// OS2IP(tv) mod p for the P-256 prime and a 48-byte big-endian string `tv`
/// (RFC 9380, Section 5.2, step 7), as a canonical `P256FieldElement`.
///
/// With `hi = OS2IP(tv[0..16])` and `lo = OS2IP(tv[16..48])`, the value is
/// `hi * 2^256 + lo`. `fp_add(lo, 0)` reduces `lo < 2^256 < 2 * p` to its
/// canonical representative.
pub fn fp256_from_be48(tv: &[u8; 48]) -> P256FieldElement {
    let mut hi_be = [0u8; 32];
    let mut lo_be = [0u8; 32];
    for i in 0..16 {
        hi_be[16 + i] = tv[i];
    }
    for i in 0..32 {
        lo_be[i] = tv[16 + i];
    }
    let hi = fp_from_bytes(&hi_be);
    let lo = fp_add(fp_from_bytes(&lo_be), [0, 0, 0, 0]);
    fp_add(fp_mul(hi, P256_TWO_256), lo)
}

/// tv = substr(uniform_bytes, L * i, L) for L = 48
/// (RFC 9380, Section 5.2, steps 5 and 6, with m = 1 and j = 0).
fn substr_48(uniform_bytes: &[u8], i: usize) -> [u8; 48] {
    let mut tv = [0u8; 48];
    for j in 0..L_48 {
        tv[j] = uniform_bytes[L_48 * i + j];
    }
    tv
}

// --- Section 5.2: hash_to_field ---

/// `hash_to_field(msg, count)` of RFC 9380, Section 5.2, with
/// F = GF(2^255 - 19), m = 1, L = 48 and
/// expand_message = `expand_message_xmd_sha512`: the parameters of the
/// curve25519 and edwards25519 suites (Section 8.5). Each output is a
/// canonical radix-2^51 field element of `crate::curve25519`.
///
/// Returns `None` exactly when `expand_message_xmd_sha512(msg, DST, count * 48)`
/// aborts, that is when `count > 340` or `len(DST) > 255`.
pub fn hash_to_field_25519_sha512(msg: &[u8], dst: &[u8], count: usize) -> Option<Vec<[u64; 5]>> {
    if count > MAX_LEN_IN_BYTES / L_48 {
        None
    } else {
        // Step 1: len_in_bytes = count * m * L.
        let len_in_bytes = count * L_48;
        // Step 2.
        match expand_message_xmd_sha512(msg, dst, len_in_bytes) {
            None => None,
            Some(uniform_bytes) => {
                let mut u = Vec::new();
                // Steps 3 to 8.
                for i in 0..count {
                    let tv = substr_48(&uniform_bytes, i);
                    u.push(fe25519_from_be48(&tv));
                }
                Some(u)
            }
        }
    }
}

/// `hash_to_field(msg, count)` of RFC 9380, Section 5.2, with F the P-256
/// base field, m = 1, L = 48 and expand_message = `expand_message_xmd_sha256`:
/// the parameters of the P-256 suites (Section 8.2). Each output is a
/// canonical `P256FieldElement`.
///
/// Returns `None` exactly when `expand_message_xmd_sha256(msg, DST, count * 48)`
/// aborts, that is when `count > 170` or `len(DST) > 255`.
pub fn hash_to_field_p256_sha256(
    msg: &[u8],
    dst: &[u8],
    count: usize,
) -> Option<Vec<P256FieldElement>> {
    if count > MAX_LEN_IN_BYTES / L_48 {
        None
    } else {
        // Step 1: len_in_bytes = count * m * L.
        let len_in_bytes = count * L_48;
        // Step 2.
        match expand_message_xmd_sha256(msg, dst, len_in_bytes) {
            None => None,
            Some(uniform_bytes) => {
                let mut u = Vec::new();
                // Steps 3 to 8.
                for i in 0..count {
                    let tv = substr_48(&uniform_bytes, i);
                    u.push(fp256_from_be48(&tv));
                }
                Some(u)
            }
        }
    }
}
