//! Pure Rust ECDSA with P-256 and SHA-256 specification (FIPS 186-4).
//!
//! Uses `crate::p256` for elliptic curve operations and `crate::sha256` for
//! hashing. No external dependencies.
//!
//! All functions are pure and value-passing.

use crate::p256::{
    base_mult, fn_add, fn_from_bytes, fn_inv, fn_mul, fp_from_bytes, fp_to_bytes,
    point_add, point_affine_x, point_is_identity, scalar_mult, P256FieldElement,
    P256Point, P256_N,
};
use crate::sha256::sha256;

/// Check if a scalar (mod n) is zero.
fn is_zero(a: &P256FieldElement) -> bool {
    a[0] == 0 && a[1] == 0 && a[2] == 0 && a[3] == 0
}

/// Compare two 256-bit big-endian numbers. Returns true if a >= b.
fn ge256(a: &P256FieldElement, b: &P256FieldElement) -> bool {
    let mut i = 0;
    while i < 4 {
        if a[i] > b[i] {
            return true;
        }
        if a[i] < b[i] {
            return false;
        }
        i += 1;
    }
    true // equal
}

/// Reduce a field element mod n (the curve order).
/// If a >= n, subtract n.
fn reduce_mod_n(a: P256FieldElement) -> P256FieldElement {
    if ge256(&a, &P256_N) {
        let mut r = [0u64; 4];
        let mut borrow: u128 = 0;
        let mut i: usize = 4;
        while i > 0 {
            i -= 1;
            let s = (a[i] as u128).wrapping_sub(P256_N[i] as u128).wrapping_sub(borrow);
            r[i] = s as u64;
            borrow = (s >> 127) & 1;
        }
        r
    } else {
        a
    }
}

/// ECDSA P-256 signature generation (FIPS 186-4, Section 6.4).
///
/// Input:
/// - `secret_key`: 32-byte big-endian private key d.
/// - `msg`: arbitrary-length message.
/// - `k_random`: 32-byte big-endian random nonce k (must be in [1, n-1]).
///
/// Output:
/// - `Some([u8; 64])` containing r || s (each 32 bytes, big-endian).
/// - `None` if r == 0 or s == 0.
///
/// Steps:
/// 1. e = SHA-256(msg)
/// 2. (x1, _) = k * G
/// 3. r = x1 mod n (return None if r == 0)
/// 4. s = k^(-1) * (e + r * d) mod n (return None if s == 0)
/// 5. Return r || s
pub fn ecdsa_p256_sign(
    secret_key: &[u8; 32],
    msg: &[u8],
    k_random: &[u8; 32],
) -> Option<[u8; 64]> {
    // Parse private key d.
    let d = fn_from_bytes(secret_key);

    // Parse nonce k.
    let k = fn_from_bytes(k_random);
    if is_zero(&k) {
        return None;
    }

    // Compute hash e = SHA-256(msg).
    let e_hash = sha256(msg);
    let e = fn_from_bytes(&e_hash);

    // Compute (x1, _) = k * G.
    let kg = base_mult(k_random);
    if point_is_identity(&kg) {
        return None;
    }

    // r = x1 mod n.
    let x1 = point_affine_x(&kg);
    let r = reduce_mod_n(x1);
    if is_zero(&r) {
        return None;
    }

    // s = k^(-1) * (e + r * d) mod n.
    let k_inv = fn_inv(k);
    let rd = fn_mul(r, d);
    let e_rd = fn_add(e, rd);
    let s = fn_mul(k_inv, e_rd);
    if is_zero(&s) {
        return None;
    }

    // Encode r || s as 64 bytes (big-endian).
    let mut sig = [0u8; 64];
    let r_bytes = fp_to_bytes(r);
    let s_bytes = fp_to_bytes(s);
    let mut i = 0;
    while i < 32 {
        sig[i] = r_bytes[i];
        sig[32 + i] = s_bytes[i];
        i += 1;
    }

    Some(sig)
}

/// ECDSA P-256 signature verification (FIPS 186-4, Section 6.4).
///
/// Input:
/// - `public_key`: 65-byte uncompressed public key (0x04 || x || y).
/// - `msg`: arbitrary-length message.
/// - `signature`: 64-byte signature (r || s, each 32 bytes big-endian).
///
/// Output: true if the signature is valid.
///
/// Steps:
/// 1. e = SHA-256(msg) as integer mod n
/// 2. r, s = decode signature
/// 3. Check 1 <= r, s < n
/// 4. w = s^(-1) mod n
/// 5. u1 = e * w mod n, u2 = r * w mod n
/// 6. (x1, _) = u1 * G + u2 * Q
/// 7. Check x1 mod n == r
pub fn ecdsa_p256_verify(
    public_key: &[u8; 65],
    msg: &[u8],
    signature: &[u8; 64],
) -> bool {
    // Decode public key.
    if public_key[0] != 0x04 {
        return false;
    }
    let mut qx_bytes = [0u8; 32];
    let mut qy_bytes = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        qx_bytes[i] = public_key[1 + i];
        qy_bytes[i] = public_key[33 + i];
        i += 1;
    }
    let qx = fp_from_bytes(&qx_bytes);
    let qy = fp_from_bytes(&qy_bytes);
    let q = P256Point {
        x: qx,
        y: qy,
        z: [0, 0, 0, 1],
    };

    // Decode r and s.
    let mut r_bytes = [0u8; 32];
    let mut s_bytes = [0u8; 32];
    i = 0;
    while i < 32 {
        r_bytes[i] = signature[i];
        s_bytes[i] = signature[32 + i];
        i += 1;
    }
    let r = fp_from_bytes(&r_bytes);
    let s = fp_from_bytes(&s_bytes);

    // Check 1 <= r, s < n.
    if is_zero(&r) || is_zero(&s) {
        return false;
    }
    if ge256(&r, &P256_N) {
        return false;
    }
    if ge256(&s, &P256_N) {
        return false;
    }

    // Compute hash e = SHA-256(msg).
    let e_hash = sha256(msg);
    let e = fn_from_bytes(&e_hash);

    // w = s^(-1) mod n.
    let w = fn_inv(s);

    // u1 = e * w mod n.
    let u1 = fn_mul(e, w);

    // u2 = r * w mod n.
    let u2 = fn_mul(r, w);

    // Compute u1 * G + u2 * Q.
    let u1_bytes = fp_to_bytes(u1);
    let u2_bytes = fp_to_bytes(u2);
    let u1g = base_mult(&u1_bytes);
    let u2q = scalar_mult(&u2_bytes, &q);
    let point = point_add(&u1g, &u2q);

    if point_is_identity(&point) {
        return false;
    }

    // Check x1 mod n == r.
    let x1 = point_affine_x(&point);
    let x1_mod_n = reduce_mod_n(x1);

    x1_mod_n == r
}

/// Derive the ECDSA P-256 public key from a secret key.
///
/// Returns the 65-byte uncompressed encoding (0x04 || x || y).
pub fn ecdsa_p256_public_key(secret_key: &[u8; 32]) -> [u8; 65] {
    let pk_point = base_mult(secret_key);
    crate::p256::point_to_uncompressed(&pk_point)
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

    /// Self-consistency: sign then verify with a known private key and nonce.
    #[test]
    fn test_sign_verify_roundtrip() {
        // Use a simple test key and nonce.
        // Private key d = 1 (big-endian 32 bytes).
        let mut sk = [0u8; 32];
        sk[31] = 1;

        // Public key = 1 * G = G.
        let pk = ecdsa_p256_public_key(&sk);

        // Nonce k = 2.
        let mut k = [0u8; 32];
        k[31] = 2;

        let msg = b"test message";
        let sig = ecdsa_p256_sign(&sk, msg, &k).expect("signing should succeed");

        assert!(
            ecdsa_p256_verify(&pk, msg, &sig),
            "verification should succeed"
        );
    }

    /// Verify with a wrong message should fail.
    #[test]
    fn test_verify_wrong_message() {
        let mut sk = [0u8; 32];
        sk[31] = 1;
        let pk = ecdsa_p256_public_key(&sk);

        let mut k = [0u8; 32];
        k[31] = 2;

        let msg = b"correct message";
        let sig = ecdsa_p256_sign(&sk, msg, &k).expect("signing should succeed");

        let wrong_msg = b"wrong message";
        assert!(
            !ecdsa_p256_verify(&pk, wrong_msg, &sig),
            "verification should fail for wrong message"
        );
    }

    /// Verify with a wrong public key should fail.
    #[test]
    fn test_verify_wrong_key() {
        let mut sk = [0u8; 32];
        sk[31] = 1;

        // Different key: d = 3.
        let mut sk2 = [0u8; 32];
        sk2[31] = 3;
        let pk2 = ecdsa_p256_public_key(&sk2);

        let mut k = [0u8; 32];
        k[31] = 2;

        let msg = b"test";
        let sig = ecdsa_p256_sign(&sk, msg, &k).expect("signing should succeed");

        assert!(
            !ecdsa_p256_verify(&pk2, msg, &sig),
            "verification should fail with wrong key"
        );
    }

    /// The public key for d=1 should be the base point G.
    #[test]
    fn test_public_key_d1() {
        let mut sk = [0u8; 32];
        sk[31] = 1;
        let pk = ecdsa_p256_public_key(&sk);

        // pk should be 0x04 || Gx || Gy.
        assert_eq!(pk[0], 0x04);

        let expected_gx = crate::p256::fp_to_bytes(crate::p256::P256_GX);
        let expected_gy = crate::p256::fp_to_bytes(crate::p256::P256_GY);

        let mut i = 0;
        while i < 32 {
            assert_eq!(pk[1 + i], expected_gx[i], "Gx mismatch at byte {}", i);
            assert_eq!(pk[33 + i], expected_gy[i], "Gy mismatch at byte {}", i);
            i += 1;
        }
    }

    /// ECDSA P-256 / SHA-256 test vector from RFC 6979, Appendix A.2.5
    /// (deterministic nonce; message "sample").
    ///
    /// Private key d:
    ///   C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
    /// Nonce k:
    ///   A6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60
    /// Message: "sample"
    /// Expected r:
    ///   EFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716
    /// Expected s:
    ///   F7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8
    #[test]
    fn test_nist_vector() {
        let sk = hex_to_32(
            "C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721",
        );
        let k = hex_to_32(
            "A6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60",
        );
        let msg = b"sample";

        let sig = ecdsa_p256_sign(&sk, msg, &k).expect("signing should succeed");

        let expected_r = hex_to_32(
            "EFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716",
        );
        let expected_s = hex_to_32(
            "F7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8",
        );

        let mut r_got = [0u8; 32];
        let mut s_got = [0u8; 32];
        let mut i = 0;
        while i < 32 {
            r_got[i] = sig[i];
            s_got[i] = sig[32 + i];
            i += 1;
        }

        assert_eq!(r_got, expected_r, "r mismatch");
        assert_eq!(s_got, expected_s, "s mismatch");

        // Verify the signature.
        let pk = ecdsa_p256_public_key(&sk);
        assert!(ecdsa_p256_verify(&pk, msg, &sig));
    }
}
