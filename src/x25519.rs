//! X25519 (RFC 7748), backed by real Curve25519 field arithmetic.
//!
//! Delegates to `curve25519.rs` (pure hacspec-style spec copied from
//! libcrux-lean-specs, differential-tested against libcrux-curve25519).

use crate::curve25519;

/// X25519 scalar multiplication: compute scalar * point on Curve25519.
pub fn scalarmult(scalar: [u8; 32], point: [u8; 32]) -> [u8; 32] {
    curve25519::x25519_scalarmult(&scalar, &point)
}

/// X25519 base point multiplication: compute scalar * 9.
pub fn base_mult(scalar: [u8; 32]) -> [u8; 32] {
    curve25519::x25519_base(&scalar)
}
