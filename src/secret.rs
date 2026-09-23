//! Secret value types.
//!
//! A value that must not influence control flow or memory access is given a
//! secret type at its binding. The extraction records the names of such
//! bindings, and the compiler's constant-time check rejects a branch, a loop
//! guard or a memory index that depends on one.

/// A secret 32-byte little-endian scalar.
///
/// The bytes leave the type only through [`Scalar::declassify`].
#[derive(Clone, Copy)]
pub struct Scalar(pub(crate) [u8; 32]);

impl Scalar {
    /// A public byte string as a secret scalar.
    pub fn from_bytes_secret(bytes: [u8; 32]) -> Self {
        Scalar(bytes)
    }

    /// The bytes of the scalar as a public value. Each call is a point at which
    /// the secret is released and is reviewed as such.
    pub fn declassify(self) -> [u8; 32] {
        self.0
    }
}
