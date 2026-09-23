//! Fixed-base comb scalar multiplication on Edwards25519, in radix 16.
//!
//! `comb_walk` computes `k · B` for a 32-byte little-endian scalar `k` by one
//! table lookup and one point addition per 4-bit digit: sixty-four windows, a
//! row of sixteen entries each, row `i` holding the multiples `(d · 16^i) · B`.
//! The lookup is a full scan of the row, so the sequence of memory accesses is
//! the same whatever the digit is.
//!
//! Every function here is pure and value-passing, over `edwards25519`'s point
//! operations, and mirrors a Lean definition one for one:
//!
//! | here | `CatCrypt.Crypto.EdDSA.FixedBaseComb` |
//! |---|---|
//! | `comb_digit` | `combDigit k i = k / 16^i % 16` |
//! | `comb_row` | `combRow B i = (List.range 16).map (fun d => (d * 16^i) • B)` |
//! | `comb_select` | `combSelect T i d = ctScanSelect (T.getD i []) d` |
//! | `comb_walk` | `combMul (combTable B) k = combTrips (combTable B) k 64` |
//!
//! `combMul_correct` gives `combMul (combTable B) k = k • B` for `k < 2^256`,
//! which is the statement `comb_walk_matches_scalar_mult` checks numerically.

use alloc::vec::Vec;

use crate::edwards25519::{point_add, point_double, point_identity, EdPoint};

/// Entries in a table row: one per value of a 4-bit digit.
pub const COMB_ENTRIES: usize = 16;

/// Rows in the table: one per digit of a 256-bit scalar.
pub const COMB_WINDOWS: usize = 64;

/// Digit `i` of the scalar in radix 16, that is `k / 16^i % 16`.
///
/// The scalar is 32 bytes little-endian, so digit `i` is a nibble of byte
/// `i / 2`: the low nibble for even `i`, the high nibble for odd `i`. The
/// index arithmetic depends on `i` alone.
pub fn comb_digit(k: &[u8; 32], i: usize) -> usize {
    let byte = k[i / 2];
    let shifted = if i % 2 == 0 { byte } else { byte >> 4 };
    (shifted & 15) as usize
}

/// `16 · p`, by four doublings.
fn point_mul16(p: &EdPoint) -> EdPoint {
    let p2 = point_double(p);
    let p4 = point_double(&p2);
    let p8 = point_double(&p4);
    point_double(&p8)
}

/// Row `i` of the comb table of `base`: the sixteen multiples
/// `(d · 16^i) · base` for `d < 16`, in order of `d`.
///
/// `weight` is `(16^i) · base`; entry `d` is the running sum of `d` copies of
/// it, so entry `0` is the identity.
fn comb_row_from_weight(weight: &EdPoint) -> Vec<EdPoint> {
    let mut row: Vec<EdPoint> = Vec::new();
    let mut acc = point_identity();
    let mut d = 0usize;
    while d < COMB_ENTRIES {
        row.push(acc);
        acc = point_add(&acc, weight);
        d += 1;
    }
    row
}

/// The comb table of `base`, row-major: entry `COMB_ENTRIES * i + d` is
/// `(d · 16^i) · base`, for `i < 64` and `d < 16`.
pub fn comb_table(base: &EdPoint) -> Vec<EdPoint> {
    let mut table: Vec<EdPoint> = Vec::new();
    let mut weight = *base;
    let mut i = 0usize;
    while i < COMB_WINDOWS {
        let row = comb_row_from_weight(&weight);
        let mut d = 0usize;
        while d < COMB_ENTRIES {
            table.push(row[d]);
            d += 1;
        }
        weight = point_mul16(&weight);
        i += 1;
    }
    table
}

/// Entry `d` of row `i`, read by a full scan of the row.
///
/// Every entry of the row is read, in order, and the accumulator keeps the one
/// whose index is `d`. The access pattern does not depend on `d`, and an out of
/// range `d` yields the identity.
pub fn comb_select(table: &[EdPoint], i: usize, d: usize) -> EdPoint {
    let mut acc = point_identity();
    let base = COMB_ENTRIES * i;
    let mut j = 0usize;
    while j < COMB_ENTRIES {
        if j == d {
            acc = table[base + j];
        }
        j += 1;
    }
    acc
}

/// `k · base` for the 32-byte little-endian scalar `k`, over the comb table of
/// `base`, by one scan and one addition per window.
///
/// The accumulator starts at the identity and window `i` adds the entry its
/// digit selects, which is `combTrips` run to sixty-four.
pub fn comb_walk(table: &[EdPoint], k: &[u8; 32]) -> EdPoint {
    let mut acc = point_identity();
    let mut i = 0usize;
    while i < COMB_WINDOWS {
        let d = comb_digit(k, i);
        let entry = comb_select(table, i, d);
        acc = point_add(&acc, &entry);
        i += 1;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edwards25519::{ed25519_base_point, point_encode, scalar_mult};
    use crate::sha512::sha512;

    /// A 32-byte scalar from a splitmix64 stream, so the cases are spread over
    /// the digit range rather than clustered at the low windows.
    fn scalar_from_seed(seed: u64) -> [u8; 32] {
        let mut k = [0u8; 32];
        let mut state = seed;
        let mut i = 0usize;
        while i < 4 {
            state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^= z >> 31;
            let bytes = z.to_le_bytes();
            let mut j = 0usize;
            while j < 8 {
                k[8 * i + j] = bytes[j];
                j += 1;
            }
            i += 1;
        }
        k
    }

    #[test]
    fn comb_digit_reconstructs_the_scalar() {
        // Σ_{i<64} digit(i) · 16^i = k, checked byte by byte: the two nibbles
        // of byte b are digits 2b and 2b+1.
        let k = scalar_from_seed(7);
        let mut b = 0usize;
        while b < 32 {
            let lo = comb_digit(&k, 2 * b);
            let hi = comb_digit(&k, 2 * b + 1);
            assert_eq!(lo + 16 * hi, k[b] as usize, "byte {b}");
            b += 1;
        }
    }

    #[test]
    fn comb_select_reads_the_row_entry() {
        let base = ed25519_base_point();
        let table = comb_table(&base);
        let mut d = 0usize;
        while d < COMB_ENTRIES {
            let got = comb_select(&table, 3, d);
            assert_eq!(
                point_encode(&got),
                point_encode(&table[COMB_ENTRIES * 3 + d]),
                "row 3, digit {d}"
            );
            d += 1;
        }
    }

    #[test]
    fn comb_walk_matches_scalar_mult() {
        let base = ed25519_base_point();
        let table = comb_table(&base);
        let mut n = 0u64;
        while n < 16 {
            let k = scalar_from_seed(n);
            let by_comb = comb_walk(&table, &k);
            let by_double_and_add = scalar_mult(&k, &base);
            assert_eq!(
                point_encode(&by_comb),
                point_encode(&by_double_and_add),
                "seed {n}"
            );
            n += 1;
        }
    }

    /// RFC 8032, Section 7.1, Test Vector 1: the comb reproduces the published
    /// public key of the secret key
    /// `9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60`,
    /// which is `encode(a · B)` for `a` the clamped low half of its SHA-512
    /// hash. This is the vector `ed25519::test_rfc8032_vector1_keygen` drives
    /// through `scalar_mult`, taken here through `comb_walk` instead.
    #[test]
    fn comb_walk_matches_rfc8032_vector1_public_key() {
        let sk: [u8; 32] = [
            0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec,
            0x2c, 0xc4, 0x44, 0x49, 0xc5, 0x69, 0x7b, 0x32, 0x69, 0x19, 0x70, 0x3b, 0xac, 0x03,
            0x1c, 0xae, 0x7f, 0x60,
        ];
        let expected_pk: [u8; 32] = [
            0xd7, 0x5a, 0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64,
            0x07, 0x3a, 0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68,
            0xf7, 0x07, 0x51, 0x1a,
        ];

        // a = clamp(SHA-512(sk)[0..32]), per RFC 8032 Section 5.1.5.
        let h = sha512(&sk);
        let mut a = [0u8; 32];
        let mut i = 0usize;
        while i < 32 {
            a[i] = h[i];
            i += 1;
        }
        a[0] &= 248;
        a[31] &= 127;
        a[31] |= 64;

        let base = ed25519_base_point();
        let table = comb_table(&base);
        assert_eq!(point_encode(&comb_walk(&table, &a)), expected_pk);
    }

    #[test]
    fn comb_walk_on_edge_scalars() {
        let base = ed25519_base_point();
        let table = comb_table(&base);
        let zero = [0u8; 32];
        let one = {
            let mut k = [0u8; 32];
            k[0] = 1;
            k
        };
        let all_ones = [0xffu8; 32];
        assert_eq!(
            point_encode(&comb_walk(&table, &zero)),
            point_encode(&point_identity())
        );
        assert_eq!(
            point_encode(&comb_walk(&table, &one)),
            point_encode(&base)
        );
        assert_eq!(
            point_encode(&comb_walk(&table, &all_ones)),
            point_encode(&scalar_mult(&all_ones, &base))
        );
    }
}
