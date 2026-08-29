//! Pure Rust AES-128 and AES-256 specification (FIPS 197).
//!
//! No external dependencies. All functions are pure and value-passing.
//! Copied from `rust-specs/src/aes.rs` in
//! <https://github.com/spitters/libcrux-lean-specs> (MIT, Bas Spitters).

/// AES S-box lookup table (FIPS 197, Section 5.1.1).
#[rustfmt::skip]
pub const SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

/// AES round constants (FIPS 197, Section 5.2).
pub const RCON: [u8; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

/// Multiply by 2 in GF(2^8) with irreducible polynomial x^8 + x^4 + x^3 + x + 1.
pub fn gf_mul2(x: u8) -> u8 {
    let shifted = (x as u16) << 1;
    if shifted >= 256 {
        (shifted ^ 0x11b) as u8
    } else {
        shifted as u8
    }
}

/// Multiply by 3 in GF(2^8): 3*x = 2*x XOR x.
pub fn gf_mul3(x: u8) -> u8 {
    gf_mul2(x) ^ x
}

/// AES SubBytes: apply S-box to each byte of state.
fn sub_bytes(state: [u8; 16]) -> [u8; 16] {
    let mut result = [0u8; 16];
    let mut i = 0;
    while i < 16 {
        result[i] = SBOX[state[i] as usize];
        i += 1;
    }
    result
}

/// AES ShiftRows (FIPS 197, Section 5.1.2).
/// State is column-major: state[row + 4*col].
pub fn shift_rows(state: [u8; 16]) -> [u8; 16] {
    let mut result = [0u8; 16];
    let mut col = 0;
    while col < 4 {
        let mut row = 0;
        while row < 4 {
            result[row + 4 * col] = state[row + 4 * ((col + row) % 4)];
            row += 1;
        }
        col += 1;
    }
    result
}

/// AES MixColumns (FIPS 197, Section 5.1.3).
pub fn mix_columns(state: [u8; 16]) -> [u8; 16] {
    let mut result = [0u8; 16];
    let mut col = 0;
    while col < 4 {
        let s0 = state[4 * col];
        let s1 = state[4 * col + 1];
        let s2 = state[4 * col + 2];
        let s3 = state[4 * col + 3];

        result[4 * col]     = gf_mul2(s0) ^ gf_mul3(s1) ^ s2 ^ s3;
        result[4 * col + 1] = s0 ^ gf_mul2(s1) ^ gf_mul3(s2) ^ s3;
        result[4 * col + 2] = s0 ^ s1 ^ gf_mul2(s2) ^ gf_mul3(s3);
        result[4 * col + 3] = gf_mul3(s0) ^ s1 ^ s2 ^ gf_mul2(s3);
        col += 1;
    }
    result
}

/// AES AddRoundKey: XOR state with round key.
fn add_round_key(state: [u8; 16], round_key: [u8; 16]) -> [u8; 16] {
    let mut result = [0u8; 16];
    let mut i = 0;
    while i < 16 {
        result[i] = state[i] ^ round_key[i];
        i += 1;
    }
    result
}

/// Generic AES encryption core: applies num_rounds of AES transformation.
///
/// round_keys must have length num_rounds + 1.
/// Rounds 1..num_rounds-1 are full rounds (SubBytes, ShiftRows, MixColumns, AddRoundKey).
/// The final round omits MixColumns.
pub fn aes_encrypt_rounds(
    plaintext: [u8; 16],
    round_keys: &[[u8; 16]],
    num_rounds: usize,
) -> [u8; 16] {
    // Initial AddRoundKey
    let mut state = add_round_key(plaintext, round_keys[0]);

    // Rounds 1..num_rounds-1: full rounds with MixColumns
    let mut round = 1;
    while round < num_rounds {
        state = sub_bytes(state);
        state = shift_rows(state);
        state = mix_columns(state);
        state = add_round_key(state, round_keys[round]);
        round += 1;
    }

    // Final round: SubBytes, ShiftRows, AddRoundKey (no MixColumns)
    state = sub_bytes(state);
    state = shift_rows(state);
    state = add_round_key(state, round_keys[num_rounds]);

    state
}

// --- AES-128 ---

/// AES-128 key expansion (FIPS 197, Section 5.2).
///
/// Expands a 16-byte key into 11 round keys (Nk=4, Nr=10).
pub fn aes128_key_expand(key: [u8; 16]) -> [[u8; 16]; 11] {
    let mut round_keys = [[0u8; 16]; 11];
    round_keys[0] = key;

    let mut round = 1;
    while round <= 10 {
        let prev = round_keys[round - 1];
        let mut rk = [0u8; 16];

        // RotWord + SubWord + Rcon for first column
        let rot = [prev[13], prev[14], prev[15], prev[12]];
        let mut j = 0;
        while j < 4 {
            let sbox_out = SBOX[rot[j] as usize];
            if j == 0 {
                rk[j] = prev[j] ^ sbox_out ^ RCON[round - 1];
            } else {
                rk[j] = prev[j] ^ sbox_out;
            }
            j += 1;
        }

        // Remaining columns: XOR with previous
        j = 4;
        while j < 16 {
            rk[j] = rk[j - 4] ^ prev[j];
            j += 1;
        }

        round_keys[round] = rk;
        round += 1;
    }

    round_keys
}

/// AES-128 single-block encryption (FIPS 197).
///
/// Pure value-passing: takes key and plaintext, returns ciphertext.
/// 10 rounds (9 full + final without MixColumns).
pub fn aes128_encrypt(key: [u8; 16], plaintext: [u8; 16]) -> [u8; 16] {
    let round_keys = aes128_key_expand(key);
    aes_encrypt_rounds(plaintext, &round_keys, 10)
}

// --- AES-256 ---

/// AES-256 key expansion (FIPS 197, Section 5.2).
///
/// Expands a 32-byte key into 15 round keys (Nk=8, Nr=14).
///
/// The AES-256 key schedule processes 8 columns (32 bytes) at a time:
/// - Every 8th column (i % 8 == 0): RotWord + SubWord + Rcon
/// - Every 4th column within a group (i % 8 == 4): SubWord only (no RotWord)
/// - All other columns: simple XOR with previous
pub fn aes256_key_expand(key: [u8; 32]) -> [[u8; 16]; 15] {
    // Work with the expanded key as 60 individual 4-byte words (columns).
    // AES-256: Nk=8, Nr=14, total words = 4*(Nr+1) = 60.
    let mut w = [[0u8; 4]; 60];

    // First 8 words come directly from the 32-byte key
    let mut i = 0;
    while i < 8 {
        w[i] = [key[4 * i], key[4 * i + 1], key[4 * i + 2], key[4 * i + 3]];
        i += 1;
    }

    // Generate remaining words
    i = 8;
    while i < 60 {
        let mut temp = w[i - 1];

        if i % 8 == 0 {
            // RotWord + SubWord + Rcon
            let rotated = [temp[1], temp[2], temp[3], temp[0]];
            temp = [
                SBOX[rotated[0] as usize] ^ RCON[i / 8 - 1],
                SBOX[rotated[1] as usize],
                SBOX[rotated[2] as usize],
                SBOX[rotated[3] as usize],
            ];
        } else if i % 8 == 4 {
            // SubWord only (no RotWord, no Rcon)
            temp = [
                SBOX[temp[0] as usize],
                SBOX[temp[1] as usize],
                SBOX[temp[2] as usize],
                SBOX[temp[3] as usize],
            ];
        }

        let mut j = 0;
        while j < 4 {
            temp[j] ^= w[i - 8][j];
            j += 1;
        }
        w[i] = temp;

        i += 1;
    }

    // Pack words into 16-byte round keys
    let mut round_keys = [[0u8; 16]; 15];
    let mut r = 0;
    while r < 15 {
        let mut j = 0;
        while j < 4 {
            round_keys[r][4 * j]     = w[4 * r + j][0];
            round_keys[r][4 * j + 1] = w[4 * r + j][1];
            round_keys[r][4 * j + 2] = w[4 * r + j][2];
            round_keys[r][4 * j + 3] = w[4 * r + j][3];
            j += 1;
        }
        r += 1;
    }

    round_keys
}

/// AES-256 single-block encryption (FIPS 197).
///
/// Pure value-passing: takes 32-byte key and plaintext, returns ciphertext.
/// 14 rounds (13 full + final without MixColumns).
pub fn aes256_encrypt(key: [u8; 32], plaintext: [u8; 16]) -> [u8; 16] {
    let round_keys = aes256_key_expand(key);
    aes_encrypt_rounds(plaintext, &round_keys, 14)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// FIPS 197, Appendix B — AES-128 test vector.
    #[test]
    fn test_aes128_fips197_appendix_b() {
        let key: [u8; 16] = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let plaintext: [u8; 16] = [
            0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d,
            0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
        ];
        let expected: [u8; 16] = [
            0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb,
            0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32,
        ];

        let ciphertext = aes128_encrypt(key, plaintext);
        assert_eq!(ciphertext, expected);
    }

    /// FIPS 197, Appendix C.3 — AES-256 test vector.
    #[test]
    fn test_aes256_fips197_appendix_c3() {
        let key: [u8; 32] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
        ];
        let plaintext: [u8; 16] = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
        ];
        let expected: [u8; 16] = [
            0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf,
            0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60, 0x89,
        ];

        let ciphertext = aes256_encrypt(key, plaintext);
        assert_eq!(ciphertext, expected);
    }

    /// Verify AES-128 key expansion produces correct first and last round keys.
    #[test]
    fn test_aes128_key_expand() {
        let key: [u8; 16] = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let round_keys = aes128_key_expand(key);

        // Round key 0 is the original key
        assert_eq!(round_keys[0], key);

        // Round key 1 (FIPS 197, Appendix A.1)
        let expected_rk1: [u8; 16] = [
            0xa0, 0xfa, 0xfe, 0x17, 0x88, 0x54, 0x2c, 0xb1,
            0x23, 0xa3, 0x39, 0x39, 0x2a, 0x6c, 0x76, 0x05,
        ];
        assert_eq!(round_keys[1], expected_rk1);
    }

    /// Verify AES-256 key expansion produces correct round keys.
    #[test]
    fn test_aes256_key_expand() {
        let key: [u8; 32] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
        ];
        let round_keys = aes256_key_expand(key);

        // Round key 0 is the first half of the key
        assert_eq!(
            round_keys[0],
            [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
             0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]
        );

        // Round key 1 is the second half of the key
        assert_eq!(
            round_keys[1],
            [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
             0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]
        );
    }

    /// AES-128 encryption of all-zero block with all-zero key.
    /// This produces the GHASH subkey H used in GCM tests.
    #[test]
    fn test_aes128_zero_key_zero_plaintext() {
        let key = [0u8; 16];
        let plaintext = [0u8; 16];
        let ciphertext = aes128_encrypt(key, plaintext);
        let expected: [u8; 16] = [
            0x66, 0xe9, 0x4b, 0xd4, 0xef, 0x8a, 0x2c, 0x3b,
            0x88, 0x4c, 0xfa, 0x59, 0xca, 0x34, 0x2b, 0x2e,
        ];
        assert_eq!(ciphertext, expected);
    }
}
