//! Pure Rust ChaCha20 stream cipher specification (RFC 8439, Section 2.3).
//!
//! ChaCha20 is a stream cipher that produces a 64-byte keystream block from a
//! 256-bit key, a 96-bit nonce, and a 32-bit block counter. The cipher encrypts
//! by XORing the keystream with the plaintext.
//!
//! The state is a 4x4 matrix of u32 words:
//! ```text
//!   cccc  cccc  cccc  cccc
//!   kkkk  kkkk  kkkk  kkkk
//!   kkkk  kkkk  kkkk  kkkk
//!   bbbb  nnnn  nnnn  nnnn
//! ```
//! where c = constant, k = key, b = block counter, n = nonce.
//!
//! No external dependencies. All functions are pure and value-passing.

use alloc::vec::Vec;

/// ChaCha20 constants: "expand 32-byte k" as four little-endian u32 words.
pub const CONSTANTS: [u32; 4] = [0x6170_7865, 0x3320_646e, 0x7962_2d32, 0x6b20_6574];

/// Read a little-endian u32 from a byte slice at the given offset.
pub fn u32_from_le_bytes(bytes: &[u8], offset: usize) -> u32 {
    (bytes[offset] as u32)
        | ((bytes[offset + 1] as u32) << 8)
        | ((bytes[offset + 2] as u32) << 16)
        | ((bytes[offset + 3] as u32) << 24)
}

/// Write a u32 as little-endian bytes into an array at the given offset.
pub fn u32_to_le_bytes(value: u32, out: &mut [u8], offset: usize) {
    out[offset] = value as u8;
    out[offset + 1] = (value >> 8) as u8;
    out[offset + 2] = (value >> 16) as u8;
    out[offset + 3] = (value >> 24) as u8;
}

/// ChaCha20 quarter round (RFC 8439, Section 2.1).
///
/// Operates in-place on four elements of the state matrix identified
/// by indices a, b, c, d.
pub fn quarter_round(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize) {
    state[a] = state[a].wrapping_add(state[b]);
    state[d] ^= state[a];
    state[d] = state[d].rotate_left(16);

    state[c] = state[c].wrapping_add(state[d]);
    state[b] ^= state[c];
    state[b] = state[b].rotate_left(12);

    state[a] = state[a].wrapping_add(state[b]);
    state[d] ^= state[a];
    state[d] = state[d].rotate_left(8);

    state[c] = state[c].wrapping_add(state[d]);
    state[b] ^= state[c];
    state[b] = state[b].rotate_left(7);
}

/// Perform the 20-round ChaCha20 inner block function (10 double rounds).
///
/// Each double round consists of four column quarter rounds followed by
/// four diagonal quarter rounds.
pub fn chacha20_inner_block(state: &mut [u32; 16]) {
    for _ in 0..10 {
        // Column rounds
        quarter_round(state, 0, 4, 8, 12);
        quarter_round(state, 1, 5, 9, 13);
        quarter_round(state, 2, 6, 10, 14);
        quarter_round(state, 3, 7, 11, 15);
        // Diagonal rounds
        quarter_round(state, 0, 5, 10, 15);
        quarter_round(state, 1, 6, 11, 12);
        quarter_round(state, 2, 7, 8, 13);
        quarter_round(state, 3, 4, 9, 14);
    }
}

/// Initialize the ChaCha20 state from key, nonce, and block counter.
///
/// State layout (4x4 u32 matrix):
/// - Words 0..3:   constants ("expand 32-byte k")
/// - Words 4..11:  key (8 little-endian u32 words from 32 bytes)
/// - Word 12:      block counter
/// - Words 13..15: nonce (3 little-endian u32 words from 12 bytes)
pub fn chacha20_init(key: &[u8; 32], nonce: &[u8; 12], counter: u32) -> [u32; 16] {
    let mut state = [0u32; 16];

    // Constants
    state[0] = CONSTANTS[0];
    state[1] = CONSTANTS[1];
    state[2] = CONSTANTS[2];
    state[3] = CONSTANTS[3];

    // Key (8 words, little-endian)
    for i in 0..8 {
        state[4 + i] = u32_from_le_bytes(key, 4 * i);
    }

    // Block counter
    state[12] = counter;

    // Nonce (3 words, little-endian)
    for i in 0..3 {
        state[13 + i] = u32_from_le_bytes(nonce, 4 * i);
    }

    state
}

/// Generate one 64-byte keystream block (RFC 8439, Section 2.3).
///
/// 1. Initialize state from key, nonce, and counter.
/// 2. Copy the initial state.
/// 3. Run 20 rounds (10 double rounds) on the working state.
/// 4. Add the initial state to the working state (wrapping_add per word).
/// 5. Serialize the 16 u32 words as 64 little-endian bytes.
pub fn chacha20_block(key: &[u8; 32], nonce: &[u8; 12], counter: u32) -> [u8; 64] {
    let initial_state = chacha20_init(key, nonce, counter);

    let mut working_state = initial_state;
    chacha20_inner_block(&mut working_state);

    // Add initial state to working state
    for i in 0..16 {
        working_state[i] = working_state[i].wrapping_add(initial_state[i]);
    }

    // Serialize to little-endian bytes
    let mut output = [0u8; 64];
    for i in 0..16 {
        u32_to_le_bytes(working_state[i], &mut output, 4 * i);
    }

    output
}

/// Encrypt (or decrypt) a message using ChaCha20 (RFC 8439, Section 2.4).
///
/// Generates keystream blocks starting at `counter`, XORs them with the
/// message. Encryption and decryption are the same operation (XOR is
/// its own inverse).
pub fn chacha20_encrypt(key: &[u8; 32], nonce: &[u8; 12], counter: u32, msg: &[u8]) -> Vec<u8> {
    let mut output = Vec::with_capacity(msg.len());
    let num_full_blocks = msg.len() / 64;
    let remainder = msg.len() % 64;

    for i in 0..num_full_blocks {
        let block = chacha20_block(key, nonce, counter.wrapping_add(i as u32));
        for j in 0..64 {
            output.push(msg[i * 64 + j] ^ block[j]);
        }
    }

    if remainder > 0 {
        let block = chacha20_block(key, nonce, counter.wrapping_add(num_full_blocks as u32));
        for j in 0..remainder {
            output.push(msg[num_full_blocks * 64 + j] ^ block[j]);
        }
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    /// RFC 8439, Section 2.1.1: Test quarter round on specific inputs.
    /// a = 0x11111111, b = 0x01020304, c = 0x9b8d6f43, d = 0x01234567
    /// After quarter round: a = 0xea2a92f4, b = 0xcb1cf8ce, c = 0x4581472e, d = 0x5881c4bb
    #[test]
    fn test_quarter_round() {
        let mut state = [0u32; 16];
        state[0] = 0x1111_1111;
        state[1] = 0x0102_0304;
        state[2] = 0x9b8d_6f43;
        state[3] = 0x0123_4567;
        quarter_round(&mut state, 0, 1, 2, 3);
        assert_eq!(state[0], 0xea2a_92f4);
        assert_eq!(state[1], 0xcb1c_f8ce);
        assert_eq!(state[2], 0x4581_472e);
        assert_eq!(state[3], 0x5881_c4bb);
    }

    /// RFC 8439, Section 2.3.2: ChaCha20 block function test vector.
    /// Key   = 00:01:02:...1f
    /// Nonce = 00:00:00:09:00:00:00:4a:00:00:00:00
    /// Counter = 1
    #[test]
    fn test_chacha20_block() {
        let mut key = [0u8; 32];
        for i in 0..32 {
            key[i] = i as u8;
        }
        let nonce: [u8; 12] = [
            0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x00, 0x4a, 0x00, 0x00, 0x00, 0x00,
        ];
        let counter = 1u32;

        let block = chacha20_block(&key, &nonce, counter);

        // RFC 8439, Section 2.3.2: expected keystream block
        #[rustfmt::skip]
        let expected: [u8; 64] = [
            0x10, 0xf1, 0xe7, 0xe4, 0xd1, 0x3b, 0x59, 0x15,
            0x50, 0x0f, 0xdd, 0x1f, 0xa3, 0x20, 0x71, 0xc4,
            0xc7, 0xd1, 0xf4, 0xc7, 0x33, 0xc0, 0x68, 0x03,
            0x04, 0x22, 0xaa, 0x9a, 0xc3, 0xd4, 0x6c, 0x4e,
            0xd2, 0x82, 0x64, 0x46, 0x07, 0x9f, 0xaa, 0x09,
            0x14, 0xc2, 0xd7, 0x05, 0xd9, 0x8b, 0x02, 0xa2,
            0xb5, 0x12, 0x9c, 0xd1, 0xde, 0x16, 0x4e, 0xb9,
            0xcb, 0xd0, 0x83, 0xe8, 0xa2, 0x50, 0x3c, 0x4e,
        ];
        assert_eq!(block, expected);
    }

    /// RFC 8439, Section 2.4.2: ChaCha20 encryption test vector.
    /// Key     = 00:01:02:...1f
    /// Nonce   = 00:00:00:00:00:00:00:4a:00:00:00:00
    /// Counter = 1
    /// Plaintext = "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."
    #[test]
    fn test_chacha20_encrypt() {
        let mut key = [0u8; 32];
        for i in 0..32 {
            key[i] = i as u8;
        }
        let nonce: [u8; 12] = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4a, 0x00, 0x00, 0x00, 0x00,
        ];
        let counter = 1u32;

        let plaintext = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";

        let ciphertext = chacha20_encrypt(&key, &nonce, counter, plaintext);

        #[rustfmt::skip]
        let expected: [u8; 114] = [
            0x6e, 0x2e, 0x35, 0x9a, 0x25, 0x68, 0xf9, 0x80,
            0x41, 0xba, 0x07, 0x28, 0xdd, 0x0d, 0x69, 0x81,
            0xe9, 0x7e, 0x7a, 0xec, 0x1d, 0x43, 0x60, 0xc2,
            0x0a, 0x27, 0xaf, 0xcc, 0xfd, 0x9f, 0xae, 0x0b,
            0xf9, 0x1b, 0x65, 0xc5, 0x52, 0x47, 0x33, 0xab,
            0x8f, 0x59, 0x3d, 0xab, 0xcd, 0x62, 0xb3, 0x57,
            0x16, 0x39, 0xd6, 0x24, 0xe6, 0x51, 0x52, 0xab,
            0x8f, 0x53, 0x0c, 0x35, 0x9f, 0x08, 0x61, 0xd8,
            0x07, 0xca, 0x0d, 0xbf, 0x50, 0x0d, 0x6a, 0x61,
            0x56, 0xa3, 0x8e, 0x08, 0x8a, 0x22, 0xb6, 0x5e,
            0x52, 0xbc, 0x51, 0x4d, 0x16, 0xcc, 0xf8, 0x06,
            0x81, 0x8c, 0xe9, 0x1a, 0xb7, 0x79, 0x37, 0x36,
            0x5a, 0xf9, 0x0b, 0xbf, 0x74, 0xa3, 0x5b, 0xe6,
            0xb4, 0x0b, 0x8e, 0xed, 0xf2, 0x78, 0x5e, 0x42,
            0x87, 0x4d,
        ];
        assert_eq!(ciphertext, expected);

        // Verify decryption (XOR is its own inverse)
        let decrypted = chacha20_encrypt(&key, &nonce, counter, &ciphertext);
        assert_eq!(decrypted, plaintext);
    }

    /// RFC 8439, Section 2.6.2: Poly1305 key generation test vector.
    /// Key   = 80:81:82:...:9f (32 bytes)
    /// Nonce = 00:00:00:00:00:01:02:03:04:05:06:07
    #[test]
    fn test_chacha20_poly_key_gen() {
        let mut key = [0u8; 32];
        for i in 0..32 {
            key[i] = (0x80 + i) as u8;
        }
        let nonce: [u8; 12] = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        ];
        let block = chacha20_block(&key, &nonce, 0);

        // First 32 bytes are the one-time Poly1305 key
        #[rustfmt::skip]
        let expected_poly_key: [u8; 32] = [
            0x8a, 0xd5, 0xa0, 0x8b, 0x90, 0x5f, 0x81, 0xcc,
            0x81, 0x50, 0x40, 0x27, 0x4a, 0xb2, 0x94, 0x71,
            0xa8, 0x33, 0xb6, 0x37, 0xe3, 0xfd, 0x0d, 0xa5,
            0x08, 0xdb, 0xb8, 0xe2, 0xfd, 0xd1, 0xa6, 0x46,
        ];
        assert_eq!(block[..32], expected_poly_key);
    }
}
