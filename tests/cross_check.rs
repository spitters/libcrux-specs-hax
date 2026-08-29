//! Cross-check: compare the libcrux-specs-hax implementations against the
//! libcrux-lean-specs reference, the official libcrux crates and RustCrypto.
//!
//! A failure here means a specification in this crate computes a different
//! function than the reference implementation.

use proptest::prelude::*;

// ---------- SHA-256 ----------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn sha256_32_vs_reference(msg in prop::array::uniform32(any::<u8>())) {
        let ours = libcrux_specs_hax::sha256::sha256_32(msg);
        let theirs = libcrux_specs::fixed::sha256_32(&msg);
        prop_assert_eq!(ours, theirs, "sha256_32 mismatch with libcrux-lean-specs");
    }

    #[test]
    fn sha256_32_vs_libcrux(msg in prop::array::uniform32(any::<u8>())) {
        let ours = libcrux_specs_hax::sha256::sha256_32(msg);
        let theirs = libcrux_sha2::sha256(&msg);
        prop_assert_eq!(&ours[..], &theirs[..], "sha256_32 mismatch with libcrux-sha2");
    }
}

// ---------- HMAC-SHA256 ----------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    #[test]
    fn hmac_sha256_32_vs_reference(
        key in prop::array::uniform32(any::<u8>()),
        msg in prop::array::uniform32(any::<u8>()),
    ) {
        let ours = libcrux_specs_hax::hmac::hmac_sha256_32(key, msg);
        let theirs = libcrux_specs::fixed::hmac_sha256_32(&key, &msg);
        prop_assert_eq!(ours, theirs, "hmac_sha256_32 mismatch with libcrux-lean-specs");
    }

    #[test]
    fn hmac_sha256_32_vs_libcrux(
        key in prop::array::uniform32(any::<u8>()),
        msg in prop::array::uniform32(any::<u8>()),
    ) {
        let ours = libcrux_specs_hax::hmac::hmac_sha256_32(key, msg);
        let theirs = libcrux_hmac::hmac(
            libcrux_hmac::Algorithm::Sha256, &key, &msg, None,
        );
        let theirs_arr: [u8; 32] = theirs.try_into().expect("HMAC output should be 32 bytes");
        prop_assert_eq!(ours, theirs_arr, "hmac_sha256_32 mismatch with libcrux-hmac");
    }
}

// ---------- HKDF ----------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    #[test]
    fn hkdf_extract_32_vs_reference(
        salt in prop::array::uniform32(any::<u8>()),
        ikm in prop::array::uniform32(any::<u8>()),
    ) {
        let ours = libcrux_specs_hax::hkdf::hkdf_extract_32(salt, ikm);
        let theirs = libcrux_specs::fixed::hkdf_extract_32(&salt, &ikm);
        prop_assert_eq!(ours, theirs, "hkdf_extract_32 mismatch with libcrux-lean-specs");
    }
}

// ---------- AES-128 ----------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    #[test]
    fn aes128_encrypt_vs_reference(
        key in prop::array::uniform16(any::<u8>()),
        block in prop::array::uniform16(any::<u8>()),
    ) {
        let ours = libcrux_specs_hax::aes128::aes128_encrypt(key, block);
        // Use RustCrypto AES for block-level reference
        use aes::cipher::{BlockEncrypt, KeyInit, generic_array::GenericArray};
        let cipher = aes::Aes128::new(GenericArray::from_slice(&key));
        let mut reference = GenericArray::clone_from_slice(&block);
        cipher.encrypt_block(&mut reference);
        prop_assert_eq!(&ours[..], reference.as_slice(), "aes128_encrypt mismatch with RustCrypto AES");
    }
}

// ---------- X25519 ----------
// `x25519::scalarmult` delegates to `curve25519`; this checks the wrapper
// against the libcrux-lean-specs fixed-length entry point.

#[test]
fn x25519_scalarmult_vs_reference() {
    let scalar = [9u8; 32];
    let point = [9u8; 32];
    let ours = libcrux_specs_hax::x25519::scalarmult(scalar, point);
    let theirs = libcrux_specs::fixed::x25519_scalarmult(&scalar, &point);
    assert_eq!(ours, theirs, "x25519 scalarmult mismatch with libcrux-lean-specs");
}

// ---------- NIST/RFC Known-Answer Tests ----------

#[test]
fn sha256_nist_empty() {
    // SHA-256("") = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
    // But sha256_32 takes a 32-byte input, so test SHA-256(0^32):
    let msg = [0u8; 32];
    let ours = libcrux_specs_hax::sha256::sha256_32(msg);
    let reference = libcrux_sha2::sha256(&msg);
    assert_eq!(&ours[..], &reference[..], "SHA-256 of 32 zero bytes");
}

#[test]
fn aes128_nist_fips197() {
    // FIPS 197 Appendix B: AES-128
    // Key:       2b7e151628aed2a6abf7158809cf4f3c
    // Plaintext: 3243f6a8885a308d313198a2e0370734
    // Expected:  3925841d02dc09fbdc118597196a0b32
    let key = hex::decode("2b7e151628aed2a6abf7158809cf4f3c").unwrap();
    let pt  = hex::decode("3243f6a8885a308d313198a2e0370734").unwrap();
    let exp = hex::decode("3925841d02dc09fbdc118597196a0b32").unwrap();

    let key_arr: [u8; 16] = key.try_into().unwrap();
    let pt_arr:  [u8; 16] = pt.try_into().unwrap();

    let ct = libcrux_specs_hax::aes128::aes128_encrypt(key_arr, pt_arr);
    assert_eq!(&ct[..], &exp[..], "AES-128 FIPS 197 test vector");
}
