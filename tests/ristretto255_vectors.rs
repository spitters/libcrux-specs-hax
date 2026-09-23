//! RFC 9496, Appendix A test vectors for `libcrux_specs_hax::ristretto255`.
//!
//! A.1: encodings of the multiples 0..15 of the canonical generator.
//! A.2: encodings that decoding must reject.
//! A.3: inputs and encoded outputs of the element derivation function.
//! A.4: inputs and outputs of SQRT_RATIO_M1.
//!
//! The hex strings are the RFC text with the whitespace removed.

#![allow(clippy::needless_range_loop)]

use libcrux_specs_hax::curve25519::{fe_from_bytes, fe_to_bytes};
use libcrux_specs_hax::secret::Scalar;
use libcrux_specs_hax::ristretto255::{
    decode, element_add, element_double, element_mul, element_neg, element_sub, encode, equals,
    from_uniform_bytes, generator, identity, sqrt_ratio_m1,
};

fn hex32(s: &str) -> [u8; 32] {
    let v = hex::decode(s).expect("valid hex");
    let mut out = [0u8; 32];
    out.copy_from_slice(&v);
    out
}

fn hex64(s: &str) -> [u8; 64] {
    let v = hex::decode(s).expect("valid hex");
    let mut out = [0u8; 64];
    out.copy_from_slice(&v);
    out
}

/// RFC 9496, Appendix A.1: B[0] .. B[15].
const GENERATOR_MULTIPLES: [&str; 16] = [
    "0000000000000000000000000000000000000000000000000000000000000000",
    "e2f2ae0a6abc4e71a884a961c500515f58e30b6aa582dd8db6a65945e08d2d76",
    "6a493210f7499cd17fecb510ae0cea23a110e8d5b901f8acadd3095c73a3b919",
    "94741f5d5d52755ece4f23f044ee27d5d1ea1e2bd196b462166b16152a9d0259",
    "da80862773358b466ffadfe0b3293ab3d9fd53c5ea6c955358f568322daf6a57",
    "e882b131016b52c1d3337080187cf768423efccbb517bb495ab812c4160ff44e",
    "f64746d3c92b13050ed8d80236a7f0007c3b3f962f5ba793d19a601ebb1df403",
    "44f53520926ec81fbd5a387845beb7df85a96a24ece18738bdcfa6a7822a176d",
    "903293d8f2287ebe10e2374dc1a53e0bc887e592699f02d077d5263cdd55601c",
    "02622ace8f7303a31cafc63f8fc48fdc16e1c8c8d234b2f0d6685282a9076031",
    "20706fd788b2720a1ed2a5dad4952b01f413bcf0e7564de8cdc816689e2db95f",
    "bce83f8ba5dd2fa572864c24ba1810f9522bc6004afe95877ac73241cafdab42",
    "e4549ee16b9aa03099ca208c67adafcafa4c3f3e4e5303de6026e3ca8ff84460",
    "aa52e000df2e16f55fb1032fc33bc42742dad6bd5a8fc0be0167436c5948501f",
    "46376b80f409b29dc2b5f6f0c52591990896e5716f41477cd30085ab7f10301e",
    "e0c418f7c8d9c4cdd7395b93ea124f3ad99021bb681dfc3302a9d99a2e53e64e",
];

/// RFC 9496, Appendix A.2.
const INVALID_ENCODINGS: [&str; 29] = [
    // Non-canonical field encodings.
    "00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
    "f3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
    "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
    // Negative field elements.
    "0100000000000000000000000000000000000000000000000000000000000000",
    "01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
    "ed57ffd8c914fb201471d1c3d245ce3c746fcbe63a3679d51b6a516ebebe0e20",
    "c34c4e1826e5d403b78e246e88aa051c36ccf0aafebffe137d148a2bf9104562",
    "c940e5a4404157cfb1628b108db051a8d439e1a421394ec4ebccb9ec92a8ac78",
    "47cfc5497c53dc8e61c91d17fd626ffb1c49e2bca94eed052281b510b1117a24",
    "f1c6165d33367351b0da8f6e4511010c68174a03b6581212c71c0e1d026c3c72",
    "87260f7a2f12495118360f02c26a470f450dadf34a413d21042b43b9d93e1309",
    // Non-square x^2.
    "26948d35ca62e643e26a83177332e6b6afeb9d08e4268b650f1f5bbd8d81d371",
    "4eac077a713c57b4f4397629a4145982c661f48044dd3f96427d40b147d9742f",
    "de6a7b00deadc788eb6b6c8d20c0ae96c2f2019078fa604fee5b87d6e989ad7b",
    "bcab477be20861e01e4a0e295284146a510150d9817763caf1a6f4b422d67042",
    "2a292df7e32cababbd9de088d1d1abec9fc0440f637ed2fba145094dc14bea08",
    "f4a9e534fc0d216c44b218fa0c42d99635a0127ee2e53c712f70609649fdff22",
    "8268436f8c4126196cf64b3c7ddbda90746a378625f9813dd9b8457077256731",
    "2810e5cbc2cc4d4eece54f61c6f69758e289aa7ab440b3cbeaa21995c2f4232b",
    // Negative x * y value.
    "3eb858e78f5a7254d8c9731174a94f76755fd3941c0ac93735c07ba14579630e",
    "a45fdc55c76448c049a1ab33f17023edfb2be3581e9c7aade8a6125215e04220",
    "d483fe813c6ba647ebbfd3ec41adca1c6130c2beeee9d9bf065c8d151c5f396e",
    "8a2e1d30050198c65a54483123960ccc38aef6848e1ec8f5f780e8523769ba32",
    "32888462f8b486c68ad7dd9610be5192bbeaf3b443951ac1a8118419d9fa097b",
    "227142501b9d4355ccba290404bde41575b037693cef1f438c47f8fbf35d1165",
    "5c37cc491da847cfeb9281d407efc41e15144c876e0170b499a96a22ed31e01e",
    "445425117cb8c90edcbc7c1cc0e74f747f2c1efa5630a967c64f287792a48a4b",
    // s = -1, which causes y = 0.
    "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
];

/// RFC 9496, Appendix A.3: (input, encoded output) pairs.
const UNIFORM_BYTES: [(&str, &str); 7] = [
    (
        "5d1be09e3d0c82fc538112490e35701979d99e06ca3e2b5b54bffe8b4dc772c14d98b696a1bbfb5ca32c436cc61c16563790306c79eaca7705668b47dffe5bb6",
        "3066f82a1a747d45120d1740f14358531a8f04bbffe6a819f86dfe50f44a0a46",
    ),
    (
        "f116b34b8f17ceb56e8732a60d913dd10cce47a6d53bee9204be8b44f6678b270102a56902e2488c46120e9276cfe54638286b9e4b3cdb470b542d46c2068d38",
        "f26e5b6f7d362d2d2a94c5d0e7602cb4773c95a2e5c31a64f133189fa76ed61b",
    ),
    (
        "8422e1bbdaab52938b81fd602effb6f89110e1e57208ad12d9ad767e2e25510c27140775f9337088b982d83d7fcf0b2fa1edffe51952cbe7365e95c86eaf325c",
        "006ccd2a9e6867e6a2c5cea83d3302cc9de128dd2a9a57dd8ee7b9d7ffe02826",
    ),
    (
        "ac22415129b61427bf464e17baee8db65940c233b98afce8d17c57beeb7876c2150d15af1cb1fb824bbd14955f2b57d08d388aab431a391cfc33d5bafb5dbbaf",
        "f8f0c87cf237953c5890aec3998169005dae3eca1fbb04548c635953c817f92a",
    ),
    (
        "165d697a1ef3d5cf3c38565beefcf88c0f282b8e7dbd28544c483432f1cec7675debea8ebb4e5fe7d6f6e5db15f15587ac4d4d4a1de7191e0c1ca6664abcc413",
        "ae81e7dedf20a497e10c304a765c1767a42d6e06029758d2d7e8ef7cc4c41179",
    ),
    (
        "a836e6c9a9ca9f1e8d486273ad56a78c70cf18f0ce10abb1c7172ddd605d7fd2979854f47ae1ccf204a33102095b4200e5befc0465accc263175485f0e17ea5c",
        "e2705652ff9f5e44d3e841bf1c251cf7dddb77d140870d1ab2ed64f1a9ce8628",
    ),
    (
        "2cdc11eaeb95daf01189417cdddbf95952993aa9cb9c640eb5058d09702c74622c9965a697a3b345ec24ee56335b556e677b30e6f90ac77d781064f866a3c982",
        "80bd07262511cdde4863f8a7434cef696750681cb9510eea557088f76d9e5065",
    ),
];

/// RFC 9496, Appendix A.3: inputs that all produce `UNIFORM_BYTES_SAME_OUTPUT`.
const UNIFORM_BYTES_SAME_INPUTS: [&str; 4] = [
    "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff1200000000000000000000000000000000000000000000000000000000000000",
    "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "0000000000000000000000000000000000000000000000000000000000000080ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
    "00000000000000000000000000000000000000000000000000000000000000001200000000000000000000000000000000000000000000000000000000000080",
];

const UNIFORM_BYTES_SAME_OUTPUT: &str =
    "304282791023b73128d277bdcb5c7746ef2eac08dde9f2983379cb8e5ef0517f";

/// RFC 9496, Appendix A.4: (u, v, was_square, r).
const SQRT_RATIO_VECTORS: [(&str, &str, bool, &str); 6] = [
    (
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        true,
        "0000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0100000000000000000000000000000000000000000000000000000000000000",
        true,
        "0000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "0100000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        false,
        "0000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "0200000000000000000000000000000000000000000000000000000000000000",
        "0100000000000000000000000000000000000000000000000000000000000000",
        false,
        "3c5ff1b5d8e4113b871bd052f9e7bcd0582804c266ffb2d4f4203eb07fdb7c54",
    ),
    (
        "0400000000000000000000000000000000000000000000000000000000000000",
        "0100000000000000000000000000000000000000000000000000000000000000",
        true,
        "0200000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "0100000000000000000000000000000000000000000000000000000000000000",
        "0400000000000000000000000000000000000000000000000000000000000000",
        true,
        "f6ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3f",
    ),
];

/// A.1: B[0] is the identity and B[i+1] = B[i] + B[1].
#[test]
fn a1_generator_multiples_by_addition() {
    let g = generator();
    let mut acc = identity();
    for i in 0..16 {
        assert_eq!(
            hex::encode(encode(&acc)),
            GENERATOR_MULTIPLES[i],
            "encoding of {} * generator",
            i
        );
        acc = element_add(&acc, &g);
    }
}

/// A.1: the same encodings through scalar multiplication.
#[test]
fn a1_generator_multiples_by_scalar_mul() {
    let g = generator();
    for i in 0..16 {
        let mut k = [0u8; 32];
        k[0] = i as u8;
        assert_eq!(
            hex::encode(encode(&element_mul(&Scalar::from_bytes_secret(k), &g))),
            GENERATOR_MULTIPLES[i],
            "encoding of {} * generator",
            i
        );
    }
}

/// A.1: every listed encoding decodes, and re-encoding gives it back.
#[test]
fn a1_decode_encode_round_trip() {
    for i in 0..16 {
        let enc = hex32(GENERATOR_MULTIPLES[i]);
        let p = decode(&enc).expect("A.1 encoding decodes");
        assert_eq!(encode(&p), enc, "round trip of B[{}]", i);
    }
}

/// A.1: the decoded point equals the point computed by addition, and
/// `equals` separates distinct multiples.
#[test]
fn a1_equals() {
    let g = generator();
    let mut points = Vec::new();
    let mut acc = identity();
    for _ in 0..16 {
        points.push(acc);
        acc = element_add(&acc, &g);
    }
    for i in 0..16 {
        let decoded = decode(&hex32(GENERATOR_MULTIPLES[i])).expect("A.1 encoding decodes");
        assert!(equals(&points[i], &points[i]), "reflexivity at B[{}]", i);
        assert!(equals(&decoded, &decoded), "reflexivity at decoded B[{}]", i);
        assert!(equals(&points[i], &decoded), "B[{}] equals its decoding", i);
        assert!(equals(&decoded, &points[i]), "decoding equals B[{}]", i);
        for j in 0..16 {
            if i != j {
                assert!(!equals(&points[i], &points[j]), "B[{}] differs from B[{}]", i, j);
            }
        }
    }
}

/// Group law on the A.1 points: doubling, negation and subtraction.
#[test]
fn a1_double_neg_sub() {
    let g = generator();
    let mut points = Vec::new();
    let mut acc = identity();
    for _ in 0..16 {
        points.push(acc);
        acc = element_add(&acc, &g);
    }
    for i in 0..8 {
        assert_eq!(
            hex::encode(encode(&element_double(&points[i]))),
            GENERATOR_MULTIPLES[2 * i],
            "double of B[{}]",
            i
        );
    }
    for i in 0..16 {
        let zero = element_add(&points[i], &element_neg(&points[i]));
        assert_eq!(hex::encode(encode(&zero)), GENERATOR_MULTIPLES[0], "B[{}] - B[{}]", i, i);
        for j in 0..=i {
            assert_eq!(
                hex::encode(encode(&element_sub(&points[i], &points[j]))),
                GENERATOR_MULTIPLES[i - j],
                "B[{}] - B[{}]",
                i,
                j
            );
        }
    }
}

/// A.2: every listed encoding is rejected.
#[test]
fn a2_invalid_encodings_rejected() {
    for (i, s) in INVALID_ENCODINGS.iter().enumerate() {
        assert!(decode(&hex32(s)).is_none(), "invalid encoding {} accepted: {}", i, s);
    }
}

/// A.3: element derivation input/output pairs.
#[test]
fn a3_from_uniform_bytes() {
    for (i, (input, output)) in UNIFORM_BYTES.iter().enumerate() {
        let p = from_uniform_bytes(&hex64(input));
        assert_eq!(hex::encode(encode(&p)), *output, "A.3 pair {}", i);
    }
}

/// A.3: the four inputs that produce the same encoded output.
#[test]
fn a3_from_uniform_bytes_same_output() {
    let first = from_uniform_bytes(&hex64(UNIFORM_BYTES_SAME_INPUTS[0]));
    for (i, input) in UNIFORM_BYTES_SAME_INPUTS.iter().enumerate() {
        let p = from_uniform_bytes(&hex64(input));
        assert_eq!(hex::encode(encode(&p)), UNIFORM_BYTES_SAME_OUTPUT, "A.3 shared output, input {}", i);
        assert!(equals(&p, &first), "A.3 shared output, input {} equals input 0", i);
    }
}

/// A.3: every derived element decodes from its encoding to an equal element.
#[test]
fn a3_outputs_round_trip() {
    for (i, (input, output)) in UNIFORM_BYTES.iter().enumerate() {
        let p = from_uniform_bytes(&hex64(input));
        let q = decode(&hex32(output)).expect("A.3 output decodes");
        assert!(equals(&p, &q), "A.3 pair {} equals its decoding", i);
        assert_eq!(hex::encode(encode(&q)), *output, "A.3 pair {} round trip", i);
    }
}

/// A.4: SQRT_RATIO_M1 inputs and outputs.
#[test]
fn a4_sqrt_ratio_m1() {
    for (i, (u, v, was_square, r)) in SQRT_RATIO_VECTORS.iter().enumerate() {
        let (ws, root) = sqrt_ratio_m1(fe_from_bytes(&hex32(u)), fe_from_bytes(&hex32(v)));
        assert_eq!(ws == 1, *was_square, "A.4 vector {}: was_square", i);
        assert!(ws == 0 || ws == 1, "A.4 vector {}: was_square is a bit", i);
        assert_eq!(hex::encode(fe_to_bytes(root)), *r, "A.4 vector {}: r", i);
    }
}
