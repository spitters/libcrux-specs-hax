#![allow(clippy::needless_range_loop)]
#![allow(clippy::manual_memcpy)]

//! RFC 9380 test vectors for `libcrux_specs_hax::hash_to_curve_p256`.
//!
//! - Appendix J.1.1: P256_XMD:SHA-256_SSWU_RO_.
//! - Appendix J.1.2: P256_XMD:SHA-256_SSWU_NU_.
//!
//! For every message the tests check `u[0]` (and `u[1]`), the map outputs
//! `Q0`, `Q1` (RO) or `Q` (NU), and the result `P`. Coordinates are compared
//! as the big-endian hexadecimal strings printed in the RFC.
//!
//! The vector tables are generated from the text of
//! <https://www.rfc-editor.org/rfc/rfc9380.txt> with awk: continuation lines
//! are joined, and each `key = value` line becomes one struct field
//! (`P.x` -> `px`, `u[0]` -> `u0`, `Q0.x` -> `q0x`, ...).

use libcrux_specs_hax::hash_to_curve_p256::*;
use libcrux_specs_hax::hash_to_field::hash_to_field_p256_sha256;
use libcrux_specs_hax::p256::{
    base_point, fp_add, fp_from_bytes, fp_inv, fp_mul, fp_sq, fp_to_bytes, point_add, point_affine_x,
    point_affine_y, point_double, point_from_uncompressed, point_identity, point_is_identity,
    point_to_uncompressed, P256FieldElement, P256Point, P256_B, P256_P,
};

/// A vector of the hash_to_curve (RO) suite.
struct RoVector {
    msg: &'static str,
    px: &'static str,
    py: &'static str,
    u0: &'static str,
    u1: &'static str,
    q0x: &'static str,
    q0y: &'static str,
    q1x: &'static str,
    q1y: &'static str,
}

/// A vector of the encode_to_curve (NU) suite.
struct NuVector {
    msg: &'static str,
    px: &'static str,
    py: &'static str,
    u0: &'static str,
    qx: &'static str,
    qy: &'static str,
}

// suite = P256_XMD:SHA-256_SSWU_RO_
const J11_P256_RO_DST: &str = "QUUX-V01-CS02-with-P256_XMD:SHA-256_SSWU_RO_";

const J11_P256_RO: [RoVector; 5] = [
    RoVector {
        msg: "",
        px: "2c15230b26dbc6fc9a37051158c95b79656e17a1a920b11394ca91c44247d3e4",
        py: "8a7a74985cc5c776cdfe4b1f19884970453912e9d31528c060be9ab5c43e8415",
        u0: "ad5342c66a6dd0ff080df1da0ea1c04b96e0330dd89406465eeba11582515009",
        u1: "8c0f1d43204bd6f6ea70ae8013070a1518b43873bcd850aafa0a9e220e2eea5a",
        q0x: "ab640a12220d3ff283510ff3f4b1953d09fad35795140b1c5d64f313967934d5",
        q0y: "dccb558863804a881d4fff3455716c836cef230e5209594ddd33d85c565b19b1",
        q1x: "51cce63c50d972a6e51c61334f0f4875c9ac1cd2d3238412f84e31da7d980ef5",
        q1y: "b45d1a36d00ad90e5ec7840a60a4de411917fbe7c82c3949a6e699e5a1b66aac",
    },
    RoVector {
        msg: "abc",
        px: "0bb8b87485551aa43ed54f009230450b492fead5f1cc91658775dac4a3388a0f",
        py: "5c41b3d0731a27a7b14bc0bf0ccded2d8751f83493404c84a88e71ffd424212e",
        u0: "afe47f2ea2b10465cc26ac403194dfb68b7f5ee865cda61e9f3e07a537220af1",
        u1: "379a27833b0bfe6f7bdca08e1e83c760bf9a338ab335542704edcd69ce9e46e0",
        q0x: "5219ad0ddef3cc49b714145e91b2f7de6ce0a7a7dc7406c7726c7e373c58cb48",
        q0y: "7950144e52d30acbec7b624c203b1996c99617d0b61c2442354301b191d93ecf",
        q1x: "019b7cb4efcfeaf39f738fe638e31d375ad6837f58a852d032ff60c69ee3875f",
        q1y: "589a62d2b22357fed5449bc38065b760095ebe6aeac84b01156ee4252715446e",
    },
    RoVector {
        msg: "abcdef0123456789",
        px: "65038ac8f2b1def042a5df0b33b1f4eca6bff7cb0f9c6c1526811864e544ed80",
        py: "cad44d40a656e7aff4002a8de287abc8ae0482b5ae825822bb870d6df9b56ca3",
        u0: "0fad9d125a9477d55cf9357105b0eb3a5c4259809bf87180aa01d651f53d312c",
        u1: "b68597377392cd3419d8fcc7d7660948c8403b19ea78bbca4b133c9d2196c0fb",
        q0x: "a17bdf2965eb88074bc01157e644ed409dac97cfcf0c61c998ed0fa45e79e4a2",
        q0y: "4f1bc80c70d411a3cc1d67aeae6e726f0f311639fee560c7f5a664554e3c9c2e",
        q1x: "7da48bb67225c1a17d452c983798113f47e438e4202219dd0715f8419b274d66",
        q1y: "b765696b2913e36db3016c47edb99e24b1da30e761a8a3215dc0ec4d8f96e6f9",
    },
    RoVector {
        msg: "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        px: "4be61ee205094282ba8a2042bcb48d88dfbb609301c49aa8b078533dc65a0b5d",
        py: "98f8df449a072c4721d241a3b1236d3caccba603f916ca680f4539d2bfb3c29e",
        u0: "3bbc30446f39a7befad080f4d5f32ed116b9534626993d2cc5033f6f8d805919",
        u1: "76bb02db019ca9d3c1e02f0c17f8baf617bbdae5c393a81d9ce11e3be1bf1d33",
        q0x: "c76aaa823aeadeb3f356909cb08f97eee46ecb157c1f56699b5efebddf0e6398",
        q0y: "776a6f45f528a0e8d289a4be12c4fab80762386ec644abf2bffb9b627e4352b1",
        q1x: "418ac3d85a5ccc4ea8dec14f750a3a9ec8b85176c95a7022f391826794eb5a75",
        q1y: "fd6604f69e9d9d2b74b072d14ea13050db72c932815523305cb9e807cc900aff",
    },
    RoVector {
        msg: "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        px: "457ae2981f70ca85d8e24c308b14db22f3e3862c5ea0f652ca38b5e49cd64bc5",
        py: "ecb9f0eadc9aeed232dabc53235368c1394c78de05dd96893eefa62b0f4757dc",
        u0: "4ebc95a6e839b1ae3c63b847798e85cb3c12d3817ec6ebc10af6ee51adb29fec",
        u1: "4e21af88e22ea80156aff790750121035b3eefaa96b425a8716e0d20b4e269ee",
        q0x: "d88b989ee9d1295df413d4456c5c850b8b2fb0f5402cc5c4c7e815412e926db8",
        q0y: "bb4a1edeff506cf16def96afff41b16fc74f6dbd55c2210e5b8f011ba32f4f40",
        q1x: "a281e34e628f3a4d2a53fa87ff973537d68ad4fbc28d3be5e8d9f6a2571c5a4b",
        q1y: "f6ed88a7aab56a488100e6f1174fa9810b47db13e86be999644922961206e184",
    },
];

// suite = P256_XMD:SHA-256_SSWU_NU_
const J12_P256_NU_DST: &str = "QUUX-V01-CS02-with-P256_XMD:SHA-256_SSWU_NU_";

const J12_P256_NU: [NuVector; 5] = [
    NuVector {
        msg: "",
        px: "f871caad25ea3b59c16cf87c1894902f7e7b2c822c3d3f73596c5ace8ddd14d1",
        py: "87b9ae23335bee057b99bac1e68588b18b5691af476234b8971bc4f011ddc99b",
        u0: "b22d487045f80e9edcb0ecc8d4bf77833e2bf1f3a54004d7df1d57f4802d311f",
        qx: "f871caad25ea3b59c16cf87c1894902f7e7b2c822c3d3f73596c5ace8ddd14d1",
        qy: "87b9ae23335bee057b99bac1e68588b18b5691af476234b8971bc4f011ddc99b",
    },
    NuVector {
        msg: "abc",
        px: "fc3f5d734e8dce41ddac49f47dd2b8a57257522a865c124ed02b92b5237befa4",
        py: "fe4d197ecf5a62645b9690599e1d80e82c500b22ac705a0b421fac7b47157866",
        u0: "c7f96eadac763e176629b09ed0c11992225b3a5ae99479760601cbd69c221e58",
        qx: "fc3f5d734e8dce41ddac49f47dd2b8a57257522a865c124ed02b92b5237befa4",
        qy: "fe4d197ecf5a62645b9690599e1d80e82c500b22ac705a0b421fac7b47157866",
    },
    NuVector {
        msg: "abcdef0123456789",
        px: "f164c6674a02207e414c257ce759d35eddc7f55be6d7f415e2cc177e5d8faa84",
        py: "3aa274881d30db70485368c0467e97da0e73c18c1d00f34775d012b6fcee7f97",
        u0: "314e8585fa92068b3ea2c3bab452d4257b38be1c097d58a21890456c2929614d",
        qx: "f164c6674a02207e414c257ce759d35eddc7f55be6d7f415e2cc177e5d8faa84",
        qy: "3aa274881d30db70485368c0467e97da0e73c18c1d00f34775d012b6fcee7f97",
    },
    NuVector {
        msg: "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        px: "324532006312be4f162614076460315f7a54a6f85544da773dc659aca0311853",
        py: "8d8197374bcd52de2acfefc8a54fe2c8d8bebd2a39f16be9b710e4b1af6ef883",
        u0: "752d8eaa38cd785a799a31d63d99c2ae4261823b4a367b133b2c6627f48858ab",
        qx: "324532006312be4f162614076460315f7a54a6f85544da773dc659aca0311853",
        qy: "8d8197374bcd52de2acfefc8a54fe2c8d8bebd2a39f16be9b710e4b1af6ef883",
    },
    NuVector {
        msg: "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        px: "5c4bad52f81f39c8e8de1260e9a06d72b8b00a0829a8ea004a610b0691bea5d9",
        py: "c801e7c0782af1f74f24fc385a8555da0582032a3ce038de637ccdcb16f7ef7b",
        u0: "0e1527840b9df2dfbef966678ff167140f2b27c4dccd884c25014dce0e41dfa3",
        qx: "5c4bad52f81f39c8e8de1260e9a06d72b8b00a0829a8ea004a610b0691bea5d9",
        qy: "c801e7c0782af1f74f24fc385a8555da0582032a3ce038de637ccdcb16f7ef7b",
    },
];

// --- Helpers ---

/// A canonical field element as 64 big-endian hexadecimal digits.
fn fp_hex(a: P256FieldElement) -> String {
    hex::encode(fp_to_bytes(a))
}

/// The affine coordinates of a finite P-256 point.
fn affine_hex(p: &P256Point) -> (String, String) {
    assert!(!point_is_identity(p));
    (fp_hex(point_affine_x(p)), fp_hex(point_affine_y(p)))
}

fn pair(x: &str, y: &str) -> (String, String) {
    (x.to_string(), y.to_string())
}

/// The field element of a small integer.
fn small(n: u64) -> P256FieldElement {
    [0, 0, 0, n]
}

/// The Legendre symbol a^((p - 1) / 2), as a^(2 * c1 + 1) with
/// c1 = (p - 3) / 4.
fn legendre(a: P256FieldElement) -> P256FieldElement {
    fp_mul(fp_sq(h2c_p256_pow_public(a, H2C_P256_C1)), a)
}

/// g(x) = x^3 + A * x + B.
fn curve_g(x: P256FieldElement) -> P256FieldElement {
    fp_add(fp_add(fp_mul(fp_sq(x), x), fp_mul(H2C_P256_A, x)), P256_B)
}

/// `true` when the affine point (x, y) satisfies the curve equation, by the
/// check of `point_from_uncompressed`.
fn on_curve(p: &P256Point) -> bool {
    point_from_uncompressed(&point_to_uncompressed(p)).is_some()
}

// --- Appendix J.1: P-256 ---

#[test]
fn j11_p256_ro() {
    let dst = J11_P256_RO_DST.as_bytes();
    for v in J11_P256_RO.iter() {
        let msg = v.msg.as_bytes();
        let u = hash_to_field_p256_sha256(msg, dst, 2).unwrap();
        assert_eq!(fp_hex(u[0]), v.u0, "msg = {:?}, u[0]", v.msg);
        assert_eq!(fp_hex(u[1]), v.u1, "msg = {:?}, u[1]", v.msg);
        let q0 = map_to_curve_p256(u[0]);
        let q1 = map_to_curve_p256(u[1]);
        assert_eq!(affine_hex(&q0), pair(v.q0x, v.q0y), "msg = {:?}, Q0", v.msg);
        assert_eq!(affine_hex(&q1), pair(v.q1x, v.q1y), "msg = {:?}, Q1", v.msg);
        let p = hash_to_curve_p256(msg, dst).unwrap();
        assert_eq!(affine_hex(&p), pair(v.px, v.py), "msg = {:?}, P", v.msg);
    }
}

#[test]
fn j12_p256_nu() {
    let dst = J12_P256_NU_DST.as_bytes();
    for v in J12_P256_NU.iter() {
        let msg = v.msg.as_bytes();
        let u = hash_to_field_p256_sha256(msg, dst, 1).unwrap();
        assert_eq!(fp_hex(u[0]), v.u0, "msg = {:?}, u[0]", v.msg);
        let q = map_to_curve_p256(u[0]);
        assert_eq!(affine_hex(&q), pair(v.qx, v.qy), "msg = {:?}, Q", v.msg);
        let p = encode_to_curve_p256(msg, dst).unwrap();
        assert_eq!(affine_hex(&p), pair(v.px, v.py), "msg = {:?}, P", v.msg);
    }
}

/// Step 4 of hash_to_curve with `crate::p256::point_add` in place of the
/// complete addition gives the same P.
#[test]
fn j11_p256_ro_with_case_split_addition() {
    let dst = J11_P256_RO_DST.as_bytes();
    for v in J11_P256_RO.iter() {
        let u = hash_to_field_p256_sha256(v.msg.as_bytes(), dst, 2).unwrap();
        let r = point_add(&map_to_curve_p256(u[0]), &map_to_curve_p256(u[1]));
        assert_eq!(affine_hex(&r), pair(v.px, v.py), "msg = {:?}", v.msg);
    }
}

// --- Appendix F.2.1.2: sqrt_ratio ---

/// For u / v = s^2 the result is (1, y) with y^2 * v = u; for
/// u / v = Z * s^2 it is (0, y) with y^2 * v = Z * u.
#[test]
fn sqrt_ratio_on_squares_and_non_squares() {
    for i in 1..9u64 {
        let s = fp_mul(small(i), small(0x9e3779b97f4a7c15));
        let v = fp_add(fp_sq(small(i + 40)), small(7));
        let s2 = fp_sq(s);

        let u_sq = fp_mul(s2, v);
        let (b, y) = sqrt_ratio_3mod4(u_sq, v);
        assert_eq!(b, 1, "i = {i}");
        assert_eq!(fp_mul(fp_sq(y), v), u_sq, "i = {i}");

        let u_non = fp_mul(H2C_P256_Z, u_sq);
        let (b, y) = sqrt_ratio_3mod4(u_non, v);
        assert_eq!(b, 0, "i = {i}");
        assert_eq!(fp_mul(fp_sq(y), v), fp_mul(H2C_P256_Z, u_non), "i = {i}");
    }
}

/// u = 0 is a square ratio with root 0.
#[test]
fn sqrt_ratio_at_zero() {
    let (b, y) = sqrt_ratio_3mod4(H2C_P256_ZERO, small(5));
    assert_eq!(b, 1);
    assert_eq!(y, H2C_P256_ZERO);
}

// --- Constants ---

/// 4 * c1 + 3 = p; c2^2 = -Z and sgn0(c2) = 0; A = -3 and Z = -10.
#[test]
fn constants() {
    let c1 = H2C_P256_C1;
    assert_eq!(c1[0] >> 62, 0);
    let mut r = [0u64; 4];
    for i in 0..4 {
        let low = if i < 3 { c1[i + 1] >> 62 } else { 3 };
        r[i] = (c1[i] << 2) | low;
    }
    assert_eq!(r, P256_P);

    assert_eq!(fp_sq(H2C_P256_C2), h2c_p256_negate(H2C_P256_Z));
    assert_eq!(fp_sq(H2C_P256_C2), small(10));
    assert_eq!(h2c_p256_sgn0(H2C_P256_C2), 0);

    assert_eq!(fp_add(H2C_P256_A, small(3)), H2C_P256_ZERO);
    assert_eq!(fp_add(H2C_P256_Z, small(10)), H2C_P256_ZERO);
}

/// RFC 9380, Appendix H.2: Z is not a square (criterion 1), Z != -1
/// (criterion 2), and g(B / (Z * A)) is a square (criterion 4).
#[test]
fn z_meets_the_sswu_criteria() {
    let minus_one = h2c_p256_negate(H2C_P256_ONE);
    assert_eq!(legendre(H2C_P256_Z), minus_one);
    assert_ne!(H2C_P256_Z, minus_one);
    let x = fp_mul(P256_B, fp_inv(fp_mul(H2C_P256_Z, H2C_P256_A)));
    assert_eq!(legendre(curve_g(x)), H2C_P256_ONE);
    // The Legendre symbol itself: 1 on a square, 0 on 0.
    assert_eq!(legendre(small(4)), H2C_P256_ONE);
    assert_eq!(legendre(H2C_P256_ZERO), H2C_P256_ZERO);
}

// --- Field helpers ---

#[test]
fn field_helpers() {
    let a = small(5);
    let b = h2c_p256_negate(a);
    assert_eq!(h2c_p256_select(1, a, b), a);
    assert_eq!(h2c_p256_select(0, a, b), b);
    assert_eq!(h2c_p256_ct_eq(a, a), 1);
    assert_eq!(h2c_p256_ct_eq(a, b), 0);
    assert_eq!(h2c_p256_ct_eq([1 << 63, 0, 0, 0], H2C_P256_ZERO), 0);
    assert_eq!(h2c_p256_is_zero(H2C_P256_ZERO), 1);
    assert_eq!(h2c_p256_is_zero(H2C_P256_ONE), 0);
    assert_eq!(h2c_p256_negate(H2C_P256_ZERO), H2C_P256_ZERO);
    assert_eq!(fp_add(a, b), H2C_P256_ZERO);
    // p - 5 is even.
    assert_eq!(h2c_p256_sgn0(a), 1);
    assert_eq!(h2c_p256_sgn0(b), 0);
    assert_eq!(h2c_p256_sgn0(H2C_P256_ZERO), 0);
    assert_eq!(h2c_p256_inv0(H2C_P256_ZERO), H2C_P256_ZERO);
    assert_eq!(fp_mul(h2c_p256_inv0(a), a), H2C_P256_ONE);
    assert_eq!(h2c_p256_pow_public(a, [0, 0, 0, 3]), small(125));
    assert_eq!(h2c_p256_pow_public(a, [0, 0, 0, 0]), H2C_P256_ONE);
}

// --- The Simplified SWU map at its exceptional inputs ---

/// tv2 = Z^2 * u^4 + Z * u^2 is zero exactly at u = 0 and u^2 = -1 / Z; step 7
/// of Appendix F.2 then takes tv4 = Z. -1 / Z = 1 / 10 = (1 / c2)^2.
#[test]
fn sswu_at_exceptional_inputs() {
    let u_exc = fp_inv(H2C_P256_C2);
    let t = fp_mul(H2C_P256_Z, fp_sq(u_exc));
    assert_eq!(fp_add(fp_sq(t), t), H2C_P256_ZERO);
    for u in [H2C_P256_ZERO, u_exc, h2c_p256_negate(u_exc), H2C_P256_ONE, small(2)] {
        let q = map_to_curve_p256(u);
        assert!(on_curve(&q), "u = {}", fp_hex(u));
        assert_eq!(h2c_p256_sgn0(q.y), h2c_p256_sgn0(u), "u = {}", fp_hex(u));
    }
}

// --- Complete addition ---

/// `h2c_p256_point_add_complete` agrees with `point_add` on generic points,
/// on P + P, on points with Z != 1, and on the point at infinity.
#[test]
fn complete_addition_agrees_with_point_add() {
    let g = base_point();
    let g2 = point_double(&g);
    let g3 = point_add(&g2, &g);
    let o = point_identity();
    let cases = [(g, g), (g, g2), (g2, g), (g2, g3), (g3, g3), (o, g), (g2, o)];
    for (i, (p, q)) in cases.iter().enumerate() {
        let r = h2c_p256_point_add_complete(p, q);
        assert_eq!(
            point_to_uncompressed(&r),
            point_to_uncompressed(&point_add(p, q)),
            "case {i}"
        );
    }
}

/// P + (-P) and O + O are the point at infinity, returned as (0, 1, 0), and
/// that value is accepted as an argument.
#[test]
fn complete_addition_at_infinity() {
    let g = base_point();
    let neg_g = P256Point { x: g.x, y: h2c_p256_negate(g.y), z: g.z };
    let o = h2c_p256_point_add_complete(&g, &neg_g);
    assert!(point_is_identity(&o));
    assert_eq!((o.x, o.y), (H2C_P256_ZERO, H2C_P256_ONE));
    let oo = h2c_p256_point_add_complete(&o, &point_identity());
    assert!(point_is_identity(&oo));
    let back = h2c_p256_point_add_complete(&o, &g);
    assert_eq!(point_to_uncompressed(&back), point_to_uncompressed(&g));
}

// --- Aborts ---

/// The only abort is the one of `expand_message_xmd`: a DST over 255 bytes.
#[test]
fn long_dst_aborts() {
    let dst = [0x41u8; 256];
    assert!(hash_to_curve_p256(b"abc", &dst).is_none());
    assert!(encode_to_curve_p256(b"abc", &dst).is_none());
    assert!(hash_to_curve_p256(b"abc", &dst[..255]).is_some());
    assert!(encode_to_curve_p256(b"abc", &dst[..255]).is_some());
}

// --- Field multiplication ---

/// Products (a, b, a * b mod p) for which the signed Solinas sum of
/// `reduce_mod_p` lies outside [0, 2^256) and one correction by p does not
/// wrap 2^256. They arise inside `legendre(Z)` and inside `sqrt_ratio_3mod4`
/// on the inputs of `sqrt_ratio_on_squares_and_non_squares` (i = 1 and
/// i = 7). The expected products are computed with bc.
const FP_MUL_CARRY_CASES: [(&str, &str, &str); 3] = [
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

fn fp_from_hex(s: &str) -> P256FieldElement {
    let mut b = [0u8; 32];
    hex::decode_to_slice(s, &mut b).unwrap();
    fp_from_bytes(&b)
}

#[test]
fn fp_mul_carry_correction() {
    for (a, b, ab) in FP_MUL_CARRY_CASES.iter() {
        let x = fp_from_hex(a);
        let y = fp_from_hex(b);
        assert_eq!(fp_hex(fp_mul(x, y)), *ab, "a = {a}");
        assert_eq!(fp_hex(fp_mul(y, x)), *ab, "a = {a}");
    }
}
