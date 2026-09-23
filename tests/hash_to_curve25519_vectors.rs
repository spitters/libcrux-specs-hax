//! RFC 9380 test vectors for `libcrux_specs_hax::hash_to_curve25519`.
//!
//! - Appendix J.4.1 and J.4.2: curve25519_XMD:SHA-512_ELL2_RO_ / NU_.
//! - Appendix J.5.1 and J.5.2: edwards25519_XMD:SHA-512_ELL2_RO_ / NU_.
//!
//! For every message the tests check `u[0]` (and `u[1]`), the map outputs
//! `Q0`, `Q1` (RO) or `Q` (NU), and the result `P`. Coordinates are compared
//! as the big-endian hexadecimal strings printed in the RFC.
//!
//! The vector tables are generated from the text of
//! https://www.rfc-editor.org/rfc/rfc9380.txt with awk: continuation lines
//! are joined, and each `key = value` line becomes one struct field
//! (`P.x` -> `px`, `u[0]` -> `u0`, `Q0.x` -> `q0x`, ...).

#![allow(clippy::needless_range_loop)]

use libcrux_specs_hax::curve25519::{fe_inv, fe_mul, fe_one, fe_to_bytes, fe_zero};
use libcrux_specs_hax::edwards25519::{ed25519_base_point, point_identity, EdPoint};
use libcrux_specs_hax::hash_to_curve25519::*;
use libcrux_specs_hax::hash_to_field::hash_to_field_25519_sha512;
use libcrux_specs_hax::ristretto255::fe_neg;

/// A vector of a hash_to_curve (RO) suite.
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

/// A vector of an encode_to_curve (NU) suite.
struct NuVector {
    msg: &'static str,
    px: &'static str,
    py: &'static str,
    u0: &'static str,
    qx: &'static str,
    qy: &'static str,
}

// suite = curve25519_XMD:SHA-512_ELL2_RO_
const J41_CURVE25519_RO_DST: &str = "QUUX-V01-CS02-with-curve25519_XMD:SHA-512_ELL2_RO_";

const J41_CURVE25519_RO: [RoVector; 5] = [
    RoVector {
        msg: "",
        px: "2de3780abb67e861289f5749d16d3e217ffa722192d16bbd9d1bfb9d112b98c0",
        py: "3b5dc2a498941a1033d176567d457845637554a2fe7a3507d21abd1c1bd6e878",
        u0: "005fe8a7b8fef0a16c105e6cadf5a6740b3365e18692a9c05bfbb4d97f645a6a",
        u1: "1347edbec6a2b5d8c02e058819819bee177077c9d10a4ce165aab0fd0252261a",
        q0x: "36b4df0c864c64707cbf6cf36e9ee2c09a6cb93b28313c169be29561bb904f98",
        q0y: "6cd59d664fb58c66c892883cd0eb792e52055284dac3907dd756b45d15c3983d",
        q1x: "3fa114783a505c0b2b2fbeef0102853c0b494e7757f2a089d0daae7ed9a0db2b",
        q1y: "76c0fe7fec932aaafb8eefb42d9cbb32eb931158f469ff3050af15cfdbbeff94",
    },
    RoVector {
        msg: "abc",
        px: "2b4419f1f2d48f5872de692b0aca72cc7b0a60915dd70bde432e826b6abc526d",
        py: "1b8235f255a268f0a6fa8763e97eb3d22d149343d495da1160eff9703f2d07dd",
        u0: "49bed021c7a3748f09fa8cdfcac044089f7829d3531066ac9e74e0994e05bc7d",
        u1: "5c36525b663e63389d886105cee7ed712325d5a97e60e140aba7e2ce5ae851b6",
        q0x: "16b3d86e056b7970fa00165f6f48d90b619ad618791661b7b5e1ec78be10eac1",
        q0y: "4ab256422d84c5120b278cbdfc4e1facc5baadffeccecf8ee9bf3946106d50ca",
        q1x: "7ec29ddbf34539c40adfa98fcb39ec36368f47f30e8f888cc7e86f4d46e0c264",
        q1y: "10d1abc1cae2d34c06e247f2141ba897657fb39f1080d54f09ce0af128067c74",
    },
    RoVector {
        msg: "abcdef0123456789",
        px: "68ca1ea5a6acf4e9956daa101709b1eee6c1bb0df1de3b90d4602382a104c036",
        py: "2a375b656207123d10766e68b938b1812a4a6625ff83cb8d5e86f58a4be08353",
        u0: "6412b7485ba26d3d1b6c290a8e1435b2959f03721874939b21782df17323d160",
        u1: "24c7b46c1c6d9a21d32f5707be1380ab82db1054fde82865d5c9e3d968f287b2",
        q0x: "71de3dadfe268872326c35ac512164850860567aea0e7325e6b91a98f86533ad",
        q0y: "26a08b6e9a18084c56f2147bf515414b9b63f1522e1b6c5649f7d4b0324296ec",
        q1x: "5704069021f61e41779e2ba6b932268316d6d2a6f064f997a22fef16d1eaeaca",
        q1y: "50483c7540f64fb4497619c050f2c7fe55454ec0f0e79870bb44302e34232210",
    },
    RoVector {
        msg: "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        px: "096e9c8bae6c06b554c1ee69383bb0e82267e064236b3a30608d4ed20b73ac5a",
        py: "1eb5a62612cafb32b16c3329794645b5b948d9f8ffe501d4e26b073fef6de355",
        u0: "5e123990f11bbb5586613ffabdb58d47f64bb5f2fa115f8ea8df0188e0c9e1b5",
        u1: "5e8553eb00438a0bb1e7faa59dec6d8087f9c8011e5fb8ed9df31cb6c0d4ac19",
        q0x: "7a94d45a198fb5daa381f45f2619ab279744efdd8bd8ed587fc5b65d6cea1df0",
        q0y: "67d44f85d376e64bb7d713585230cdbfafc8e2676f7568e0b6ee59361116a6e1",
        q1x: "30506fb7a32136694abd61b6113770270debe593027a968a01f271e146e60c18",
        q1y: "7eeee0e706b40c6b5174e551426a67f975ad5a977ee2f01e8e20a6d612458c3b",
    },
    RoVector {
        msg: "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        px: "1bc61845a138e912f047b5e70ba9606ba2a447a4dade024c8ef3dd42b7bbc5fe",
        py: "623d05e47b70e25f7f1d51dda6d7c23c9a18ce015fe3548df596ea9e38c69bf1",
        u0: "20f481e85da7a3bf60ac0fb11ed1d0558fc6f941b3ac5469aa8b56ec883d6d7d",
        u1: "017d57fd257e9a78913999a23b52ca988157a81b09c5442501d07fed20869465",
        q0x: "02d606e2699b918ee36f2818f2bc5013e437e673c9f9b9cdc15fd0c5ee913970",
        q0y: "29e9dc92297231ef211245db9e31767996c5625dfbf92e1c8107ef887365de1e",
        q1x: "38920e9b988d1ab7449c0fa9a6058192c0c797bb3d42ac345724341a1aa98745",
        q1y: "24dcc1be7c4d591d307e89049fd2ed30aae8911245a9d8554bf6032e5aa40d3d",
    },
];

// suite = curve25519_XMD:SHA-512_ELL2_NU_
const J42_CURVE25519_NU_DST: &str = "QUUX-V01-CS02-with-curve25519_XMD:SHA-512_ELL2_NU_";

const J42_CURVE25519_NU: [NuVector; 5] = [
    NuVector {
        msg: "",
        px: "1bb913f0c9daefa0b3375378ffa534bda5526c97391952a7789eb976edfe4d08",
        py: "4548368f4f983243e747b62a600840ae7c1dab5c723991f85d3a9768479f3ec4",
        u0: "608d892b641f0328523802a6603427c26e55e6f27e71a91a478148d45b5093cd",
        qx: "51125222da5e763d97f3c10fcc92ea6860b9ccbbd2eb1285728f566721c1e65b",
        qy: "343d2204f812d3dfc5304a5808c6c0d81a903a5d228b342442aa3c9ba5520a3d",
    },
    NuVector {
        msg: "abc",
        px: "7c22950b7d900fa866334262fcaea47a441a578df43b894b4625c9b450f9a026",
        py: "5547bc00e4c09685dcbc6cb6765288b386d8bdcb595fa5a6e3969e08097f0541",
        u0: "46f5b22494bfeaa7f232cc8d054be68561af50230234d7d1d63d1d9abeca8da5",
        qx: "7d56d1e08cb0ccb92baf069c18c49bb5a0dcd927eff8dcf75ca921ef7f3e6eeb",
        qy: "404d9a7dc25c9c05c44ab9a94590e7c3fe2dcec74533a0b24b188a5d5dacf429",
    },
    NuVector {
        msg: "abcdef0123456789",
        px: "31ad08a8b0deeb2a4d8b0206ca25f567ab4e042746f792f4b7973f3ae2096c52",
        py: "405070c28e78b4fa269427c82827261991b9718bd6c6e95d627d701a53c30db1",
        u0: "235fe40c443766ce7e18111c33862d66c3b33267efa50d50f9e8e5d252a40aaa",
        qx: "3fbe66b9c9883d79e8407150e7c2a1c8680bee496c62fabe4619a72b3cabe90f",
        qy: "08ec476147c9a0a3ff312d303dbbd076abb7551e5fce82b48ab14b433f8d0a7b",
    },
    NuVector {
        msg: "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        px: "027877759d155b1997d0d84683a313eb78bdb493271d935b622900459d52ceaa",
        py: "54d691731a53baa30707f4a87121d5169fb5d587d70fb0292b5830dedbec4c18",
        u0: "001e92a544463bda9bd04ddbe3d6eed248f82de32f522669efc5ddce95f46f5b",
        qx: "227e0bb89de700385d19ec40e857db6e6a3e634b1c32962f370d26f84ff19683",
        qy: "5f86ff3851d262727326a32c1bf7655a03665830fa7f1b8b1e5a09d85bc66e4a",
    },
    NuVector {
        msg: "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        px: "5fd892c0958d1a75f54c3182a18d286efab784e774d1e017ba2fb252998b5dc1",
        py: "750af3c66101737423a4519ac792fb93337bd74ee751f19da4cf1e94f4d6d0b8",
        u0: "1a68a1af9f663592291af987203393f707305c7bac9c8d63d6a729bdc553dc19",
        qx: "3bcd651ee54d5f7b6013898aab251ee8ecc0688166fce6e9548d38472f6bd196",
        qy: "1bb36ad9197299f111b4ef21271c41f4b7ecf5543db8bb5931307ebdb2eaa465",
    },
];

// suite = edwards25519_XMD:SHA-512_ELL2_RO_
const J51_EDWARDS25519_RO_DST: &str = "QUUX-V01-CS02-with-edwards25519_XMD:SHA-512_ELL2_RO_";

const J51_EDWARDS25519_RO: [RoVector; 5] = [
    RoVector {
        msg: "",
        px: "3c3da6925a3c3c268448dcabb47ccde5439559d9599646a8260e47b1e4822fc6",
        py: "09a6c8561a0b22bef63124c588ce4c62ea83a3c899763af26d795302e115dc21",
        u0: "03fef4813c8cb5f98c6eef88fae174e6e7d5380de2b007799ac7ee712d203f3a",
        u1: "780bdddd137290c8f589dc687795aafae35f6b674668d92bf92ae793e6a60c75",
        q0x: "6549118f65bb617b9e8b438decedc73c496eaed496806d3b2eb9ee60b88e09a7",
        q0y: "7315bcc8cf47ed68048d22bad602c6680b3382a08c7c5d3f439a973fb4cf9feb",
        q1x: "31dcfc5c58aa1bee6e760bf78cbe71c2bead8cebb2e397ece0f37a3da19c9ed2",
        q1y: "7876d81474828d8a5928b50c82420b2bd0898d819e9550c5c82c39fc9bafa196",
    },
    RoVector {
        msg: "abc",
        px: "608040b42285cc0d72cbb3985c6b04c935370c7361f4b7fbdb1ae7f8c1a8ecad",
        py: "1a8395b88338f22e435bbd301183e7f20a5f9de643f11882fb237f88268a5531",
        u0: "5081955c4141e4e7d02ec0e36becffaa1934df4d7a270f70679c78f9bd57c227",
        u1: "005bdc17a9b378b6272573a31b04361f21c371b256252ae5463119aa0b925b76",
        q0x: "5c1525bd5d4b4e034512949d187c39d48e8cd84242aa4758956e4adc7d445573",
        q0y: "2bf426cf7122d1a90abc7f2d108befc2ef415ce8c2d09695a7407240faa01f29",
        q1x: "37b03bba828860c6b459ddad476c83e0f9285787a269df2156219b7e5c86210c",
        q1y: "285ebf5412f84d0ad7bb4e136729a9ffd2195d5b8e73c0dc85110ce06958f432",
    },
    RoVector {
        msg: "abcdef0123456789",
        px: "6d7fabf47a2dc03fe7d47f7dddd21082c5fb8f86743cd020f3fb147d57161472",
        py: "53060a3d140e7fbcda641ed3cf42c88a75411e648a1add71217f70ea8ec561a6",
        u0: "285ebaa3be701b79871bcb6e225ecc9b0b32dff2d60424b4c50642636a78d5b3",
        u1: "2e253e6a0ef658fedb8e4bd6a62d1544fd6547922acb3598ec6b369760b81b31",
        q0x: "3ac463dd7fddb773b069c5b2b01c0f6b340638f54ee3bd92d452fcec3015b52d",
        q0y: "7b03ba1e8db9ec0b390d5c90168a6a0b7107156c994c674b61fe696cbeb46baf",
        q1x: "0757e7e904f5e86d2d2f4acf7e01c63827fde2d363985aa7432106f1b3a444ec",
        q1y: "50026c96930a24961e9d86aa91ea1465398ff8e42015e2ec1fa397d416f6a1c0",
    },
    RoVector {
        msg: "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        px: "5fb0b92acedd16f3bcb0ef83f5c7b7a9466b5f1e0d8d217421878ea3686f8524",
        py: "2eca15e355fcfa39d2982f67ddb0eea138e2994f5956ed37b7f72eea5e89d2f7",
        u0: "4fedd25431c41f2a606952e2945ef5e3ac905a42cf64b8b4d4a83c533bf321af",
        u1: "02f20716a5801b843987097a8276b6d869295b2e11253751ca72c109d37485a9",
        q0x: "703e69787ea7524541933edf41f94010a201cc841c1cce60205ec38513458872",
        q0y: "32bb192c4f89106466f0874f5fd56a0d6b6f101cb714777983336c159a9bec75",
        q1x: "0c9077c5c31720ed9413abe59bf49ce768506128d810cb882435aa90f713ef6b",
        q1y: "7d5aec5210db638c53f050597964b74d6dda4be5b54fa73041bf909ccb3826cb",
    },
    RoVector {
        msg: "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        px: "0efcfde5898a839b00997fbe40d2ebe950bc81181afbd5cd6b9618aa336c1e8c",
        py: "6dc2fc04f266c5c27f236a80b14f92ccd051ef1ff027f26a07f8c0f327d8f995",
        u0: "6e34e04a5106e9bd59f64aba49601bf09d23b27f7b594e56d5de06df4a4ea33b",
        u1: "1c1c2cb59fc053f44b86c5d5eb8c1954b64976d0302d3729ff66e84068f5fd96",
        q0x: "21091b2e3f9258c7dfa075e7ae513325a94a3d8a28e1b1cb3b5b6f5d65675592",
        q0y: "41a33d324c89f570e0682cdf7bdb78852295daf8084c669f2cc9692896ab5026",
        q1x: "4c07ec48c373e39a23bd7954f9e9b66eeab9e5ee1279b867b3d5315aa815454f",
        q1y: "67ccac7c3cb8d1381242d8d6585c57eabaddbb5dca5243a68a8aeb5477d94b3a",
    },
];

// suite = edwards25519_XMD:SHA-512_ELL2_NU_
const J52_EDWARDS25519_NU_DST: &str = "QUUX-V01-CS02-with-edwards25519_XMD:SHA-512_ELL2_NU_";

const J52_EDWARDS25519_NU: [NuVector; 5] = [
    NuVector {
        msg: "",
        px: "1ff2b70ecf862799e11b7ae744e3489aa058ce805dd323a936375a84695e76da",
        py: "222e314d04a4d5725e9f2aff9fb2a6b69ef375a1214eb19021ceab2d687f0f9b",
        u0: "7f3e7fb9428103ad7f52db32f9df32505d7b427d894c5093f7a0f0374a30641d",
        qx: "42836f691d05211ebc65ef8fcf01e0fb6328ec9c4737c26050471e50803022eb",
        qy: "22cb4aaa555e23bd460262d2130d6a3c9207aa8bbb85060928beb263d6d42a95",
    },
    NuVector {
        msg: "abc",
        px: "5f13cc69c891d86927eb37bd4afc6672360007c63f68a33ab423a3aa040fd2a8",
        py: "67732d50f9a26f73111dd1ed5dba225614e538599db58ba30aaea1f5c827fa42",
        u0: "09cfa30ad79bd59456594a0f5d3a76f6b71c6787b04de98be5cd201a556e253b",
        qx: "333e41b61c6dd43af220c1ac34a3663e1cf537f996bab50ab66e33c4bd8e4e19",
        qy: "51b6f178eb08c4a782c820e306b82c6e273ab22e258d972cd0c511787b2a3443",
    },
    NuVector {
        msg: "abcdef0123456789",
        px: "1dd2fefce934ecfd7aae6ec998de088d7dd03316aa1847198aecf699ba6613f1",
        py: "2f8a6c24dd1adde73909cada6a4a137577b0f179d336685c4a955a0a8e1a86fb",
        u0: "475ccff99225ef90d78cc9338e9f6a6bb7b17607c0c4428937de75d33edba941",
        qx: "55186c242c78e7d0ec5b6c9553f04c6aeef64e69ec2e824472394da32647cfc6",
        qy: "5b9ea3c265ee42256a8f724f616307ef38496ef7eba391c08f99f3bea6fa88f0",
    },
    NuVector {
        msg: "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        px: "35fbdc5143e8a97afd3096f2b843e07df72e15bfca2eaf6879bf97c5d3362f73",
        py: "2af6ff6ef5ebba128b0774f4296cb4c2279a074658b083b8dcca91f57a603450",
        u0: "049a1c8bd51bcb2aec339f387d1ff51428b88d0763a91bcdf6929814ac95d03d",
        qx: "024b6e1621606dca8071aa97b43dce4040ca78284f2a527dcf5d0fbfac2b07e7",
        qy: "5102353883d739bdc9f8a3af650342b171217167dcce34f8db57208ec1dfdbf2",
    },
    NuVector {
        msg: "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        px: "6e5e1f37e99345887fc12111575fc1c3e36df4b289b8759d23af14d774b66bff",
        py: "2c90c3d39eb18ff291d33441b35f3262cdd307162cc97c31bfcc7a4245891a37",
        u0: "3cb0178a8137cefa5b79a3a57c858d7eeeaa787b2781be4a362a2f0750d24fa0",
        qx: "3e6368cff6e88a58e250c54bd27d2c989ae9b3acb6067f2651ad282ab8c21cd9",
        qy: "38fb39f1566ca118ae6c7af42810c0bb9767ae5960abb5a8ca792530bfb9447d",
    },
];

// --- Helpers ---

/// The canonical value of a field element as 64 big-endian hexadecimal digits.
fn fe_be_hex(a: [u64; 5]) -> String {
    let mut bytes = fe_to_bytes(a);
    bytes.reverse();
    hex::encode(bytes)
}

/// The affine coordinates (X / Z, Y / Z) of an edwards25519 point.
fn ed_affine_hex(p: &EdPoint) -> (String, String) {
    let z_inv = fe_inv(p.z);
    (fe_be_hex(fe_mul(p.x, z_inv)), fe_be_hex(fe_mul(p.y, z_inv)))
}

/// The affine coordinates of a finite curve25519 point.
fn mont_affine_hex(p: &MontPoint) -> (String, String) {
    assert_eq!(p.infinity, 0);
    (fe_be_hex(p.u), fe_be_hex(p.v))
}

fn pair(x: &str, y: &str) -> (String, String) {
    (x.to_string(), y.to_string())
}

// --- Appendix J.4: curve25519 ---

#[test]
fn j41_curve25519_ro() {
    let dst = J41_CURVE25519_RO_DST.as_bytes();
    for v in J41_CURVE25519_RO.iter() {
        let msg = v.msg.as_bytes();
        let u = hash_to_field_25519_sha512(msg, dst, 2).unwrap();
        assert_eq!(fe_be_hex(u[0]), v.u0, "msg = {:?}, u[0]", v.msg);
        assert_eq!(fe_be_hex(u[1]), v.u1, "msg = {:?}, u[1]", v.msg);
        let q0 = map_to_curve_curve25519(u[0]);
        let q1 = map_to_curve_curve25519(u[1]);
        assert_eq!(mont_affine_hex(&q0), pair(v.q0x, v.q0y), "msg = {:?}, Q0", v.msg);
        assert_eq!(mont_affine_hex(&q1), pair(v.q1x, v.q1y), "msg = {:?}, Q1", v.msg);
        let p = hash_to_curve_curve25519(msg, dst).unwrap();
        assert_eq!(mont_affine_hex(&p), pair(v.px, v.py), "msg = {:?}, P", v.msg);
    }
}

#[test]
fn j42_curve25519_nu() {
    let dst = J42_CURVE25519_NU_DST.as_bytes();
    for v in J42_CURVE25519_NU.iter() {
        let msg = v.msg.as_bytes();
        let u = hash_to_field_25519_sha512(msg, dst, 1).unwrap();
        assert_eq!(fe_be_hex(u[0]), v.u0, "msg = {:?}, u[0]", v.msg);
        let q = map_to_curve_curve25519(u[0]);
        assert_eq!(mont_affine_hex(&q), pair(v.qx, v.qy), "msg = {:?}, Q", v.msg);
        let p = encode_to_curve_curve25519(msg, dst).unwrap();
        assert_eq!(mont_affine_hex(&p), pair(v.px, v.py), "msg = {:?}, P", v.msg);
    }
}

// --- Appendix J.5: edwards25519 ---

#[test]
fn j51_edwards25519_ro() {
    let dst = J51_EDWARDS25519_RO_DST.as_bytes();
    for v in J51_EDWARDS25519_RO.iter() {
        let msg = v.msg.as_bytes();
        let u = hash_to_field_25519_sha512(msg, dst, 2).unwrap();
        assert_eq!(fe_be_hex(u[0]), v.u0, "msg = {:?}, u[0]", v.msg);
        assert_eq!(fe_be_hex(u[1]), v.u1, "msg = {:?}, u[1]", v.msg);
        let q0 = map_to_curve_edwards25519(u[0]);
        let q1 = map_to_curve_edwards25519(u[1]);
        assert_eq!(ed_affine_hex(&q0), pair(v.q0x, v.q0y), "msg = {:?}, Q0", v.msg);
        assert_eq!(ed_affine_hex(&q1), pair(v.q1x, v.q1y), "msg = {:?}, Q1", v.msg);
        let p = hash_to_curve_edwards25519(msg, dst).unwrap();
        assert_eq!(ed_affine_hex(&p), pair(v.px, v.py), "msg = {:?}, P", v.msg);
    }
}

#[test]
fn j52_edwards25519_nu() {
    let dst = J52_EDWARDS25519_NU_DST.as_bytes();
    for v in J52_EDWARDS25519_NU.iter() {
        let msg = v.msg.as_bytes();
        let u = hash_to_field_25519_sha512(msg, dst, 1).unwrap();
        assert_eq!(fe_be_hex(u[0]), v.u0, "msg = {:?}, u[0]", v.msg);
        let q = map_to_curve_edwards25519(u[0]);
        assert_eq!(ed_affine_hex(&q), pair(v.qx, v.qy), "msg = {:?}, Q", v.msg);
        let p = encode_to_curve_edwards25519(msg, dst).unwrap();
        assert_eq!(ed_affine_hex(&p), pair(v.px, v.py), "msg = {:?}, P", v.msg);
    }
}

// --- The curve25519 route through edwards25519 ---

/// The curve25519 results are the images of the edwards25519 results under
/// the birational map, for the curve25519 domain separation tags.
#[test]
fn curve25519_suites_agree_with_edwards25519_route() {
    let dst_ro = J41_CURVE25519_RO_DST.as_bytes();
    for v in J41_CURVE25519_RO.iter() {
        let p = hash_to_curve_edwards25519(v.msg.as_bytes(), dst_ro).unwrap();
        assert_eq!(mont_affine_hex(&mont_from_edwards(&p)), pair(v.px, v.py));
    }
    let dst_nu = J42_CURVE25519_NU_DST.as_bytes();
    for v in J42_CURVE25519_NU.iter() {
        let p = encode_to_curve_edwards25519(v.msg.as_bytes(), dst_nu).unwrap();
        assert_eq!(mont_affine_hex(&mont_from_edwards(&p)), pair(v.px, v.py));
    }
}

/// RFC 9380, Appendix G.2.2: with sgn0(c1) = 0 the rational map sends the
/// edwards25519 base point to the curve25519 base point (9, v), and back.
#[test]
fn birational_map_on_base_points() {
    let b = ed25519_base_point();
    let m = mont_from_edwards(&b);
    assert_eq!(
        mont_affine_hex(&m),
        pair(
            "0000000000000000000000000000000000000000000000000000000000000009",
            "5f51e65e475f794b1fe122d388b72eb36dc2b28192839e4dd6163a5d81312c14",
        )
    );
    assert_eq!(ed_affine_hex(&mont_to_edwards(&m)), ed_affine_hex(&b));
}

/// The identity and the points of order 2 under both birational maps.
#[test]
fn birational_map_on_exceptional_points() {
    let inf = mont_from_edwards(&point_identity());
    assert_eq!(inf.infinity, 1);
    assert_eq!(ed_affine_hex(&mont_to_edwards(&inf)), ed_affine_hex(&point_identity()));

    let minus_one = fe_neg(fe_one());
    let two_torsion = EdPoint { x: fe_zero(), y: minus_one, z: fe_one(), t: fe_zero() };
    let m = mont_from_edwards(&two_torsion);
    assert_eq!(m.infinity, 0);
    assert_eq!(mont_affine_hex(&m), pair(&"00".repeat(32), &"00".repeat(32)));
    assert_eq!(ed_affine_hex(&mont_to_edwards(&m)), ed_affine_hex(&two_torsion));

    // 8 * (0, 0) is the point at infinity.
    assert_eq!(clear_cofactor_curve25519(&m).infinity, 1);
}

/// u = 0: -J is not a square, so Elligator 2 returns x2 = 0 and the point
/// (0, 0); steps 8 to 12 of Appendix G.2.2 send it to the identity.
#[test]
fn elligator2_at_zero() {
    let q = map_to_curve_curve25519(fe_zero());
    assert_eq!(mont_affine_hex(&q), pair(&"00".repeat(32), &"00".repeat(32)));
    assert_eq!(
        ed_affine_hex(&map_to_curve_edwards25519(fe_zero())),
        ed_affine_hex(&point_identity())
    );
}

/// sgn0(c1) = 0 and c1^2 = -486664; c2^2 = 2 * c3; c3^2 = -1.
#[test]
fn constants() {
    let c1 = sqrt_neg_486664();
    assert_eq!(h2c_sgn0(c1), 0);
    assert_eq!(fe_be_hex(fe_neg(fe_mul(c1, c1))), format!("{:064x}", 486664));
    let c2 = elligator2_c2();
    let c3 = elligator2_c3();
    assert_eq!(fe_be_hex(fe_mul(c2, c2)), fe_be_hex(fe_mul([2, 0, 0, 0, 0], c3)));
    assert_eq!(fe_be_hex(fe_mul(c3, c3)), fe_be_hex(fe_neg(fe_one())));
    assert_eq!(fe_be_hex(mont_j()), format!("{:064x}", 486662));
}

/// The only abort is the one of `expand_message_xmd`: a DST over 255 bytes.
#[test]
fn long_dst_aborts() {
    let dst = [0x41u8; 256];
    assert!(hash_to_curve_edwards25519(b"abc", &dst).is_none());
    assert!(encode_to_curve_edwards25519(b"abc", &dst).is_none());
    assert!(hash_to_curve_curve25519(b"abc", &dst).is_none());
    assert!(encode_to_curve_curve25519(b"abc", &dst).is_none());
    assert!(hash_to_curve_edwards25519(b"abc", &dst[..255]).is_some());
}
