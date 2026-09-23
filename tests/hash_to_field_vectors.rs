//! RFC 9380 test vectors for `libcrux_specs_hax::hash_to_field`.
//!
//! - Appendix K.1, K.2 and K.3: `expand_message_xmd` with SHA-256, SHA-256
//!   with a DST longer than 255 bytes (Section 5.3.3), and SHA-512.
//! - The abort conditions of Section 5.3.1, step 2.
//! - Appendix J.5.1 and J.5.2 (edwards25519_XMD:SHA-512_ELL2_RO_ / NU_) and
//!   J.1.1 and J.1.2 (P256_XMD:SHA-256_SSWU_RO_ / NU_): the `u[0]` and `u[1]`
//!   outputs of `hash_to_field`.
//!
//! Each vector is `(msg, len_in_bytes, uniform_bytes)` or `(msg, [u...])`,
//! with `msg` and the DST as ASCII strings and the outputs in hexadecimal,
//! as printed in the RFC.

#![allow(clippy::needless_range_loop)]
#![allow(clippy::manual_memcpy)]

use libcrux_specs_hax::curve25519::fe_to_bytes;
use libcrux_specs_hax::hash_to_field::*;
use libcrux_specs_hax::p256::fp_to_bytes;

// --- Appendix K.1: expand_message_xmd(SHA-256) ---

const K1_XMD_SHA256_DST: &str = "QUUX-V01-CS02-with-expander-SHA256-128";

const K1_XMD_SHA256: [(&str, usize, &str); 10] = [
    (
        "",
        0x20,
        "68a985b87eb6b46952128911f2a4412bbc302a9d759667f87f7a21d803f07235",
    ),
    (
        "abc",
        0x20,
        "d8ccab23b5985ccea865c6c97b6e5b8350e794e603b4b97902f53a8a0d605615",
    ),
    (
        "abcdef0123456789",
        0x20,
        "eff31487c770a893cfb36f912fbfcbff40d5661771ca4b2cb4eafe524333f5c1",
    ),
    (
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqq",
        0x20,
        "b23a1d2b4d97b2ef7785562a7e8bac7eed54ed6e97e29aa51bfe3f12ddad1ff9",
    ),
    (
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaa",
        0x20,
        "4623227bcc01293b8c130bf771da8c298dede7383243dc0993d2d94823958c4c",
    ),
    (
        "",
        0x80,
        "af84c27ccfd45d41914fdff5df25293e221afc53d8ad2ac06d5e3e29485dadbe\
         e0d121587713a3e0dd4d5e69e93eb7cd4f5df4cd103e188cf60cb02edc3edf18\
         eda8576c412b18ffb658e3dd6ec849469b979d444cf7b26911a08e63cf31f9dc\
         c541708d3491184472c2c29bb749d4286b004ceb5ee6b9a7fa5b646c993f0ced",
    ),
    (
        "abc",
        0x80,
        "abba86a6129e366fc877aab32fc4ffc70120d8996c88aee2fe4b32d6c7b6437a\
         647e6c3163d40b76a73cf6a5674ef1d890f95b664ee0afa5359a5c4e07985635\
         bbecbac65d747d3d2da7ec2b8221b17b0ca9dc8a1ac1c07ea6a1e60583e2cb00\
         058e77b7b72a298425cd1b941ad4ec65e8afc50303a22c0f99b0509b4c895f40",
    ),
    (
        "abcdef0123456789",
        0x80,
        "ef904a29bffc4cf9ee82832451c946ac3c8f8058ae97d8d629831a74c6572bd9\
         ebd0df635cd1f208e2038e760c4994984ce73f0d55ea9f22af83ba4734569d4b\
         c95e18350f740c07eef653cbb9f87910d833751825f0ebefa1abe5420bb52be1\
         4cf489b37fe1a72f7de2d10be453b2c9d9eb20c7e3f6edc5a60629178d9478df",
    ),
    (
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqq",
        0x80,
        "80be107d0884f0d881bb460322f0443d38bd222db8bd0b0a5312a6fedb49c1bb\
         d88fd75d8b9a09486c60123dfa1d73c1cc3169761b17476d3c6b7cbbd727acd0\
         e2c942f4dd96ae3da5de368d26b32286e32de7e5a8cb2949f866a0b80c58116b\
         29fa7fabb3ea7d520ee603e0c25bcaf0b9a5e92ec6a1fe4e0391d1cdbce8c68a",
    ),
    (
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaa",
        0x80,
        "546aff5444b5b79aa6148bd81728704c32decb73a3ba76e9e75885cad9def1d0\
         6d6792f8a7d12794e90efed817d96920d728896a4510864370c207f99bd4a608\
         ea121700ef01ed879745ee3e4ceef777eda6d9e5e38b90c86ea6fb0b36504ba4\
         a45d22e86f6db5dd43d98a294bebb9125d5b794e9d2a81181066eb954966a487",
    ),
];

// --- Appendix K.2: expand_message_xmd(SHA-256) (Long DST) ---

const K2_XMD_SHA256_LONG_DST_DST: &str = "QUUX-V01-CS02-with-expander-SHA256-128-long-DST-1111111111111111\
         1111111111111111111111111111111111111111111111111111111111111111\
         1111111111111111111111111111111111111111111111111111111111111111\
         1111111111111111111111111111111111111111111111111111111111111111";

const K2_XMD_SHA256_LONG_DST: [(&str, usize, &str); 10] = [
    (
        "",
        0x20,
        "e8dc0c8b686b7ef2074086fbdd2f30e3f8bfbd3bdf177f73f04b97ce618a3ed3",
    ),
    (
        "abc",
        0x20,
        "52dbf4f36cf560fca57dedec2ad924ee9c266341d8f3d6afe5171733b16bbb12",
    ),
    (
        "abcdef0123456789",
        0x20,
        "35387dcf22618f3728e6c686490f8b431f76550b0b2c61cbc1ce7001536f4521",
    ),
    (
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqq",
        0x20,
        "01b637612bb18e840028be900a833a74414140dde0c4754c198532c3a0ba42bc",
    ),
    (
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaa",
        0x20,
        "20cce7033cabc5460743180be6fa8aac5a103f56d481cf369a8accc0c374431b",
    ),
    (
        "",
        0x80,
        "14604d85432c68b757e485c8894db3117992fc57e0e136f71ad987f789a0abc2\
         87c47876978e2388a02af86b1e8d1342e5ce4f7aaa07a87321e691f6fba7e007\
         2eecc1218aebb89fb14a0662322d5edbd873f0eb35260145cd4e64f748c5dfe6\
         0567e126604bcab1a3ee2dc0778102ae8a5cfd1429ebc0fa6bf1a53c36f55dfc",
    ),
    (
        "abc",
        0x80,
        "1a30a5e36fbdb87077552b9d18b9f0aee16e80181d5b951d0471d55b66684914\
         aef87dbb3626eaabf5ded8cd0686567e503853e5c84c259ba0efc37f71c839da\
         2129fe81afdaec7fbdc0ccd4c794727a17c0d20ff0ea55e1389d6982d1241cb8\
         d165762dbc39fb0cee4474d2cbbd468a835ae5b2f20e4f959f56ab24cd6fe267",
    ),
    (
        "abcdef0123456789",
        0x80,
        "d2ecef3635d2397f34a9f86438d772db19ffe9924e28a1caf6f1c8f15603d402\
         8f40891044e5c7e39ebb9b31339979ff33a4249206f67d4a1e7c765410bcd249\
         ad78d407e303675918f20f26ce6d7027ed3774512ef5b00d816e51bfcc96c353\
         9601fa48ef1c07e494bdc37054ba96ecb9dbd666417e3de289d4f424f502a982",
    ),
    (
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqq",
        0x80,
        "ed6e8c036df90111410431431a232d41a32c86e296c05d426e5f44e75b9a50d3\
         35b2412bc6c91e0a6dc131de09c43110d9180d0a70f0d6289cb4e43b05f7ee5e\
         9b3f42a1fad0f31bac6a625b3b5c50e3a83316783b649e5ecc9d3b1d9471cb50\
         24b7ccf40d41d1751a04ca0356548bc6e703fca02ab521b505e8e45600508d32",
    ),
    (
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaa",
        0x80,
        "78b53f2413f3c688f07732c10e5ced29a17c6a16f717179ffbe38d92d6c9ec29\
         6502eb9889af83a1928cd162e845b0d3c5424e83280fed3d10cffb2f8431f14e\
         7a23f4c68819d40617589e4c41169d0b56e0e3535be1fd71fbb08bb70c5b5ffe\
         d953d6c14bf7618b35fc1f4c4b30538236b4b08c9fbf90462447a8ada60be495",
    ),
];

// --- Appendix K.3: expand_message_xmd(SHA-512) ---

const K3_XMD_SHA512_DST: &str = "QUUX-V01-CS02-with-expander-SHA512-256";

const K3_XMD_SHA512: [(&str, usize, &str); 10] = [
    (
        "",
        0x20,
        "6b9a7312411d92f921c6f68ca0b6380730a1a4d982c507211a90964c394179ba",
    ),
    (
        "abc",
        0x20,
        "0da749f12fbe5483eb066a5f595055679b976e93abe9be6f0f6318bce7aca8dc",
    ),
    (
        "abcdef0123456789",
        0x20,
        "087e45a86e2939ee8b91100af1583c4938e0f5fc6c9db4b107b83346bc967f58",
    ),
    (
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqq",
        0x20,
        "7336234ee9983902440f6bc35b348352013becd88938d2afec44311caf8356b3",
    ),
    (
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaa",
        0x20,
        "57b5f7e766d5be68a6bfe1768e3c2b7f1228b3e4b3134956dd73a59b954c66f4",
    ),
    (
        "",
        0x80,
        "41b037d1734a5f8df225dd8c7de38f851efdb45c372887be655212d07251b921\
         b052b62eaed99b46f72f2ef4cc96bfaf254ebbbec091e1a3b9e4fb5e5b619d2e\
         0c5414800a1d882b62bb5cd1778f098b8eb6cb399d5d9d18f5d5842cf5d13d7e\
         b00a7cff859b605da678b318bd0e65ebff70bec88c753b159a805d2c89c55961",
    ),
    (
        "abc",
        0x80,
        "7f1dddd13c08b543f2e2037b14cefb255b44c83cc397c1786d975653e36a6b11\
         bdd7732d8b38adb4a0edc26a0cef4bb45217135456e58fbca1703cd6032cb134\
         7ee720b87972d63fbf232587043ed2901bce7f22610c0419751c065922b48843\
         1851041310ad659e4b23520e1772ab29dcdeb2002222a363f0c2b1c972b3efe1",
    ),
    (
        "abcdef0123456789",
        0x80,
        "3f721f208e6199fe903545abc26c837ce59ac6fa45733f1baaf0222f8b7acb04\
         24814fcb5eecf6c1d38f06e9d0a6ccfbf85ae612ab8735dfdf9ce84c372a77c8\
         f9e1c1e952c3a61b7567dd0693016af51d2745822663d0c2367e3f4f0bed827f\
         eecc2aaf98c949b5ed0d35c3f1023d64ad1407924288d366ea159f46287e61ac",
    ),
    (
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
         qqqqq",
        0x80,
        "b799b045a58c8d2b4334cf54b78260b45eec544f9f2fb5bd12fb603eaee70db7\
         317bf807c406e26373922b7b8920fa29142703dd52bdf280084fb7ef69da78af\
         df80b3586395b433dc66cde048a258e476a561e9deba7060af40adf30c64249c\
         a7ddea79806ee5beb9a1422949471d267b21bc88e688e4014087a0b592b695ed",
    ),
    (
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\
         aaaaa",
        0x80,
        "05b0bfef265dcee87654372777b7c44177e2ae4c13a27f103340d9cd11c86cb2\
         426ffcad5bd964080c2aee97f03be1ca18e30a1f14e27bc11ebbd650f305269c\
         c9fb1db08bf90bfc79b42a952b46daf810359e7bc36452684784a64952c343c5\
         2e5124cd1f71d474d5197fefc571a92929c9084ffe1112cf5eea5192ebff330b",
    ),
];

// --- Appendix J.5.1: edwards25519_XMD:SHA-512_ELL2_RO_ ---

const J51_EDWARDS25519_RO_DST: &str = "QUUX-V01-CS02-with-edwards25519_XMD:SHA-512_ELL2_RO_";

const J51_EDWARDS25519_RO: [(&str, [&str; 2]); 5] = [
    (
        "",
        ["03fef4813c8cb5f98c6eef88fae174e6e7d5380de2b007799ac7ee712d203f3a",
         "780bdddd137290c8f589dc687795aafae35f6b674668d92bf92ae793e6a60c75"],
    ),
    (
        "abc",
        ["5081955c4141e4e7d02ec0e36becffaa1934df4d7a270f70679c78f9bd57c227",
         "005bdc17a9b378b6272573a31b04361f21c371b256252ae5463119aa0b925b76"],
    ),
    (
        "abcdef0123456789",
        ["285ebaa3be701b79871bcb6e225ecc9b0b32dff2d60424b4c50642636a78d5b3",
         "2e253e6a0ef658fedb8e4bd6a62d1544fd6547922acb3598ec6b369760b81b31"],
    ),
    (
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        ["4fedd25431c41f2a606952e2945ef5e3ac905a42cf64b8b4d4a83c533bf321af",
         "02f20716a5801b843987097a8276b6d869295b2e11253751ca72c109d37485a9"],
    ),
    (
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        ["6e34e04a5106e9bd59f64aba49601bf09d23b27f7b594e56d5de06df4a4ea33b",
         "1c1c2cb59fc053f44b86c5d5eb8c1954b64976d0302d3729ff66e84068f5fd96"],
    ),
];

// --- Appendix J.5.2: edwards25519_XMD:SHA-512_ELL2_NU_ ---

const J52_EDWARDS25519_NU_DST: &str = "QUUX-V01-CS02-with-edwards25519_XMD:SHA-512_ELL2_NU_";

const J52_EDWARDS25519_NU: [(&str, [&str; 1]); 5] = [
    (
        "",
        ["7f3e7fb9428103ad7f52db32f9df32505d7b427d894c5093f7a0f0374a30641d"],
    ),
    (
        "abc",
        ["09cfa30ad79bd59456594a0f5d3a76f6b71c6787b04de98be5cd201a556e253b"],
    ),
    (
        "abcdef0123456789",
        ["475ccff99225ef90d78cc9338e9f6a6bb7b17607c0c4428937de75d33edba941"],
    ),
    (
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        ["049a1c8bd51bcb2aec339f387d1ff51428b88d0763a91bcdf6929814ac95d03d"],
    ),
    (
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        ["3cb0178a8137cefa5b79a3a57c858d7eeeaa787b2781be4a362a2f0750d24fa0"],
    ),
];

// --- Appendix J.1.1: P256_XMD:SHA-256_SSWU_RO_ ---

const J11_P256_RO_DST: &str = "QUUX-V01-CS02-with-P256_XMD:SHA-256_SSWU_RO_";

const J11_P256_RO: [(&str, [&str; 2]); 5] = [
    (
        "",
        ["ad5342c66a6dd0ff080df1da0ea1c04b96e0330dd89406465eeba11582515009",
         "8c0f1d43204bd6f6ea70ae8013070a1518b43873bcd850aafa0a9e220e2eea5a"],
    ),
    (
        "abc",
        ["afe47f2ea2b10465cc26ac403194dfb68b7f5ee865cda61e9f3e07a537220af1",
         "379a27833b0bfe6f7bdca08e1e83c760bf9a338ab335542704edcd69ce9e46e0"],
    ),
    (
        "abcdef0123456789",
        ["0fad9d125a9477d55cf9357105b0eb3a5c4259809bf87180aa01d651f53d312c",
         "b68597377392cd3419d8fcc7d7660948c8403b19ea78bbca4b133c9d2196c0fb"],
    ),
    (
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        ["3bbc30446f39a7befad080f4d5f32ed116b9534626993d2cc5033f6f8d805919",
         "76bb02db019ca9d3c1e02f0c17f8baf617bbdae5c393a81d9ce11e3be1bf1d33"],
    ),
    (
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        ["4ebc95a6e839b1ae3c63b847798e85cb3c12d3817ec6ebc10af6ee51adb29fec",
         "4e21af88e22ea80156aff790750121035b3eefaa96b425a8716e0d20b4e269ee"],
    ),
];

// --- Appendix J.1.2: P256_XMD:SHA-256_SSWU_NU_ ---

const J12_P256_NU_DST: &str = "QUUX-V01-CS02-with-P256_XMD:SHA-256_SSWU_NU_";

const J12_P256_NU: [(&str, [&str; 1]); 5] = [
    (
        "",
        ["b22d487045f80e9edcb0ecc8d4bf77833e2bf1f3a54004d7df1d57f4802d311f"],
    ),
    (
        "abc",
        ["c7f96eadac763e176629b09ed0c11992225b3a5ae99479760601cbd69c221e58"],
    ),
    (
        "abcdef0123456789",
        ["314e8585fa92068b3ea2c3bab452d4257b38be1c097d58a21890456c2929614d"],
    ),
    (
        "q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        ["752d8eaa38cd785a799a31d63d99c2ae4261823b4a367b133b2c6627f48858ab"],
    ),
    (
        "a512_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        ["0e1527840b9df2dfbef966678ff167140f2b27c4dccd884c25014dce0e41dfa3"],
    ),
];

// --- Appendix K ---

#[test]
fn k1_expand_message_xmd_sha256() {
    for (msg, len_in_bytes, uniform_bytes) in K1_XMD_SHA256.iter() {
        let expected = hex::decode(uniform_bytes).unwrap();
        assert_eq!(expected.len(), *len_in_bytes);
        let got = expand_message_xmd_sha256(
            msg.as_bytes(),
            K1_XMD_SHA256_DST.as_bytes(),
            *len_in_bytes,
        );
        assert_eq!(got, Some(expected.clone()), "msg = {:?}", msg);
        // A DST of at most 255 bytes is used as given by the long-DST variant.
        let got_long = expand_message_xmd_sha256_long_dst(
            msg.as_bytes(),
            K1_XMD_SHA256_DST.as_bytes(),
            *len_in_bytes,
        );
        assert_eq!(got_long, Some(expected), "msg = {:?}", msg);
    }
}

#[test]
fn k2_expand_message_xmd_sha256_long_dst() {
    let dst = K2_XMD_SHA256_LONG_DST_DST.as_bytes();
    assert_eq!(dst.len(), 256);
    // DST_prime of Appendix K.2 without its final length byte 0x20.
    let short_dst = dst_oversize_sha256(dst);
    assert_eq!(
        short_dst.to_vec(),
        hex::decode("412717974da474d0f8c420f320ff81e8432adb7c927d9bd082b4fb4d16c0a236").unwrap()
    );
    assert_eq!(
        build_dst_prime(&short_dst),
        hex::decode("412717974da474d0f8c420f320ff81e8432adb7c927d9bd082b4fb4d16c0a23620").unwrap()
    );
    for (msg, len_in_bytes, uniform_bytes) in K2_XMD_SHA256_LONG_DST.iter() {
        let expected = hex::decode(uniform_bytes).unwrap();
        assert_eq!(expected.len(), *len_in_bytes);
        let got = expand_message_xmd_sha256_long_dst(msg.as_bytes(), dst, *len_in_bytes);
        assert_eq!(got, Some(expected.clone()), "msg = {:?}", msg);
        let got_short = expand_message_xmd_sha256(msg.as_bytes(), &short_dst, *len_in_bytes);
        assert_eq!(got_short, Some(expected), "msg = {:?}", msg);
        // Section 5.3.1 aborts on the 256-byte DST itself.
        assert_eq!(expand_message_xmd_sha256(msg.as_bytes(), dst, *len_in_bytes), None);
    }
}

#[test]
fn k3_expand_message_xmd_sha512() {
    for (msg, len_in_bytes, uniform_bytes) in K3_XMD_SHA512.iter() {
        let expected = hex::decode(uniform_bytes).unwrap();
        assert_eq!(expected.len(), *len_in_bytes);
        let got = expand_message_xmd_sha512(
            msg.as_bytes(),
            K3_XMD_SHA512_DST.as_bytes(),
            *len_in_bytes,
        );
        assert_eq!(got, Some(expected.clone()), "msg = {:?}", msg);
        let got_long = expand_message_xmd_sha512_long_dst(
            msg.as_bytes(),
            K3_XMD_SHA512_DST.as_bytes(),
            *len_in_bytes,
        );
        assert_eq!(got_long, Some(expected), "msg = {:?}", msg);
    }
}

#[test]
fn dst_prime_matches_appendix_k() {
    assert_eq!(
        build_dst_prime(K1_XMD_SHA256_DST.as_bytes()),
        hex::decode(
            "515555582d5630312d435330322d776974682d657870616e6465722d5348413235362d31323826"
        )
        .unwrap()
    );
    assert_eq!(
        build_dst_prime(K3_XMD_SHA512_DST.as_bytes()),
        hex::decode(
            "515555582d5630312d435330322d776974682d657870616e6465722d5348413531322d32353626"
        )
        .unwrap()
    );
}

#[test]
fn oversize_dst_prefix_is_ascii() {
    assert_eq!(&OVERSIZE_DST_PREFIX[..], &b"H2C-OVERSIZE-DST-"[..]);
}

// --- Section 5.3.1, step 2: abort conditions ---

#[test]
fn expand_message_xmd_sha256_aborts() {
    let dst = K1_XMD_SHA256_DST.as_bytes();
    // ell = 255 is the largest block count: 255 * 32 = 8160 bytes.
    assert_eq!(expand_message_xmd_sha256(b"abc", dst, 8160).map(|v| v.len()), Some(8160));
    // ell = 256 > 255.
    assert_eq!(expand_message_xmd_sha256(b"abc", dst, 8161), None);
    // len_in_bytes > 65535.
    assert_eq!(expand_message_xmd_sha256(b"abc", dst, 65536), None);
    assert_eq!(expand_message_xmd_sha256_long_dst(b"abc", dst, 8161), None);
    assert_eq!(expand_message_xmd_sha256_long_dst(b"abc", dst, 65536), None);
    // len(DST) = 255 is accepted, len(DST) = 256 aborts.
    let dst_255 = [0x41u8; 255];
    let dst_256 = [0x41u8; 256];
    assert_eq!(expand_message_xmd_sha256(b"abc", &dst_255, 32).map(|v| v.len()), Some(32));
    assert_eq!(expand_message_xmd_sha256(b"abc", &dst_256, 32), None);
    // len_in_bytes = 0 gives the empty string.
    assert_eq!(expand_message_xmd_sha256(b"abc", dst, 0), Some(Vec::new()));
}

#[test]
fn expand_message_xmd_sha512_aborts() {
    let dst = K3_XMD_SHA512_DST.as_bytes();
    // ell = 255 is the largest block count: 255 * 64 = 16320 bytes.
    assert_eq!(expand_message_xmd_sha512(b"abc", dst, 16320).map(|v| v.len()), Some(16320));
    // ell = 256 > 255.
    assert_eq!(expand_message_xmd_sha512(b"abc", dst, 16321), None);
    // len_in_bytes > 65535.
    assert_eq!(expand_message_xmd_sha512(b"abc", dst, 65536), None);
    assert_eq!(expand_message_xmd_sha512_long_dst(b"abc", dst, 16321), None);
    assert_eq!(expand_message_xmd_sha512_long_dst(b"abc", dst, 65536), None);
    // len(DST) = 255 is accepted, len(DST) = 256 aborts.
    let dst_255 = [0x41u8; 255];
    let dst_256 = [0x41u8; 256];
    assert_eq!(expand_message_xmd_sha512(b"abc", &dst_255, 32).map(|v| v.len()), Some(32));
    assert_eq!(expand_message_xmd_sha512(b"abc", &dst_256, 32), None);
    // The long-DST variant hashes the 256-byte DST (Section 5.3.3).
    assert_eq!(
        expand_message_xmd_sha512_long_dst(b"abc", &dst_256, 32),
        expand_message_xmd_sha512(b"abc", &dst_oversize_sha512(&dst_256), 32)
    );
    // len_in_bytes = 0 gives the empty string.
    assert_eq!(expand_message_xmd_sha512(b"abc", dst, 0), Some(Vec::new()));
}

#[test]
fn hash_to_field_aborts() {
    let dst_256 = [0x41u8; 256];
    let dst = J51_EDWARDS25519_RO_DST.as_bytes();
    // count * 48 = 16320 = 255 * 64 is the largest SHA-512 request.
    assert_eq!(hash_to_field_25519_sha512(b"abc", dst, 340).map(|u| u.len()), Some(340));
    assert_eq!(hash_to_field_25519_sha512(b"abc", dst, 341), None);
    assert_eq!(hash_to_field_25519_sha512(b"abc", dst, 1366), None);
    assert_eq!(hash_to_field_25519_sha512(b"abc", &dst_256, 2), None);
    assert_eq!(hash_to_field_25519_sha512(b"abc", dst, 0), Some(Vec::new()));
    // count * 48 = 8160 = 255 * 32 is the largest SHA-256 request.
    let dst = J11_P256_RO_DST.as_bytes();
    assert_eq!(hash_to_field_p256_sha256(b"abc", dst, 170).map(|u| u.len()), Some(170));
    assert_eq!(hash_to_field_p256_sha256(b"abc", dst, 171), None);
    assert_eq!(hash_to_field_p256_sha256(b"abc", dst, 1366), None);
    assert_eq!(hash_to_field_p256_sha256(b"abc", &dst_256, 2), None);
    assert_eq!(hash_to_field_p256_sha256(b"abc", dst, 0), Some(Vec::new()));
}

// --- OS2IP(tv) mod p ---

/// The canonical big-endian encoding of a GF(2^255 - 19) element, as printed
/// in Appendix J: `fe_to_bytes` is little-endian.
fn fe25519_to_be_hex(a: [u64; 5]) -> String {
    let mut bytes = fe_to_bytes(a);
    bytes.reverse();
    hex::encode(bytes)
}

#[test]
fn fe25519_from_be48_reduces() {
    let mut tv = [0u8; 48];
    assert_eq!(fe25519_to_be_hex(fe25519_from_be48(&tv)), "00".repeat(32));
    // tv = 1.
    tv[47] = 1;
    assert_eq!(
        fe25519_to_be_hex(fe25519_from_be48(&tv)),
        format!("{}01", "00".repeat(31))
    );
    // tv = p = 2^255 - 19 reduces to 0.
    let mut tv = [0u8; 48];
    tv[16] = 0x7f;
    for i in 17..47 {
        tv[i] = 0xff;
    }
    tv[47] = 0xed;
    assert_eq!(fe25519_to_be_hex(fe25519_from_be48(&tv)), "00".repeat(32));
    // tv = 2^255 reduces to 19.
    let mut tv = [0u8; 48];
    tv[16] = 0x80;
    assert_eq!(
        fe25519_to_be_hex(fe25519_from_be48(&tv)),
        format!("{}13", "00".repeat(31))
    );
    // tv = 2^384 - 1 = 2^129 * 2^255 - 1 reduces to 19 * 2^129 - 1
    // = 0x25ffff...ff (2 + 128 / 4 hexadecimal digits).
    let tv = [0xffu8; 48];
    assert_eq!(
        fe25519_to_be_hex(fe25519_from_be48(&tv)),
        format!("{}25{}", "00".repeat(15), "ff".repeat(16))
    );
}

#[test]
fn fp256_from_be48_reduces() {
    let mut tv = [0u8; 48];
    assert_eq!(hex::encode(fp_to_bytes(fp256_from_be48(&tv))), "00".repeat(32));
    // tv = p reduces to 0.
    let p = hex::decode("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff")
        .unwrap();
    for i in 0..32 {
        tv[16 + i] = p[i];
    }
    assert_eq!(hex::encode(fp_to_bytes(fp256_from_be48(&tv))), "00".repeat(32));
    // tv = 2^256 reduces to 2^224 - 2^192 - 2^96 + 1.
    let mut tv = [0u8; 48];
    tv[15] = 1;
    assert_eq!(
        hex::encode(fp_to_bytes(fp256_from_be48(&tv))),
        "00000000fffffffeffffffffffffffffffffffff000000000000000000000001"
    );
    assert_eq!(
        hex::encode(fp_to_bytes(P256_TWO_256)),
        "00000000fffffffeffffffffffffffffffffffff000000000000000000000001"
    );
}

// --- Appendix J: hash_to_field ---

#[test]
fn j51_hash_to_field_edwards25519_ro() {
    for (msg, u) in J51_EDWARDS25519_RO.iter() {
        let got = hash_to_field_25519_sha512(msg.as_bytes(), J51_EDWARDS25519_RO_DST.as_bytes(), 2)
            .unwrap();
        assert_eq!(got.len(), 2);
        for i in 0..2 {
            assert_eq!(fe25519_to_be_hex(got[i]), u[i], "msg = {:?}, u[{}]", msg, i);
        }
    }
}

#[test]
fn j52_hash_to_field_edwards25519_nu() {
    for (msg, u) in J52_EDWARDS25519_NU.iter() {
        let got = hash_to_field_25519_sha512(msg.as_bytes(), J52_EDWARDS25519_NU_DST.as_bytes(), 1)
            .unwrap();
        assert_eq!(got.len(), 1);
        assert_eq!(fe25519_to_be_hex(got[0]), u[0], "msg = {:?}", msg);
    }
}

#[test]
fn j11_hash_to_field_p256_ro() {
    for (msg, u) in J11_P256_RO.iter() {
        let got =
            hash_to_field_p256_sha256(msg.as_bytes(), J11_P256_RO_DST.as_bytes(), 2).unwrap();
        assert_eq!(got.len(), 2);
        for i in 0..2 {
            assert_eq!(hex::encode(fp_to_bytes(got[i])), u[i], "msg = {:?}, u[{}]", msg, i);
        }
    }
}

#[test]
fn j12_hash_to_field_p256_nu() {
    for (msg, u) in J12_P256_NU.iter() {
        let got =
            hash_to_field_p256_sha256(msg.as_bytes(), J12_P256_NU_DST.as_bytes(), 1).unwrap();
        assert_eq!(got.len(), 1);
        assert_eq!(hex::encode(fp_to_bytes(got[0])), u[0], "msg = {:?}", msg);
    }
}
