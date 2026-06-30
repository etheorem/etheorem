import LeanPoseidon.Field

/-!
# `LeanPoseidon.Poseidon2.Params`: instance data + the pinned constants

**This file is generated** by `scripts/gen_poseidon_params.py` from the
pinned `scripts/poseidon2_*.json` data files (HorizenLabs `zkhash` v0.2.0);
do not edit by hand. Run `just poseidon-gen-params` to regenerate. The
generator header documents the sources and the flattening layout.

## What a Poseidon2 instance is (for the Lean-fluent reader)

A Poseidon2 *permutation* mixes a *state* of `t` field elements through a
sequence of rounds. A *full round* applies the non-linear S-box `x ↦ xᵈ` to
all `t` elements; a *partial round* applies it to one element only (cheaper,
most rounds are partial). *Round constants* (ARK = "add round key") are
added before each S-box layer; between S-box layers a *linear layer* (a
matrix multiply, see `Poseidon2/LinearLayers.lean`) diffuses the state.
Capturing all of this as *data* (rather than hardcoding) follows CLAUDE.md's
"configure, don't integrate" and makes a new instance, even over a new
*field*, new data, not new code (Open/Closed).
-/

set_option autoImplicit false

namespace LeanPoseidon.Poseidon2

/-- A Poseidon2 instance captured as data, generic over the coefficient type
`R`. The shipped layers/permutation specialise the *width* to `t = 3`
(`Vector R 3`); the *field* is whatever `R` the instance is built over (the
field abstraction, ARCHITECTURE.md §3). -/
structure Params (R : Type) where
  /-- State width (number of field elements). -/
  t : Nat
  /-- `R_f`: total full rounds, split half before / half after the partial
  rounds. -/
  fullRounds : Nat
  /-- `R_p`: partial rounds (S-box on element 0 only). -/
  partialRounds : Nat
  /-- S-box exponent `d` (= 5 for the shipped instances). -/
  sboxDegree : Nat
  /-- Flattened ARK ("add round key") constants: beginning full rounds (all
  `t` entries each), partial rounds (entry 0 only), end full rounds (all `t`
  entries). For `t = 3` that is `8·3 + 56 = 80`. `Poseidon2/Permutation.lean`
  indexes it with exactly this layout. -/
  roundConstants : Array R
  /-- The internal linear layer's matrix diagonal, length `t`. For the t=3
  instances it is `[2,2,3]`; the dense internal matrix is
  `J + diag(intDiagᵢ − 1)`. See `Poseidon2/LinearLayers.lean`. -/
  intDiag : Array R

/-- Pinned BN254/BLS-style Poseidon2 instance `bn254Params` over `Bn254Fr`,
generated from `zkhash` v0.2.0 (see the generator header). `Bn254Fr.ofNat`
reduces each literal mod the modulus; every constant is already canonical. -/
def bn254Params : Params Bn254Fr where
  t := 3
  fullRounds := 8
  partialRounds := 56
  sboxDegree := 5
  roundConstants := #[
    -- beginning full rounds 0..3 (3 entries each)
    Bn254Fr.ofNat 0x1d066a255517b7fd8bddd3a93f7804ef7f8fcde48bb4c37a59a09a1a97052816,
    Bn254Fr.ofNat 0x29daefb55f6f2dc6ac3f089cebcc6120b7c6fef31367b68eb7238547d32c1610,
    Bn254Fr.ofNat 0x1f2cb1624a78ee001ecbd88ad959d7012572d76f08ec5c4f9e8b7ad7b0b4e1d1,
    Bn254Fr.ofNat 0x0aad2e79f15735f2bd77c0ed3d14aa27b11f092a53bbc6e1db0672ded84f31e5,
    Bn254Fr.ofNat 0x2252624f8617738cd6f661dd4094375f37028a98f1dece66091ccf1595b43f28,
    Bn254Fr.ofNat 0x1a24913a928b38485a65a84a291da1ff91c20626524b2b87d49f4f2c9018d735,
    Bn254Fr.ofNat 0x22fc468f1759b74d7bfc427b5f11ebb10a41515ddff497b14fd6dae1508fc47a,
    Bn254Fr.ofNat 0x1059ca787f1f89ed9cd026e9c9ca107ae61956ff0b4121d5efd65515617f6e4d,
    Bn254Fr.ofNat 0x02be9473358461d8f61f3536d877de982123011f0bf6f155a45cbbfae8b981ce,
    Bn254Fr.ofNat 0x0ec96c8e32962d462778a749c82ed623aba9b669ac5b8736a1ff3a441a5084a4,
    Bn254Fr.ofNat 0x292f906e073677405442d9553c45fa3f5a47a7cdb8c99f9648fb2e4d814df57e,
    Bn254Fr.ofNat 0x274982444157b86726c11b9a0f5e39a5cc611160a394ea460c63f0b2ffe5657e,
    -- partial rounds (entry 0 only)
    Bn254Fr.ofNat 0x1a1d063e54b1e764b63e1855bff015b8cedd192f47308731499573f23597d4b5,
    Bn254Fr.ofNat 0x26abc66f3fdf8e68839d10956259063708235dccc1aa3793b91b002c5b257c37,
    Bn254Fr.ofNat 0x0c7c64a9d887385381a578cfed5aed370754427aabca92a70b3c2b12ff4d7be8,
    Bn254Fr.ofNat 0x1cf5998769e9fab79e17f0b6d08b2d1eba2ebac30dc386b0edd383831354b495,
    Bn254Fr.ofNat 0x0f5e3a8566be31b7564ca60461e9e08b19828764a9669bc17aba0b97e66b0109,
    Bn254Fr.ofNat 0x18df6a9d19ea90d895e60e4db0794a01f359a53a180b7d4b42bf3d7a531c976e,
    Bn254Fr.ofNat 0x04f7bf2c5c0538ac6e4b782c3c6e601ad0ea1d3a3b9d25ef4e324055fa3123dc,
    Bn254Fr.ofNat 0x29c76ce22255206e3c40058523748531e770c0584aa2328ce55d54628b89ebe6,
    Bn254Fr.ofNat 0x198d425a45b78e85c053659ab4347f5d65b1b8e9c6108dbe00e0e945dbc5ff15,
    Bn254Fr.ofNat 0x25ee27ab6296cd5e6af3cc79c598a1daa7ff7f6878b3c49d49d3a9a90c3fdf74,
    Bn254Fr.ofNat 0x138ea8e0af41a1e024561001c0b6eb1505845d7d0c55b1b2c0f88687a96d1381,
    Bn254Fr.ofNat 0x306197fb3fab671ef6e7c2cba2eefd0e42851b5b9811f2ca4013370a01d95687,
    Bn254Fr.ofNat 0x1a0c7d52dc32a4432b66f0b4894d4f1a21db7565e5b4250486419eaf00e8f620,
    Bn254Fr.ofNat 0x2b46b418de80915f3ff86a8e5c8bdfccebfbe5f55163cd6caa52997da2c54a9f,
    Bn254Fr.ofNat 0x12d3e0dc0085873701f8b777b9673af9613a1af5db48e05bfb46e312b5829f64,
    Bn254Fr.ofNat 0x263390cf74dc3a8870f5002ed21d089ffb2bf768230f648dba338a5cb19b3a1f,
    Bn254Fr.ofNat 0x0a14f33a5fe668a60ac884b4ca607ad0f8abb5af40f96f1d7d543db52b003dcd,
    Bn254Fr.ofNat 0x28ead9c586513eab1a5e86509d68b2da27be3a4f01171a1dd847df829bc683b9,
    Bn254Fr.ofNat 0x1c6ab1c328c3c6430972031f1bdb2ac9888f0ea1abe71cffea16cda6e1a7416c,
    Bn254Fr.ofNat 0x1fc7e71bc0b819792b2500239f7f8de04f6decd608cb98a932346015c5b42c94,
    Bn254Fr.ofNat 0x03e107eb3a42b2ece380e0d860298f17c0c1e197c952650ee6dd85b93a0ddaa8,
    Bn254Fr.ofNat 0x2d354a251f381a4669c0d52bf88b772c46452ca57c08697f454505f6941d78cd,
    Bn254Fr.ofNat 0x094af88ab05d94baf687ef14bc566d1c522551d61606eda3d14b4606826f794b,
    Bn254Fr.ofNat 0x19705b783bf3d2dc19bcaeabf02f8ca5e1ab5b6f2e3195a9d52b2d249d1396f7,
    Bn254Fr.ofNat 0x09bf4acc3a8bce3f1fcc33fee54fc5b28723b16b7d740a3e60cef6852271200e,
    Bn254Fr.ofNat 0x1803f8200db6013c50f83c0c8fab62843413732f301f7058543a073f3f3b5e4e,
    Bn254Fr.ofNat 0x0f80afb5046244de30595b160b8d1f38bf6fb02d4454c0add41f7fef2faf3e5c,
    Bn254Fr.ofNat 0x126ee1f8504f15c3d77f0088c1cfc964abcfcf643f4a6fea7dc3f98219529d78,
    Bn254Fr.ofNat 0x23c203d10cfcc60f69bfb3d919552ca10ffb4ee63175ddf8ef86f991d7d0a591,
    Bn254Fr.ofNat 0x2a2ae15d8b143709ec0d09705fa3a6303dec1ee4eec2cf747c5a339f7744fb94,
    Bn254Fr.ofNat 0x07b60dee586ed6ef47e5c381ab6343ecc3d3b3006cb461bbb6b5d89081970b2b,
    Bn254Fr.ofNat 0x27316b559be3edfd885d95c494c1ae3d8a98a320baa7d152132cfe583c9311bd,
    Bn254Fr.ofNat 0x1d5c49ba157c32b8d8937cb2d3f84311ef834cc2a743ed662f5f9af0c0342e76,
    Bn254Fr.ofNat 0x2f8b124e78163b2f332774e0b850b5ec09c01bf6979938f67c24bd5940968488,
    Bn254Fr.ofNat 0x1e6843a5457416b6dc5b7aa09a9ce21b1d4cba6554e51d84665f75260113b3d5,
    Bn254Fr.ofNat 0x11cdf00a35f650c55fca25c9929c8ad9a68daf9ac6a189ab1f5bc79f21641d4b,
    Bn254Fr.ofNat 0x21632de3d3bbc5e42ef36e588158d6d4608b2815c77355b7e82b5b9b7eb560bc,
    Bn254Fr.ofNat 0x0de625758452efbd97b27025fbd245e0255ae48ef2a329e449d7b5c51c18498a,
    Bn254Fr.ofNat 0x2ad253c053e75213e2febfd4d976cc01dd9e1e1c6f0fb6b09b09546ba0838098,
    Bn254Fr.ofNat 0x1d6b169ed63872dc6ec7681ec39b3be93dd49cdd13c813b7d35702e38d60b077,
    Bn254Fr.ofNat 0x1660b740a143664bb9127c4941b67fed0be3ea70a24d5568c3a54e706cfef7fe,
    Bn254Fr.ofNat 0x0065a92d1de81f34114f4ca2deef76e0ceacdddb12cf879096a29f10376ccbfe,
    Bn254Fr.ofNat 0x1f11f065202535987367f823da7d672c353ebe2ccbc4869bcf30d50a5871040d,
    Bn254Fr.ofNat 0x26596f5c5dd5a5d1b437ce7b14a2c3dd3bd1d1a39b6759ba110852d17df0693e,
    Bn254Fr.ofNat 0x16f49bc727e45a2f7bf3056efcf8b6d38539c4163a5f1e706743db15af91860f,
    Bn254Fr.ofNat 0x1abe1deb45b3e3119954175efb331bf4568feaf7ea8b3dc5e1a4e7438dd39e5f,
    Bn254Fr.ofNat 0x0e426ccab66984d1d8993a74ca548b779f5db92aaec5f102020d34aea15fba59,
    Bn254Fr.ofNat 0x0e7c30c2e2e8957f4933bd1942053f1f0071684b902d534fa841924303f6a6c6,
    Bn254Fr.ofNat 0x0812a017ca92cf0a1622708fc7edff1d6166ded6e3528ead4c76e1f31d3fc69d,
    Bn254Fr.ofNat 0x21a5ade3df2bc1b5bba949d1db96040068afe5026edd7a9c2e276b47cf010d54,
    Bn254Fr.ofNat 0x01f3035463816c84ad711bf1a058c6c6bd101945f50e5afe72b1a5233f8749ce,
    Bn254Fr.ofNat 0x0b115572f038c0e2028c2aafc2d06a5e8bf2f9398dbd0fdf4dcaa82b0f0c1c8b,
    Bn254Fr.ofNat 0x1c38ec0b99b62fd4f0ef255543f50d2e27fc24db42bc910a3460613b6ef59e2f,
    Bn254Fr.ofNat 0x1c89c6d9666272e8425c3ff1f4ac737b2f5d314606a297d4b1d0b254d880c53e,
    Bn254Fr.ofNat 0x03326e643580356bf6d44008ae4c042a21ad4880097a5eb38b71e2311bb88f8f,
    Bn254Fr.ofNat 0x268076b0054fb73f67cee9ea0e51e3ad50f27a6434b5dceb5bdde2299910a4c9,
    -- end full rounds (3 entries each)
    Bn254Fr.ofNat 0x1acd63c67fbc9ab1626ed93491bda32e5da18ea9d8e4f10178d04aa6f8747ad0,
    Bn254Fr.ofNat 0x19f8a5d670e8ab66c4e3144be58ef6901bf93375e2323ec3ca8c86cd2a28b5a5,
    Bn254Fr.ofNat 0x1c0dc443519ad7a86efa40d2df10a011068193ea51f6c92ae1cfbb5f7b9b6893,
    Bn254Fr.ofNat 0x14b39e7aa4068dbe50fe7190e421dc19fbeab33cb4f6a2c4180e4c3224987d3d,
    Bn254Fr.ofNat 0x1d449b71bd826ec58f28c63ea6c561b7b820fc519f01f021afb1e35e28b0795e,
    Bn254Fr.ofNat 0x1ea2c9a89baaddbb60fa97fe60fe9d8e89de141689d1252276524dc0a9e987fc,
    Bn254Fr.ofNat 0x0478d66d43535a8cb57e9c1c3d6a2bd7591f9a46a0e9c058134d5cefdb3c7ff1,
    Bn254Fr.ofNat 0x19272db71eece6a6f608f3b2717f9cd2662e26ad86c400b21cde5e4a7b00bebe,
    Bn254Fr.ofNat 0x14226537335cab33c749c746f09208abb2dd1bd66a87ef75039be846af134166,
    Bn254Fr.ofNat 0x01fd6af15956294f9dfe38c0d976a088b21c21e4a1c2e823f912f44961f9a9ce,
    Bn254Fr.ofNat 0x18e5abedd626ec307bca190b8b2cab1aaee2e62ed229ba5a5ad8518d4e5f2a57,
    Bn254Fr.ofNat 0x0fc1bbceba0590f5abbdffa6d3b35e3297c021a3a409926d0e2d54dc1c84fda6
  ]
  intDiag := #[Bn254Fr.ofNat 2, Bn254Fr.ofNat 2, Bn254Fr.ofNat 3]

/-! ## Shape gates -/
#guard bn254Params.t = 3
#guard bn254Params.fullRounds = 8
#guard bn254Params.partialRounds = 56
#guard bn254Params.roundConstants.size = 80
#guard bn254Params.intDiag.size = 3

/-- Pinned BN254/BLS-style Poseidon2 instance `bls12Params` over `Bls12Fr`,
generated from `zkhash` v0.2.0 (see the generator header). `Bls12Fr.ofNat`
reduces each literal mod the modulus; every constant is already canonical. -/
def bls12Params : Params Bls12Fr where
  t := 3
  fullRounds := 8
  partialRounds := 56
  sboxDegree := 5
  roundConstants := #[
    -- beginning full rounds 0..3 (3 entries each)
    Bls12Fr.ofNat 0x6f007a551156b3a449e44936b7c093644a0ed33f33eaccc628e942e836c1a875,
    Bls12Fr.ofNat 0x360d7470611e473d353f628f76d110f34e71162f31003b7057538c2596426303,
    Bls12Fr.ofNat 0x4b5fec3aa073df44019091f007a44ca996484965f7036dce3e9d0977edcdc0f6,
    Bls12Fr.ofNat 0x67cf1868af6396c0b84cce715e539f849e06cd1c383ac5b06100c76bcc973a11,
    Bls12Fr.ofNat 0x555db4d1dced819f5d3de70fde83f1c7d3e8c98968e516a23a771a5c9c8257aa,
    Bls12Fr.ofNat 0x2bab94d7ae222d135dc3c6c5febfaa314908ac2f12ebe06fbdb74213bf63188b,
    Bls12Fr.ofNat 0x66f44be5296682c4fa7882799d6dd049b6d7d2c950ccf98cf2e50d6d1ebb77c2,
    Bls12Fr.ofNat 0x150c93fef652fb1c2bf03e1a29aa871fef77e7d736766c5d0939d92753cc5dc8,
    Bls12Fr.ofNat 0x3270661e68928b3a955d55db56dc57c103cc0a60141e894e14259dce537782b2,
    Bls12Fr.ofNat 0x073f116f04122e25a0b7afe4e2057299b407c370f2b5a1ccce9fb9ffc345afb3,
    Bls12Fr.ofNat 0x409fda22558cfe4d3dd8dce24f69e76f8c2aaeb1dd0f09d65e654c71f32aa23f,
    Bls12Fr.ofNat 0x2a32ec5c4ee5b1837affd09c1f53f5fd55c9cd2061ae93ca8ebad76fc71554d8,
    -- partial rounds (entry 0 only)
    Bls12Fr.ofNat 0x5848ebeb5923e92555b7124fffba5d6bd571c6f984195eb9cfd3a3e8eb55b1d4,
    Bls12Fr.ofNat 0x270326ee039df19e651e2cfc740628ca634d24fc6e2559f22d8ccbe292efeead,
    Bls12Fr.ofNat 0x27c6642ac633bc66dc100fe7fcfa54918af895bce012f182a068fc37c182e274,
    Bls12Fr.ofNat 0x1bdfd8b01401c70ad27f57396989129d710e1fb6ab976a459ca18682e26d7ff9,
    Bls12Fr.ofNat 0x491b9ba6983bcf9f05fe4794adb44a30879bf8289662e1f57d90f672414e8a4a,
    Bls12Fr.ofNat 0x162a14c62f9a89b814b9d6a9c84dd678f4f6fb3f9054d373c832d824261a35ea,
    Bls12Fr.ofNat 0x2d193e0f76de586b2af6f79e3127feeaac0a1fc71e2cf0c0f79824667b5b6bec,
    Bls12Fr.ofNat 0x46efd8a9a262d6d8fdc9ca5c04b0982f24ddcc6e9863885a6a732a3906a07b95,
    Bls12Fr.ofNat 0x509717e0c200e3c92d8dca2973b3db45f0788294351ad07ae75cbb780693a798,
    Bls12Fr.ofNat 0x7299b28464a8c94fb9d4df61380f39c0dca9c2c014118789e227252820f01bfc,
    Bls12Fr.ofNat 0x044ca3cc4a85d73b81696ef1104e674f4feff82984990ff85d0bf58dc8a4aa94,
    Bls12Fr.ofNat 0x1cbaf2b371dac6a81d0453416d3e235cb8d9e2d4f314f46f6198785f0cd6b9af,
    Bls12Fr.ofNat 0x1d5b2777692c205b0e6c49d061b6b5f4293c4ab038fdbbdc343e07610f3fede5,
    Bls12Fr.ofNat 0x56ae7c7a5293bdc23e85e1698c81c77f8ad88c4b33a5780437ad047c6edb59ba,
    Bls12Fr.ofNat 0x2e9bdbba3dd34bffaa30535bdd749a7e06a9adb0c1e6f962f60e971b8d73b04f,
    Bls12Fr.ofNat 0x2de11886b18011ca8bd5bae36969299fde40fbe26d047b05035a13661f22418b,
    Bls12Fr.ofNat 0x2e07de1780b8a70d0d5b4a3f1841dcd82ab9395c449be947bc998884ba96a721,
    Bls12Fr.ofNat 0x0f69f1854d20ca0cbbdb63dbd52dad16250440a99d6b8af3825e4c2bb74925ca,
    Bls12Fr.ofNat 0x5dc987318e6e59c1afb87b655dd58cc1d22e513a05838cd4585d04b135b957ca,
    Bls12Fr.ofNat 0x48b725758571c9df6c01dc639a85f07297696b1bb678633a29dc91de95ef53f6,
    Bls12Fr.ofNat 0x5e565e08c0821099256b56490eaee1d573afd10bb6d17d13ca4e5c611b2a3718,
    Bls12Fr.ofNat 0x2eb1b25417fe17670d135dc639fb09a46ce5113507f96de9816c059422dc705e,
    Bls12Fr.ofNat 0x115cd0a0643cfb988c24cb44c3fab48aff36c661d26cc42db8b1bdf4953bd82c,
    Bls12Fr.ofNat 0x26ca293f7b2c462d066d7378b999868bbb57ddf14e0f958ade801612311d04cd,
    Bls12Fr.ofNat 0x4147400d8e1aaccf311a6b5b762011ab3e45326e4d4b9de26992816b99c528ac,
    Bls12Fr.ofNat 0x6b0db7dccc4ba1b268f6bdcc4d372848d4a72976c268ea30519a2f73e6db4d55,
    Bls12Fr.ofNat 0x17bf1b93c4c7e01a2a830aa162412cd90f160bf9f71e967ff5209d14b24820ca,
    Bls12Fr.ofNat 0x4b431cd9efedbc94cf1eca6f9e9c1839d0e66a8bffa8c8464cac81a39d3cf8f1,
    Bls12Fr.ofNat 0x35b41a7ac4f3c571a24f8456369c85dfe03c0354bd8cfd3805c86f2e7dc293c5,
    Bls12Fr.ofNat 0x3b1480080523c439435927994849bea964e14d3beb2dddde72ac156af435d09e,
    Bls12Fr.ofNat 0x2cc6810031dc1b0d4950856dc907d57508e286442a2d3eb2271618d874b14c6d,
    Bls12Fr.ofNat 0x6f4141c8401c5a395ba6790efd71c70c04afea06c3c92826bcabdd5cb5477d51,
    Bls12Fr.ofNat 0x25bdbbeda1bde8c1059618e2afd2ef999e517aa93b78341d91f318c09f0cb566,
    Bls12Fr.ofNat 0x392a4a8758e06ee8b95f33c25dde8ac02a5ed0a27b61926cc6313487073f7f7b,
    Bls12Fr.ofNat 0x272a55878a08442b9aa6111f4de009485e6a6fd15db89365e7bbcef02eb5866c,
    Bls12Fr.ofNat 0x631ec1d6d28dd9e824ee89a30730aef7ab463acfc9d184b355aa05fd6938eab5,
    Bls12Fr.ofNat 0x4eb6fda10fd0fbde02c7449bfbddc35bcd8225e7e5c3833a0818a100409dc6f2,
    Bls12Fr.ofNat 0x2d5b308b0cf02cdfefa13c4e60e26239a6ebba011694dd129b925b3c5b21e0e2,
    Bls12Fr.ofNat 0x16549fc6af2f3b72dd5d293d72e2e5f244dff42f18b46c56ef38c57c311673ac,
    Bls12Fr.ofNat 0x42332677ff359c5e8db836d9f5fb54822e39bd5e22340bb9ba975ba1a92be382,
    Bls12Fr.ofNat 0x49d7d2c0b449e5179bc5ccc3b44c6075d9849b5610465f09ea725ddc97723a94,
    Bls12Fr.ofNat 0x64c20fb90d7a003831757cc4c6226f6e4985fc9ecb416b9f684ca0351d967904,
    Bls12Fr.ofNat 0x59cff40de83b52b41bc443d7979510d771c940b9758ca820fe73b5c8d5580934,
    Bls12Fr.ofNat 0x53db2731730c39b04edd875fe3b7c882808285cdbc621d7af4f80dd53ebb71b0,
    Bls12Fr.ofNat 0x1b10bb7a82afce39fa69c3a2ad52f76d76398265344203119b7126d9b46860df,
    Bls12Fr.ofNat 0x561b6012d666bfe179c4dd7f84cdd1531596d3aac7c5700ceb319f91046a63c9,
    Bls12Fr.ofNat 0x0f1e7505ebd91d2fc79c2df7dc98a3bed1b36968ba0405c090d27f6a00b7dfc8,
    Bls12Fr.ofNat 0x2f313faf0d3f6187537a7497a3b43f46797fd6e3f18eb1caff457756b819bb20,
    Bls12Fr.ofNat 0x3a5cbb6de450b481fa3ca61c0ed15bc55cad11ebf0f7ceb8f0bc3e732ecb26f6,
    Bls12Fr.ofNat 0x681d93411bf8ce63f6716aefbd0e24506454c0348ee38fabeb264702714ccf94,
    Bls12Fr.ofNat 0x5178e940f50004312646b436727f0e80a7b8f2e9ee1fdc677c4831a7672777fb,
    Bls12Fr.ofNat 0x3dab54bc9bef688dd92086e253b439d651baa6e20f892b62865527cbca915982,
    Bls12Fr.ofNat 0x4b3ce75311218f9ae905f84eaa5b2b3818448bbf3972e1aad69de321009015d0,
    Bls12Fr.ofNat 0x06dbfb42b979884de280d31670123f744c24b33b410fefd4368045acf2b71ae3,
    Bls12Fr.ofNat 0x068d6b4608aae810c6f039ea1973a63eb8d2de72e3d2c9eca7fc32d22f18b9d3,
    Bls12Fr.ofNat 0x4c5c254589a92a36084a57d3b1d964278acc7e4fe8f69f2955954f27a79cebef,
    -- end full rounds (3 entries each)
    Bls12Fr.ofNat 0x6cbac5e1700984ebc32da15b4bb9683faabab55f67ccc4f71d9560b3475a77eb,
    Bls12Fr.ofNat 0x4603c403bbfa9a17738a5c6278eaab1c37ec30b0737aa2409fc4898069eb983c,
    Bls12Fr.ofNat 0x6894e7e22b2c1d5c70a712a6345ae6b192a9c833a9234c31c56aacd16bc2f100,
    Bls12Fr.ofNat 0x5be2cbbc44053ad08afa4d1eabc7f3d231eea799b93f226e905b7d4d65c58ebb,
    Bls12Fr.ofNat 0x58e55f287b453a9808624a8c2a353d528da0f7e713a5c6d0d7711e47063fa611,
    Bls12Fr.ofNat 0x366ebfafa3ad381c0ee258c9b8fdfccdb868a7d7e1f1f69a2b5dfcc5572555df,
    Bls12Fr.ofNat 0x45766ab728968c642f90d97ccf5504ddc10518a819ebbcc4d09c3f5d784d67ce,
    Bls12Fr.ofNat 0x39678f65512f1ee404db3024f41d3f567ef66d89d044d022e6bc229e95bc76b1,
    Bls12Fr.ofNat 0x463aed1d2f1f955e3078be5bf7bfc46fc0eb8c51551906a8868f18ffae30cf4f,
    Bls12Fr.ofNat 0x21668f016a8063c0d58b7750a3bc2fe1cf82c25f99dc01a4e534c88fe53d85fe,
    Bls12Fr.ofNat 0x39d00994a8a5046a1bc749363e98a768e34dea56439fe1954bef429bc5331608,
    Bls12Fr.ofNat 0x4d7f5dcd78ece9a933984de32c0b48fac2bba91f261996b8e9d1021773bd07cc
  ]
  intDiag := #[Bls12Fr.ofNat 2, Bls12Fr.ofNat 2, Bls12Fr.ofNat 3]

/-! ## Shape gates -/
#guard bls12Params.t = 3
#guard bls12Params.fullRounds = 8
#guard bls12Params.partialRounds = 56
#guard bls12Params.roundConstants.size = 80
#guard bls12Params.intDiag.size = 3

end LeanPoseidon.Poseidon2
