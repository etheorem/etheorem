import LeanPoseidon

/-!
# `LeanPoseidonTests.Kat` — committed HorizenLabs `zkhash` t=3 vectors

A batch of fixed Poseidon2 permutation and 2-to-1 `compress` known-answer
tests, each a `native_decide` assertion against the pure-Lean
implementation, across **both shipped fields** (BN254 and BLS12-381 scalar
fields — the BLS vectors exercise the field abstraction through the *same*
generic `permute`). The expected outputs were produced by the **HorizenLabs
`zkhash` crate, version 0.2.0** (the same trusted reference the differential
test runs against), over a spread of inputs: small values, the boundary
residues `r−1, r−2, r−3`, and full-width field elements.

These fire on `lake build LeanPoseidonTests` (`just test-poseidon-vectors`)
and need **no Rust toolchain** — `native_decide` evaluates the pure-Lean
`permute` / `compress`. They are the broader, no-toolchain-needed anchor
set; the per-field `[0,1,2]` permutation anchors live in
`LeanPoseidon.Poseidon2.Permutation` and fire on `lake build LeanPoseidon`,
and the live differential test (`just fuzz-poseidon`) covers thousands more
inputs per field against the oracle at runtime.

Regenerate (when bumping the pinned reference) from the `rust-oracle`
crate; the values are otherwise stable and checked in, keeping CI's
no-Rust path hermetic.
-/

set_option autoImplicit false
-- A batch of full-permutation `native_decide` evaluations; raise the
-- heartbeat ceiling so the elaborator doesn't time out across the set.
set_option maxHeartbeats 2000000

namespace LeanPoseidonTests.Kat

open LeanPoseidon LeanPoseidon.Poseidon2

/-! ## Permutation vectors -/

example :
    permute bn254Params (#v[Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000, Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000, Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000])
      = #v[Bn254Fr.ofNat 0x2ed1da00b14d635bd35b88ab49390d5c13c90da7e9e3a5f1ea69cd87a0aa3e82,
           Bn254Fr.ofNat 0x1e21e979cc3fd844b88c2016fd18f4db07a698aa27deca67ca509f5b0a4480d0,
           Bn254Fr.ofNat 0x2c40d0115da2c9b55553b231be55295f411e628ed0cd0e187917066515f0a060] := by native_decide

example :
    permute bn254Params (#v[Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000001, Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000002, Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000003])
      = #v[Bn254Fr.ofNat 0x0a799a621cac2cea1ec6fdbcd5dc92cadd31c210c912aaca009aca578d210768,
           Bn254Fr.ofNat 0x1570f61795255f02ce99b299edfd70fad14b1f5c6b1856a12191be0e1598876a,
           Bn254Fr.ofNat 0x285e9571da987271dde96c087a306f402e722b76c3a25017694ce6e9b8dc3019] := by native_decide

example :
    permute bn254Params (#v[Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000007, Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000, Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000])
      = #v[Bn254Fr.ofNat 0x2d7349bb7251d7ea69af00f80d751a0e755f15c5dbe685916f9fa9beadeaf912,
           Bn254Fr.ofNat 0x2235b18e926c262c2bcaa0f925af38182776f7dffc591ff5424df2cb02bafa02,
           Bn254Fr.ofNat 0x238f2ad4fd0f74f6fdb22c7b2a25cca90d1ec5ba6c4ba002c2f8906255e7b192] := by native_decide

example :
    permute bn254Params (#v[Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000002, Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000003, Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000005])
      = #v[Bn254Fr.ofNat 0x2a643bdacdcda447f8434587a940913c30b6c7ce1110f235e728be16feb43d28,
           Bn254Fr.ofNat 0x2750c6ad6ac4cc8e3e6e9c417ba74c6f8ab0944324eb503159d23487155175d1,
           Bn254Fr.ofNat 0x0a88c6bd17de2334b2483496854d24ca0c98e327d927664861d8455fd6b130f1] := by native_decide

example :
    permute bn254Params (#v[Bn254Fr.ofNat 0x00000000000000000000000000000000000000000000000000000000075bcd15, Bn254Fr.ofNat 0x000000000000000000000000000000000000000000000000000000003ade68b1, Bn254Fr.ofNat 0x000000000000000000000000000000000000000000000000000000000000022b])
      = #v[Bn254Fr.ofNat 0x1e070ba068fc461c4b480d144ca34b0e2c0043a023dc9cc55b2d934d23960ce5,
           Bn254Fr.ofNat 0x21111032a1325ffb8cff1501700ccc0a2e56d6ac62f189e7fd79049b14bfd0ad,
           Bn254Fr.ofNat 0x2d3440cf33e6dbd53dc022ec02dac2d384da612e8df1398dacdf78f50bf9de2e] := by native_decide

example :
    permute bn254Params (#v[Bn254Fr.ofNat 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000, Bn254Fr.ofNat 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593efffffff, Bn254Fr.ofNat 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effffffe])
      = #v[Bn254Fr.ofNat 0x2d0aec82382f6f38d0b1362cd221eb5c88575954917ceb50ccdd184548ab8761,
           Bn254Fr.ofNat 0x0ee230db343ce9495236839c502e30483c35c3eba168c208fbb3c278fee87bcb,
           Bn254Fr.ofNat 0x14108464277fb653ab9dc2e444faab33f5c4313d2b1826071c90690ca19ed962] := by native_decide

example :
    permute bn254Params (#v[Bn254Fr.ofNat 0x1d066a255517b7fd8bddd3a93f7804ef7f8fcde48bb4c37a59a09a1a97052816, Bn254Fr.ofNat 0x29daefb55f6f2dc6ac3f089cebcc6120b7c6fef31367b68eb7238547d32c1610, Bn254Fr.ofNat 0x0fc1bbceba0590f5abbdffa6d3b35e3297c021a3a409926d0e2d54dc1c84fda6])
      = #v[Bn254Fr.ofNat 0x206ed97b54820460db844a1ffdf604ac441d3b13d360142e304ebcc8a76af630,
           Bn254Fr.ofNat 0x22f47772c992a3da6cefbc5fedb26f72d6d5fc5699c494d122353e3f5e344684,
           Bn254Fr.ofNat 0x1e71eda9512b24f9f6e7acd1d399271451e02f547a86d05269a14e32f117d51c] := by native_decide

example :
    permute bn254Params (#v[Bn254Fr.ofNat 0x2a2ae15d8b143709ec0d09705fa3a6303dec1ee4eec2cf747c5a339f7744fb94, Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000, Bn254Fr.ofNat 0x19f8a5d670e8ab66c4e3144be58ef6901bf93375e2323ec3ca8c86cd2a28b5a5])
      = #v[Bn254Fr.ofNat 0x2ce005517b6687b8057c9d3ff9ef242f9659c6e02663373e26df0f211aff8092,
           Bn254Fr.ofNat 0x08862a43e343499f4cfbdf135fddd95f9f18b35c1ab5f99a9862d8cc7402e163,
           Bn254Fr.ofNat 0x3024835e8cae7a6f402ff486a1f0357b45ca52b53f11eb3fffc5be866ffa5e59] := by native_decide

/-! ## Compression vectors -/

example : compress (Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000005) (Bn254Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000006)
    = Bn254Fr.ofNat 0x0857df72d6ed7752cb928b44a2ec441a20e419275c7362d6116d3afac63ebb09 := by native_decide

example : compress (Bn254Fr.ofNat 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000) (Bn254Fr.ofNat 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000)
    = Bn254Fr.ofNat 0x091a9b01a4a67a83b8311b7b186a2d625ae1f74d39e125d5924f25cebfa9a0ed := by native_decide

example : compress (Bn254Fr.ofNat 0x2a2ae15d8b143709ec0d09705fa3a6303dec1ee4eec2cf747c5a339f7744fb94) (Bn254Fr.ofNat 0x19f8a5d670e8ab66c4e3144be58ef6901bf93375e2323ec3ca8c86cd2a28b5a5)
    = Bn254Fr.ofNat 0x0fd3617cc1a27d6b930298311f29627bcbbff851f10510d4f3043e16b5fd311d := by native_decide

/-! ## BLS12-381 permutation vectors (a second field, same generic `permute`) -/

example :
    permute bls12Params (#v[Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000, Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000001, Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000002])
      = #v[Bls12Fr.ofNat 0x1b152349b1950b6a8ca75ee4407b6e26ca5cca5650534e56ef3fd45761fbf5f0,
           Bls12Fr.ofNat 0x4c5793c87d51bdc2c08a32108437dc0000bd0275868f09ebc5f36919af5b3891,
           Bls12Fr.ofNat 0x1fc8ed171e67902ca49863159fe5ba6325318843d13976143b8125f08b50dc6b] := by native_decide

example :
    permute bls12Params (#v[Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000, Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000, Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000])
      = #v[Bls12Fr.ofNat 0x44fbea4934de59fe3dea4bb6ce5f053fe967f8c43a872b343a6d12fe40d75ca3,
           Bls12Fr.ofNat 0x3adcbb4b9afbb07dc4ab2f472d56d0fd84218b13637dc79ae8ca9bc82fd3caa4,
           Bls12Fr.ofNat 0x43bd99b4f7761171142eaae1d22bcfaeac77c9a6caa931e6c09996ab144ddf4b] := by native_decide

example :
    permute bls12Params (#v[Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000001, Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000002, Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000003])
      = #v[Bls12Fr.ofNat 0x20587c3ce7be3cb2a30cab7366e1ce0fc2f7a6b55a9830575a64dde2ede4c094,
           Bls12Fr.ofNat 0x3263145440c99cca7fa9fa57fb4c83f30f5647e38d326b827e93684cd81189a5,
           Bls12Fr.ofNat 0x66e339cfce8d916a44896fdb8b34758eb9181e4e2170fe2dc2d0d14663f5647f] := by native_decide

example :
    permute bls12Params (#v[Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000007, Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000, Bls12Fr.ofNat 0x0000000000000000000000000000000000000000000000000000000000000000])
      = #v[Bls12Fr.ofNat 0x6913e0181f8f8c228b07607c9fe41b1053cea2a1f963d13a0983ffeeb4ce69d3,
           Bls12Fr.ofNat 0x4baaa0e07601d28c480e082476cbe183b3dd4953001b08d576ad41242919ff7d,
           Bls12Fr.ofNat 0x6a11c9d23ba4e0222b075aed2d8cc6baaec59284ee8469784bff9c79e1074224] := by native_decide

example :
    permute bls12Params (#v[Bls12Fr.ofNat 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000, Bls12Fr.ofNat 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffffffff, Bls12Fr.ofNat 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffefffffffe])
      = #v[Bls12Fr.ofNat 0x3488eef72783184e5bc361b1df9f12d2758b1550e81e752cf34eda8747e9cdb6,
           Bls12Fr.ofNat 0x0a1f56577fc51b18c5c978542f91784f31586ff5da7d6a47c7557f0f57fe37a4,
           Bls12Fr.ofNat 0x5022d86dbd39ccbbb21f4479fd12190281cbc77c838a323b8bac416a18a70ba1] := by native_decide

example :
    permute bls12Params (#v[Bls12Fr.ofNat 0x1b152349b1950b6a8ca75ee4407b6e26ca5cca5650534e56ef3fd45761fbf5f0, Bls12Fr.ofNat 0x4c5793c87d51bdc2c08a32108437dc0000bd0275868f09ebc5f36919af5b3891, Bls12Fr.ofNat 0x1fc8ed171e67902ca49863159fe5ba6325318843d13976143b8125f08b50dc6b])
      = #v[Bls12Fr.ofNat 0x3b627c1adf7becbf476aa2283ae625e8707fb7da78e8de2ef9dfdff2a4758739,
           Bls12Fr.ofNat 0x68bf104aaaab200f116c83f5bf7377cb4b27ac79ef8794db8878e69b5c3a43a6,
           Bls12Fr.ofNat 0x2e15526555e18f7d3f98137dcae698a4ad7ece5e29ce4f8af3b9e64e0c7181d5] := by native_decide

end LeanPoseidonTests.Kat
