import Submissions.UpperLeanIsa.LayerBits

/-! The effective index of a raw 128-bit hash slice.

The machine ties unit 11's field through its landing hint `g ^ e`, a word of limb 0. Bits
28..36 of that word are the field value; its other bits are the fixed mask `hintMask v`. The
tie patterns of the other units are the field layout rotated left by 47 bits, which moves unit
11's field (bits 109..117) onto bits 28..36. `unmask` removes the mask and undoes the rotation;
it is a bijection with inverse `remask`. The effective index discards bit zero of the result. -/

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option linter.constructorNameAsVariable false

abbrev RawIndex := BitVec 128
abbrev Index := BitVec 127

/-- The 512 masks of unit 11's landing hints, 64 bits each, the mask of `v` at bit `64 v`. -/
def hintMaskN : ℕ := 0xee1212000df724c6b23f09800b48d64595070be00413d383abb510c00ffd4c2f7078874002d81398be0d19c00f4652a91ceb2d600c4d060171e8e8200073b2fe03e2c6200c5fcf234d65c880087543ea28e0c20009b93d82467810600d0072a318fdf1600c8c947573dce160076b6bffbca08d600dc88576b3edb6e0074c886c67b2200008de754495fe97e00737163440a4af800e3464c40712c5000b60aba7e2c2d9e0033aaaed7ac032a00d132362722d6b6002399a8da827a7000e83f809c77221400abb4ae9043cbf600fe3cf45a9b4ab8009dfe75c1346926003639a74ac374c600717a0b4a99521e00b4a7162cc5bfcc0060c305225ca5180041fd343ce93d02003cbd736543e82e008f50d8541719e400911b42b6f542e8004e9e48ae154f3000f43306a484091200249731bc11b28c001f84cf41e107e4000fc73841b7ec8800b8dcf2c9e2ce1c004357e17d4d77b000e0f8b0cac5b0fc00c4af7c813b30e800e95c91ed6c545e001d2efc51035cb600113fb2aa405f4600f5207cb7ce30b800aadb5ea73cb3be00a458647b7871fc00cdcbf81dcbf8e0000234e445f2304c004062d99e84754200ae945c9f4ae48e003ec74e3af4326000af5952fa131be2001ceb2d96182cf8001739f5096a802c0085d4d28b2a26c4003519504aae51d600a1d7f3e8ee1f8c006f316fa26d23da000a26ee53f5a23e00d012e352c4e87e00a89826bbd652680033e1f129e0f1ce00380f82de6a06e400521fdbb465c8e400d1b38b32da6b30009a92f4067d3c1e00e902e2a1792d2400553cc77365cc4000ec89d79b78a43e006e9ca44e98f478001739660faf2658007a0ae9f7af26fc00658288bcb7259e00f9e225b65030b000bd1584503f78b20069f71b3ce7d56c0075606f77a2b080005be888d616741200c385ce6f8f1c7200b5fe71a71dc95400411f81dcab2c6e00a519a62a1b668600940b3aa5c6e9d2008495e36b8e7740002075cfa574e81000c73615b6d1e82a009de8f6af0e406c000f99810fea260800493f21234d342c006e012cd10ddafe001d50f2be454bb600bca96dc82b782000dfab28113af71a005a83333807be3600507b998e520de80052050ae2c486e800d6c545c9a0c00000d970b0867ba934002cf167584ed09c0074e9f470d815ba005e48b94bf2f688009ed1979b483ff80008e88d4677ebd000a9b4abc7c653840059722798fe0e5a00cfd97c21eee33c0000f7c6e41128140074c7a3a02b20e800479b517b70e17200fb9f64277e7d0800f1e38e31448a0a00f2eec89b9e093e00d7937e2dd337ac008bfa430947795c006a802d067ecbe600942c4839a6f8ce00c77eb5cbfcea44004336b7d43a62540079411a923251d000da3e2d9c71a39000cba2a06230bae6004fe2f5ddc9ec0c005bb9754586a96000bf53fddd7c3a1c00300656b73c85d400776a2a2188e1ca00a654f1add4c4ae00653859912d7df80044cb4f73aab328006b0d52ec774efc0032cda36469c9c8008061e80a0ba5680009090f12227f6400559637ea0316ce0026b32570d012e200e9d4424cf2f5ce0085fc9d13a74fa40047e49f44e7053000b99b0a026f316e00a324244c78fb3000f378588ec88da000f83dae2dc0259e00b7f83aca65e2b0003f7531cceb1b90005bf491749d6822006435cb81368f8a00385879aaad426a00fce543f5992cf0000eeb21d4ed6d7e00e987f12836af8800a41ffc103952ce00da47b7886afc3600b862b54b82017c00a532f1a7f3006400ba63f1fc81d73c00195f563877590c0086ec77d481717e00b2934d92e0935200ec75780236a64200be09a782c3219a0096166467ea7fb40084d6d1bbd1b38a00dc90585d507b98004ed09d36660f1a006a21bfc0433fbe00519723918f2946006652f4c77c1ed600ca90ff50b716160049190e0fa6803800cf64dadba35744009fea2974c8d9bc00ba7713c58602fc00f6ab50e9b9602800881da6729d103a00792d47742344d6005a072e8a072eee00a6b7737d792d46009eb223ccccab78009110dd17bcbaac000f78a3c15d2cee00b7871fca265a7a005db2bff43caae800c1fe8676e987f0008a0b8ca0bf7a3c00608797e51121480086cd6ccb5fe71200800335400e765e007e1f4898532a34007c1a3362e71df600c9a23046502ce80003df3ce1f5667c001fb9e91324247200ce3d1ee7fba50800d046d4887f6cdc0049638dccdc58e00079e0693b65c2c000ad005faa62e3720014c8c20c12e9d200e04f0cb86b97c000f6909740fc738400b495d28d29051a00573304c08513760086238721b325720046ca3777f7373600e38730474c5a0600ef4ba6f03b4d7800474a9ebecaecaa006faaa593a7510800c63825f4721192000e17ffcfad23580091273e1af264100015907423592990003e874c627f17ae00fdb365bb4ae204007cf6f1521ffdf600cea387b482c57e008395ca2dbfc1d20018dd60acf034c600d01c86d716b3b800b15fc8a017d436005667d3cb89d3c8007c3fddd23f24fa003abc993f97603e00e14cedb32a11d0006634809a1d50fa00b7252bf6175348000e0f10b7252b1e00796451534b62060098d2ea926e5a0200cf752681bb1dc200acea392879b9860070610f7df03090002028bc321937be004cbc50c9c5b0bc00c8464c69190e0e00ebf65bcafecdd200e28914f3224e7c009895617112858800d337ad9f37858200167ce39b78d192003a09d61866fd8200c4dc07ef330332008a0319b980d6fc0094b74663d9c1e000e5d80fee373cb40066526f2dfb66ca0011fef4c95615e4006bf8ee8b481f320033098af06405200044f689219984c4008c95fe82bb12d4005b8b0b93658288007a333052df444400caecab119f0f8e006a1b669d93446000c02da61df0a25a00f2f689321d2efc00131be3f490187a001826e5cd2d111000b0b67f0c6f3aa00032b09d19de71e800707841340f7cf200cf738592fff50400e3d1d04fdf9bf800d15b9a6006128e00bb12d5084b207e006760d33a6a4bd0006d5f122cc8badc008512d769ecd71c00834e402a4c8886007fd08e4a0fe01c00be80fcde834e40009eb00c2dc315ac003934a4b5e31c1200d335e03d124b9800f6614b22e9addc0090baaff49f90d8009d66e5e1e6d45c009a3b87f9d470f00006da403978a1ee003d91003fb9e90200febd65b00335b200609bd686dccc9800fc3d5cfd7ff50c00b0615838311e0a000867f731d32218006000c2449c2c3c00c38a385ed32a7800281858585fc9da00fecdd3dfab44c800bd50bae0469b1c00570dd3e53d644600a1930e3f9805b400637535b0d9ad96000fa0bf7baafcee0054c6d303873008009392f128579eae00b8814981a9fbe0009dfaf47b99584e009d98741fdc761200d688ff9396ef46002d677261b1cd3a00cb014a6a23fde800c1e36a05f58a9400c562d8057330460037647e62236bd0008722bd5373361400c2eb9e202786020074efd7975606fc00b820179e3709bc00bdc28c1a3f395000127cd4f392f10000d0d2d132b4a71600f447212c76fd0c0088f056434eb37200529d10157aca9000f71d84cb663480008fa1eab84bceac002cdae3c4fb1d3a0099044a617f487400f3e84c7d85323000e7824f4dfab28c001cb77a9b2f4b3600c78fb3eeef4ba600739e426110f8b0007facceb07c583400af20c7990145e40096e154387a994000a4f40fab4fec1c00a26c5cb1ea40f8008fdf17ef16d27000f3730eb5e87836008965a46bf91c1c00520de967219b6400c09c7c0c6adc94007c61e521cf7ccc00794991067facce00b9475f5396fb4c00e36ca04a40a14c00d4fdf08922e5280022a5db186fe7fe00108d138528a72200dbd05e296a0ccc00df41261bf9e46400a309b48ced257400480c3dc44fb43a00f6356e262093e600e258a386a2a63600d8396513a66bc000180b1df0271f1000f03091187f8ad2005b0bd1cf6f042800b98c318ad6751c00520a3684c4f0ba00d1fc1cd0f821b2000d6fd081fe0680001ba74ebb7a0bca00d44b13538533b400d2892017580030007795d8d17f5eb2004df19f14ff8e0200678cae0b772ebc007294536ed754ca00ff15a5b59ec9b4006f0428e99d557200be1d0e751950b600313c2ed17a239000995070a6f1e8e8005b73323e460f2e00834017817952da0062743fc7dcfb2600c1f980189265e200bb8cf69721d01c006d92b74e59144400250a1bbe09a7b400bceacb57072b94007a6714cd472694008d992b3d1f43d400f1631f1e5d1506002e0935be25969000f32a115e59a3b8003709bc49b5c63c0098b7f973a309b4005b49c2eb42ddf0005d532abca37b06001cdae75a4b70aa008edfa17f7a333000dabb51930163ba00ebc9964a42ffdc0012cfd663da425e0065e966fcb60aba0008d3632bf65b02008298b82a6747f000dc967e2ef47b7800fdcdcd4ee499d400f0e4065a448432007e24999ec1856200039ef917977644000b77c1ac1cb2a2005c43512afc74f6008e774141fe861e0006e5bc4aaa519a00a16d139fd6a1b6007a994024371f5600d3c1fbfadfa48e00a249727b1710d40042da343b5b9616005d6e773e776a2a0069fd831cd79b2e000dbf64f9871470000facdc51fefea2009a3493e137ad000050dc7d4bdf892600287bb836ee73c80057e776f399a89200a519e068c1f980004d663780187a1a002221f16b44dc0200f6db7f77cf11280090dd333314063200fa5ffbb717a0ba00977090d8ca54da00cf2cef28722bd60085ffb83b604e7000171b9945d7922e008a722a2a8925ca009e041f3cf87fba0093ad04d087d66e00606c0ada5b512c0087fbfa6a9842340074c5a09c5a87d8001f7b416cc6ea6a00d0f06de73e874c00b0af28632937d000b593afd2dee1460048e677a70a32420033bce393ff53080089ae9891f18796001121495a03f0fa0084326f9f0fa4480026f7e2d6bf8ee400bcf576c74eaf26001281594f57695c00a4af9e4e17533a008396e43256e04e00213be054733bce001ece0f68f47b380020fcbbd45ce59a0087e370fcbb657e007b35c7898c311c006fb4ca51092bc60025d3a676d7bab000e635c15f1dfad400cd0f53b267fad20092991241d11b660080be8fb8df554a004d342d77cf6f1a006167417d2d6bc800e528ea0f109df000911320b326541c00ff504f609d6e1c0071df73e10d465400a34c4f1c6d940c006c6f45d163637a00081ae5a147b2d800e9d023523f0320000812278091132000bc9692da16d1a60085d4ce646ec8fc007fad2335b9df0a00afbf2f1a48e66a009729469377318600872df6b7a1a5a2001f16168f1b576a00bf9ffa0d8de8ac006b96fa865f407e004890861a51240600be460950294e8800a6bc96a41fd34000a967b205a00bea008fab33984e1e78006390e8d875fcc000586e98231bac00004a3bcacb46989e00533a3f7519a69a00d13700ecb368f400d2cef4c7a671480029951adc3d7c8c0072d0180ad2ee12001ffdf7c573282000d01f61ade9c07c00d94c061349190e0010ebf6798da7f600595136eacdc9ec00815bb9953c6d94002c6c6f37f1448a008cf2ee8198311e00de0867e1930b3a00d6e1c2f1bf31ae0005f58a84d74c5a002eef4bc2ba5124001ebe46383f73d200c5fd7a11d7ecb600e70531671341800035b2e1285b44dc0059f6dbab04deb4007d4371010c6eb0006128ef3

def hintMaskV (v : ℕ) : ℕ := hintMaskN / 2 ^ (64 * v) % 2 ^ 64

/-- The known bits of unit 11's landing hint for field value `v`; bits 28..36 are zero. -/
def hintMask (v : ℕ) : RawIndex := BitVec.ofNat 128 (hintMaskV v)

/-- Bits 28..36: unit 11's field, as written by its landing hint. -/
def hintField (r : RawIndex) : BitVec 9 := r.extractLsb' 28 9

def unmask (r : RawIndex) : RawIndex := (r ^^^ hintMask (hintField r).toNat).rotateRight 47

def remask (d : RawIndex) : RawIndex :=
  d.rotateLeft 47 ^^^ hintMask (hintField (d.rotateLeft 47)).toNat

theorem hintMaskN_lt : hintMaskN < 2 ^ (64 * 512) := by decide +kernel

theorem hintMaskV_ok : ∀ v < 512, hintMaskV v / 2 ^ 28 % 2 ^ 9 = 0 := by decide +kernel

theorem hintMaskV_bits (v : ℕ) : hintMaskV v / 2 ^ 28 % 2 ^ 9 = 0 ∧ hintMaskV v < 2 ^ 64 := by
  refine ⟨?_, Nat.mod_lt _ (by positivity)⟩
  by_cases hv : v < 512
  · exact hintMaskV_ok v hv
  · have h : hintMaskN / 2 ^ (64 * v) = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hintMaskN_lt
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hintMaskV, h]

theorem hintMask_field (v : ℕ) : hintField (hintMask v) = 0 := by
  have h := hintMaskV_bits v
  apply BitVec.eq_of_toNat_eq
  simp only [hintField, hintMask, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show hintMaskV v < 2 ^ 128 by omega)]
  simpa using h.1

theorem hintField_xor_mask (r : RawIndex) (v : ℕ) : hintField (r ^^^ hintMask v) = hintField r := by
  have h := hintMask_field v
  unfold hintField at h ⊢
  rw [BitVec.extractLsb'_xor, h]
  simp

theorem rotR_rotL (x : RawIndex) : (x.rotateLeft 47).rotateRight 47 = x := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight]
  by_cases h1 : i < 81
  · have h2 : ¬ (47 + i < 47) := by omega
    simp [h1, h2, hi, show 47 + i < 128 by omega, show 47 + i - 47 = i by omega]
  · have h2 : i - 81 < 47 := by omega
    simp [h1, h2, hi, show 81 + (i - 81) = i by omega]

theorem rotL_rotR (x : RawIndex) : (x.rotateRight 47).rotateLeft 47 = x := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight]
  by_cases h1 : i < 47
  · have h2 : ¬ (81 + i < 81) := by omega
    simp [h1, h2, show 81 + i < 128 by omega, show 81 + i - 81 = i by omega]
  · have h2 : i - 47 < 81 := by omega
    simp [h1, h2, hi, show 47 + (i - 47) = i by omega]

theorem rotL_xor (x y : RawIndex) :
    (x ^^^ y).rotateLeft 47 = x.rotateLeft 47 ^^^ y.rotateLeft 47 := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_xor]
  by_cases h1 : i < 47 <;> simp [h1, hi]

/-- Rotation moves unit 11's field onto the hint bits. -/
theorem hintField_rotL (d : RawIndex) : hintField (d.rotateLeft 47) = d.extractLsb' 109 9 := by
  unfold hintField
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft]
  simp [hi, show 28 + i < 47 by omega, show 81 + (28 + i) = 109 + i by omega]

theorem remask_unmask (r : RawIndex) : remask (unmask r) = r := by
  unfold remask unmask
  rw [rotL_rotR, hintField_xor_mask, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem unmask_remask (d : RawIndex) : unmask (remask d) = d := by
  unfold remask unmask
  rw [hintField_xor_mask, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, rotR_rotL]

/-- A word built as the machine's tie builds it unmasks to the field layout. -/
theorem unmask_hint (d : RawIndex) {v : ℕ} (hv : (d.extractLsb' 109 9).toNat = v) :
    unmask (d.rotateLeft 47 ^^^ hintMask v) = d := by
  unfold unmask
  rw [hintField_xor_mask, hintField_rotL, hv, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero,
    rotR_rotL]

def effective (w : RawIndex) : Index := (unmask w).extractLsb' 1 127

def indexSlice {n : ℕ} (w : BitVec n) : Index := effective (w.extractLsb' 0 128)

def indexRest (w : BitVec 256) : BitVec 129 :=
  w.extractLsb' 128 128 ++ (unmask (w.extractLsb' 0 128)).extractLsb' 0 1

def joinIndex (i : Index) (r : BitVec 129) : BitVec 256 :=
  r.extractLsb' 1 128 ++ remask (i ++ r.extractLsb' 0 1)

theorem indexSlice_effective (w : BitVec 256) :
    indexSlice w = effective (w.extractLsb' 0 128) := rfl

theorem split_low (x : RawIndex) : x.extractLsb' 1 127 ++ x.extractLsb' 0 1 = x := by
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 1 = 0 + 1)]
  exact BitVec.extractLsb'_eq_self

theorem joinIndex_split (w : BitVec 256) : joinIndex (indexSlice w) (indexRest w) = w := by
  unfold joinIndex indexSlice indexRest effective
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right, split_low,
    remask_unmask]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 128 = 0 + 128)]
  exact BitVec.extractLsb'_eq_self

theorem indexSlice_join (i : Index) (r : BitVec 129) : indexSlice (joinIndex i r) = i := by
  unfold indexSlice joinIndex effective
  rw [BitVec.extractLsb'_append_eq_right, unmask_remask,
    BitVec.extractLsb'_append_eq_of_le (by decide : 1 ≤ 1)]
  simp

theorem indexRest_join (i : Index) (r : BitVec 129) : indexRest (joinIndex i r) = r := by
  unfold indexRest joinIndex
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right, unmask_remask]
  simp only [BitVec.extractLsb'_append_eq_ite]
  norm_num

theorem card_indexSlice (p : Index → Prop) [DecidablePred p] :
    (Finset.univ.filter fun w : BitVec 256 => p (indexSlice w)).card =
      (Finset.univ.filter p).card * 2 ^ 129 := by
  have hu : (Finset.univ : Finset (BitVec 129)).card = 2 ^ 129 := by
    rw [Finset.card_univ, Fintype.card_bitVec]
  rw [← hu, ← Finset.card_product]
  refine Finset.card_nbij' (fun w => (indexSlice w, indexRest w))
    (fun x => joinIndex x.1 x.2) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
    simp [hw]
  · intro x hx
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_ofPred_eq, Finset.coe_univ, Set.mem_univ, and_true] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      indexSlice_join]
    exact hx
  · intro w _
    exact joinIndex_split w
  · intro x _
    exact Prod.ext (indexSlice_join _ _) (indexRest_join _ _)

end OptimalOTS.LeanIsaBaseline.Layer
