import Submissions.UpperLeanIsa.LayerWire
import Submissions.UpperLeanIsa.LayerDigits
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Constraint mathematics for the fused machine

Pure facts the machine proofs share, none of them about the bytecode:

1. the layer scheme under a fixed oracle table: `fixed_chain`, `fixed_root`, `fixed_index` and
   the exact decision `fixed_verify` on arbitrary raw inputs, and `probTrue_zero_of_fixed`;
2. cells and bits: `natV` cells, `cellOfBits` turning `XOR` into field addition, disjoint bit
   fields adding, the output pair of a `BLAKE2S`;
3. the loader's cells for a signature of `5503` bits.
-/

namespace OptimalOTS.HLG3

open OracleComp LeanerVM.Parameters
open OptimalOTS.LeanIsaBaseline.Layer
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord statementBits)

noncomputable section

/-! ## 1. The layer scheme under a fixed table -/

/-- A fixed oracle table. -/
abbrev HashTable := QueryImpl hashSpec Id

theorem fixed_hash (f : HashTable) {n : ℕ} (x : BitVec n) :
    simulateQ (unifFwdAnswerImpl f) (hash x) = pure (f ⟨n, x⟩) := by
  rw [hash, simulateQ_spec_query]
  rfl

/-- The answer of the table to an 896-bit query, typed as a 256-bit word. -/
def ans (f : HashTable) (q : BitVec 896) : BitVec 256 := f ⟨896, q⟩

/-- A `BLAKE2S`-sized query, typed as a 256-bit answer. -/
def hash896 (q : BitVec 896) : OracleComp Spec (BitVec 256) := hash q

theorem fixed_hash896 (f : HashTable) (q : BitVec 896) :
    simulateQ (unifFwdAnswerImpl f) (hash896 q) = pure (ans f q) := fixed_hash f q

section Fixed

variable (f : HashTable) (P : Params)

theorem fixed_tabulate {α : Type} {n : ℕ} (oa : Fin n → OracleComp Spec α) (w : Fin n → α)
    (h : ∀ i, simulateQ (unifFwdAnswerImpl f) (oa i) = pure (w i)) :
    simulateQ (unifFwdAnswerImpl f) (tabulate oa) = pure w := by
  induction n with
  | zero =>
    simp only [tabulate, simulateQ_pure]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [tabulate, simulateQ_bind, simulateQ_pure, h, pure_bind]
    rw [ih (fun i => oa i.succ) (fun i => w i.succ) (fun i => h i.succ), pure_bind]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

end Fixed

/-- A zero-probability lemma that keeps all repeated hash answers consistent. -/
theorem probTrue_zero_of_fixed (oa : OracleComp Spec Bool)
    (h : ∀ f : HashTable, true ∉ support (simulateQ (unifFwdAnswerImpl f) oa)) :
    probTrue oa = 0 := by
  rw [probTrue, probOutput_eq_zero_iff]
  intro hs
  change true ∈ support (Prod.fst <$> (simulateQ oracleImpl oa).run ∅) at hs
  rw [support_map] at hs
  obtain ⟨⟨b, cache⟩, hs, hb⟩ := hs
  change b = true at hb
  subst b
  obtain ⟨f, _, hf⟩ :=
    (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff oa ∅ true).mpr ⟨cache, hs⟩
  exact h f hf

/-! ## 2. Cells and bits -/

/-- `cellOfBits` turns `XOR` into field addition. -/
theorem cellOfBits_add (a b : BitVec 128) :
    cellOfBits a + cellOfBits b = cellOfBits (a ^^^ b) := by
  unfold cellOfBits
  rw [add_limbs, BitVec.extractLsb'_xor, BitVec.extractLsb'_xor]
  rfl

/-- `XOR` with a block above the low `n` bits is addition. -/
theorem xor_mul_eq_add {N a n : ℕ} (hN : N < 2 ^ n) : N ^^^ (a * 2 ^ n) = N + a * 2 ^ n := by
  rw [← Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.shiftLeft_eq, Nat.add_comm N, mul_comm,
    Nat.testBit_two_pow_mul_add a hN j]
  by_cases hj : j < n
  · rw [if_pos hj, decide_eq_false (show ¬ (j ≥ n) by omega), Bool.false_and, Bool.xor_false]
  · have hNj : N.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num)
        (by omega)))
    rw [if_neg hj, decide_eq_true (show j ≥ n by omega), Bool.true_and, hNj, Bool.false_xor]

/-- The canonical cell holding `n`. -/
def natV (n : ℕ) : E := cellOfBits (BitVec.ofNat 128 n)

theorem natV_add_disjoint {N a n : ℕ} (hN : N < 2 ^ n) (h : N + a * 2 ^ n < 2 ^ 128) :
    natV N + natV (a * 2 ^ n) = natV (N + a * 2 ^ n) := by
  unfold natV
  rw [cellOfBits_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h,
    xor_mul_eq_add hN]

theorem cellBits_natV (n : ℕ) : cellBits (natV n) = BitVec.ofNat 128 n := cellBits_cellOfBits _

theorem hi_append_lo (a : BitVec 256) : a.extractLsb' 128 128 ++ a.extractLsb' 0 128 = a := by
  have h := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := a) (start₁ := 0)
    (len₁ := 128) (start₂ := 128) (len₂ := 128) rfl
  exact h.trans BitVec.extractLsb'_eq_self

/-- The committed output pair of a `BLAKE2S` is the whole answer, high cell first. -/
theorem out_pair (lo hi : E) (ans : BitVec 256) (hlo : cellBits lo = ans.extractLsb' 0 128)
    (hhi : cellBits hi = ans.extractLsb' 128 128) : cellBits hi ++ cellBits lo = ans := by
  rw [hlo, hhi]
  exact hi_append_lo ans

theorem cellBits_ofK (a : K) : cellBits (ofK a) = (0 : BitVec 64) ++ a := by
  unfold cellBits
  rw [limb_ofK, limb_ofK]
  simp

/-! ## 3. The loader -/

theorem take_drop_toBits {n : ℕ} (x : BitVec n) (s w : ℕ) (h : s + w ≤ n) :
    ((toBits x).drop s).take w = toBits (x.extractLsb' s w) := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, length_bits, length_bits]
    omega
  · intro i h₁ h₂
    have hiw : i < w := by
      rw [length_bits] at h₂
      exact h₂
    simp only [List.getElem_take, List.getElem_drop, toBits, List.getElem_ofFn,
      BitVec.getLsbD_extractLsb', decide_eq_true hiw, Bool.true_and]

/-- The loader's cell 1 holds message bits `0 … 127`. -/
theorem inputWord_one (pk : PublicKey) (m : Message) (σ : List Bool) :
    inputWord pk m σ 1 = cellOfBits (m.extractLsb' 0 128) := by
  have hpk : (toBits pk).length = 128 := length_bits pk
  have hm : (toBits m).length = 256 := length_bits m
  have hm1 : 128 ≤ (toBits m).length := by rw [hm]; omega
  have hslice : ((toBits m).drop 0).take 128 = toBits (m.extractLsb' 0 128) :=
    take_drop_toBits m 0 128 (by show 0 + 128 ≤ 256; omega)
  rw [List.drop_zero] at hslice
  have h : ((statementBits pk m σ).drop (1 * 128)).take 128 = toBits (m.extractLsb' 0 128) := by
    unfold statementBits
    rw [Nat.one_mul]
    simp only [List.append_assoc]
    rw [List.drop_left' hpk, List.take_append_of_le_length hm1]
    exact hslice
  unfold inputWord
  rw [h, ofBits_bits]

/-- The loader's cell 2 holds message bits `128 … 255`. -/
theorem inputWord_two (pk : PublicKey) (m : Message) (σ : List Bool) :
    inputWord pk m σ 2 = cellOfBits (m.extractLsb' 128 128) := by
  have hpk : (toBits pk).length = 128 := length_bits pk
  have hm : (toBits m).length = 256 := length_bits m
  have hm1 : 128 ≤ (toBits m).length := by rw [hm]; omega
  have hm2 : 128 ≤ ((toBits m).drop 128).length := by rw [List.length_drop, hm]
  have hslice : ((toBits m).drop 128).take 128 = toBits (m.extractLsb' 128 128) :=
    take_drop_toBits m 128 128 (by show 128 + 128 ≤ 256; omega)
  have h : ((statementBits pk m σ).drop (2 * 128)).take 128 =
      toBits (m.extractLsb' 128 128) := by
    unfold statementBits
    rw [show 2 * 128 = (toBits pk).length + 128 by omega]
    simp only [List.append_assoc]
    rw [List.drop_length_add_append, List.drop_append_of_le_length hm1,
      List.take_append_of_le_length hm2]
    exact hslice
  unfold inputWord
  rw [h, ofBits_bits]

/-- The loader's cell 0 holds the public key. -/
theorem inputWord_pk (pk : PublicKey) (msg : Message) (σ : List Bool) :
    inputWord pk msg σ 0 = cellOfBits pk := by
  have h : ((statementBits pk msg σ).drop (0 * 128)).take 128 = toBits pk := by
    unfold statementBits
    rw [Nat.zero_mul, List.drop_zero, List.append_assoc, List.append_assoc]
    exact List.take_left' (length_bits pk)
  unfold inputWord
  rw [h]
  exact congrArg cellOfBits (ofBits_bits pk)

/-- The loader's cell 3 holds the capped signature length. -/
theorem inputWord_len (pk : PublicKey) (msg : Message) (σ : List Bool) :
    inputWord pk msg σ 3 = natV (min σ.length (maxSignatureBits + 1)) := by
  have hpre : (toBits pk ++ toBits msg).length = 3 * 128 := by
    rw [List.length_append, length_bits, length_bits]
    all_goals rfl
  have h : ((statementBits pk msg σ).drop (3 * 128)).take 128 =
      toBits (BitVec.ofNat 128 (min σ.length (maxSignatureBits + 1))) := by
    unfold statementBits
    rw [List.append_assoc, List.drop_left' hpre]
    exact List.take_left' (length_bits _)
  unfold inputWord
  rw [h, ofBits_bits]; rfl

/-- For a signature of the admitted length, cell `4 + i` holds signature cell `i`. -/
theorem inputWord_sig (pk : PublicKey) (msg : Message) (σ : List Bool)
    (hlen : σ.length = 5503) (i : ℕ) :
    inputWord pk msg σ (4 + i) = cellOfBits (ofBits 128 ((σ.drop (128 * i)).take 128)) := by
  have hpre : (toBits pk ++ toBits msg ++
      toBits (BitVec.ofNat 128 (min σ.length (maxSignatureBits + 1)))).length = 512 := by
    rw [List.length_append, List.length_append, length_bits, length_bits, length_bits]
    all_goals rfl
  have htake : σ.take maxSignatureBits = σ :=
    List.take_of_length_le (by rw [hlen]; unfold maxSignatureBits; omega)
  unfold inputWord statementBits
  rw [show (4 + i) * 128 = 512 + 128 * i by omega, ← List.drop_drop, List.drop_left' hpre,
    htake]

theorem inputWord_word (pk : PublicKey) (msg : Message) (σ : List Bool)
    (hlen : σ.length = 5503) (k : Fin numChains) :
    inputWord pk msg σ (4 + k.val) = cellOfBits (decodeWord σ k) :=
  inputWord_sig pk msg σ hlen k.val

theorem fold_bits_lt (xs : List Bool) :
    xs.foldr (fun (b : Bool) (a : ℕ) => b.toNat + 2 * a) 0 < 2 ^ xs.length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem inputWord_nonce (pk : PublicKey) (msg : Message) (σ : List Bool)
    (hlen : σ.length = 5503) : inputWord pk msg σ 46 = cellOfBits (nonceWord (decodeNonce σ)) := by
  rw [show 46 = 4 + 42 from rfl, inputWord_sig pk msg σ hlen]
  have hs : (σ.drop (128 * 42)).length = 127 := by simp [List.length_drop, hlen]
  rw [List.take_of_length_le (by omega)]
  unfold decodeNonce
  rw [List.take_of_length_le (by simpa [numChains] using le_of_eq hs)]
  apply congrArg cellOfBits
  apply BitVec.eq_of_toNat_eq
  have hb := fold_bits_lt (σ.drop (128 * 42))
  rw [hs] at hb
  simp only [ofBits, nonceWord, BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_zero,
    Nat.zero_mul, Nat.zero_add, Nat.shiftLeft_zero]
  norm_num only [numChains] at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb]
  simp

/-- The length cell pins the admitted length: `5503 < 5505`, so the capped length is exact. -/
theorem length_of_inputWord_len (pk : PublicKey) (msg : Message) (σ : List Bool)
    (h : inputWord pk msg σ 3 = natV 5503) : σ.length = 5503 := by
  rw [inputWord_len] at h
  have hb := congrArg cellBits h
  rw [cellBits_natV, cellBits_natV] at hb
  have hn := congrArg BitVec.toNat hb
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hn
  unfold maxSignatureBits at hn
  have h1 : min σ.length (5504 + 1) < 2 ^ 128 := by
    have : min σ.length (5504 + 1) ≤ 5505 := Nat.min_le_right _ _
    have h2 : (5505 : ℕ) < 2 ^ 128 := by norm_num
    omega
  have h3 : (5503 : ℕ) < 2 ^ 128 := by norm_num
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3] at hn
  omega

theorem inputWord_len_of (pk : PublicKey) (msg : Message) (σ : List Bool)
    (h : σ.length = 5503) : inputWord pk msg σ 3 = natV 5503 := by
  rw [inputWord_len, h]; rfl

end

end OptimalOTS.HLG3
