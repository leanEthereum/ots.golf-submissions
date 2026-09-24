import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LeanerVM.Parameters.Generator
import OptimalOTS.LeanIsaMachine
import Submissions.UpperLeanIsa.Correctness

/-!
# Constraint mathematics for the leanISA verifier

The machine program (design `NOTES.md`, §4 and §6) checks a Winternitz signature with
`MUL` / `XOR` / `SET` / `BLAKE2S` constraints along a dispatched path. This file proves, over plain
functions and values, the facts that turn those constraints into the scheme's fixed-table
verifier. Nothing here mentions the program or its execution, so the lemmas can be glued to any
layout.

1. `E` has characteristic two.
2. Chains: consecutive `BLAKE2S` outputs from position `e` compute `chainValue` (`chain_from`);
   `BLAKE2S` operands give `chainInput` and absorb inputs.
3. The absorb states compute `rootValue`.
4. Bytes: packing the tie words recovers message bytes, `digit m i` is a message byte, and the
   loader's cells (`inputWord_*`, including the zero padding `inputWord_pad_zero`).
5. The checksum identity `Σ_{k<32} E k + 256 · E 32 + E 33 = 8160` recovers the two checksum
   digits (`checksum_digits`), and the true digits satisfy it (`checksum_honest_sum`).
-/

namespace OptimalOTS.LeanIsaBaseline.Machine

open LeanerVM.Parameters
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord statementBits)

/-! ## 1. Characteristic two -/

/-- Addition in `E` is limb-wise `XOR`, so every word is its own negative. -/
theorem add_self_E (a : E) : a + a = 0 := by
  exact CharTwo.add_self_eq_zero a

/-- Addition in `K` is `XOR`. -/
theorem add_self_K (a : K) : a + a = 0 := BF64.add_self a

/-! ## 2. Chains -/

theorem chainValue_zero' (f : HashTable) (i j : ℕ) (x : Word) : chainValue f i j 0 x = x := by
  rfl

/-- One more chain step, appended at the end. -/
theorem chainValue_succ' (f : HashTable) (i j n : ℕ) (x : Word) :
    chainValue f i j (n + 1) x =
      (f ⟨896, chainInput i (j + n) (chainValue f i j n x)⟩).extractLsb' 0 128 := by
  rw [← chainValue_add f i j n 1 x]
  all_goals rfl

/-- A chain entered at position `e`: step `e` hashes `σ` (when `e < 255`), steps
`j ∈ (e, 254]` hash the previous output, and for `e = 255` the endpoint is `σ` itself. Then the
endpoint `x 255` is `chainValue f i e (255 - e) σ`. -/
theorem chain_from (f : HashTable) (i e : ℕ) (he : e ≤ 255) (σ : Word) (x : ℕ → Word)
    (hleaf : e < 255 → x (e + 1) = (f ⟨896, chainInput i e σ⟩).extractLsb' 0 128)
    (hbody : ∀ j, e < j → j ≤ 254 →
      x (j + 1) = (f ⟨896, chainInput i j (x j)⟩).extractLsb' 0 128)
    (h255 : e = 255 → x 255 = σ) :
    x 255 = chainValue f i e (255 - e) σ := by
  rcases Nat.lt_or_ge e 255 with hlt | hge
  · have key : ∀ n, e + n ≤ 254 → x (e + n + 1) = chainValue f i e (n + 1) σ := by
      intro n
      induction n with
      | zero =>
        intro _
        rw [chainValue_succ', chainValue_zero', Nat.add_zero]
        exact hleaf hlt
      | succ n ih =>
        intro hn
        rw [chainValue_succ', ← ih (by omega), show e + (n + 1) = e + n + 1 by omega]
        exact hbody (e + n + 1) (by omega) (by omega)
    have h := key (254 - e) (by omega)
    rwa [show e + (254 - e) + 1 = 255 by omega, show 254 - e + 1 = 255 - e by omega] at h
  · obtain rfl : e = 255 := by omega
    rw [h255 rfl, Nat.sub_self, chainValue_zero']

/-! ### `BLAKE2S` operands as scheme queries -/

theorem zero_append_zero_128 : (0 : BitVec 128) ++ (0 : BitVec 128) = (0 : BitVec 256) := by
  exact BitVec.zero_append_zero

set_option exponentiation.threshold 512 in
theorem zero_append_three (y : BitVec 128) :
    (0 : BitVec 128) ++ (0 : BitVec 128) ++ (0 : BitVec 128) ++ y = y.setWidth 512 := by
  apply BitVec.eq_of_toNat_eq
  have h0 : (0 : BitVec 128).toNat = 0 := by
    rfl
  have hy := BitVec.toNat_lt_twoPow_of_le (by decide : 128 ≤ 512) (x := y)
  rw [BitVec.toNat_setWidth]
  simp only [BitVec.toNat_append, h0, Nat.zero_shiftLeft, Nat.zero_or]
  exact (Nat.mod_eq_of_lt hy).symm

/-- A chain step's `BLAKE2S`: message `(x, I_i, J_j, 0)`, zero chaining pair, metadata `1`,
queries exactly `chainInput i j x`. -/
theorem blake2sQuery_chain_gen (i j : ℕ) (m : Fin 4 → E) (cv0 cv1 md : E)
    (hm1 : cellBits (m 1) = BitVec.ofNat 128 i) (hm2 : cellBits (m 2) = BitVec.ofNat 128 j)
    (hm3 : cellBits (m 3) = 0) (hc0 : cellBits cv0 = 0) (hc1 : cellBits cv1 = 0)
    (hmd : cellBits md = 1) :
    blake2sQuery m cv0 cv1 md = chainInput i j (cellBits (m 0)) := by
  have hcv : cellBits cv1 ++ cellBits cv0 = (0 : BitVec 256) := by
    rw [hc0, hc1, zero_append_zero_128]
  have hblk : cellBits (m 3) ++ cellBits (m 2) ++ cellBits (m 1) ++ cellBits (m 0) =
      (0 : BitVec 128) ++ BitVec.ofNat 128 j ++ BitVec.ofNat 128 i ++ cellBits (m 0) := by
    rw [hm1, hm2, hm3]
  have key : hashInput (cellBits cv1 ++ cellBits cv0)
      (cellBits (m 3) ++ cellBits (m 2) ++ cellBits (m 1) ++ cellBits (m 0)) (cellBits md) =
      hashInput (0 : BitVec 256)
        ((0 : BitVec 128) ++ BitVec.ofNat 128 j ++ BitVec.ofNat 128 i ++ cellBits (m 0))
        (1 : BitVec 128) := by
    rw [hcv, hblk, hmd]
  exact key

/-- `blake2sQuery_chain_gen` for the literal operand vector the machine reads. -/
theorem blake2sQuery_chain (i j : ℕ) (x tagI tagJ z cv0 cv1 md : E)
    (hI : cellBits tagI = BitVec.ofNat 128 i) (hJ : cellBits tagJ = BitVec.ofNat 128 j)
    (hz : cellBits z = 0) (hc0 : cellBits cv0 = 0) (hc1 : cellBits cv1 = 0)
    (hmd : cellBits md = 1) :
    blake2sQuery ![x, tagI, tagJ, z] cv0 cv1 md = chainInput i j (cellBits x) :=
  blake2sQuery_chain_gen i j ![x, tagI, tagJ, z] cv0 cv1 md hI hJ hz hc0 hc1 hmd

/-- An absorb step's `BLAKE2S`: message `(x, 0, 0, 0)`, chaining pair `(cv0, cv1)`, metadata
`2 + r`, queries exactly the input of `absorb r (cv1 ++ cv0) x`. -/
theorem blake2sQuery_absorb_gen (r : ℕ) (m : Fin 4 → E) (cv0 cv1 md : E)
    (hm1 : cellBits (m 1) = 0) (hm2 : cellBits (m 2) = 0) (hm3 : cellBits (m 3) = 0)
    (hmd : cellBits md = BitVec.ofNat 128 (2 + r)) :
    blake2sQuery m cv0 cv1 md =
      hashInput (cellBits cv1 ++ cellBits cv0) ((cellBits (m 0)).setWidth 512)
        (BitVec.ofNat 128 (2 + r)) := by
  have hblk : cellBits (m 3) ++ cellBits (m 2) ++ cellBits (m 1) ++ cellBits (m 0) =
      (cellBits (m 0)).setWidth 512 := by
    rw [hm1, hm2, hm3, zero_append_three]
  have key : hashInput (cellBits cv1 ++ cellBits cv0)
      (cellBits (m 3) ++ cellBits (m 2) ++ cellBits (m 1) ++ cellBits (m 0)) (cellBits md) =
      hashInput (cellBits cv1 ++ cellBits cv0) ((cellBits (m 0)).setWidth 512)
        (BitVec.ofNat 128 (2 + r)) := by
    rw [hblk, hmd]
  exact key

/-- `blake2sQuery_absorb_gen` for the literal operand vector the machine reads. -/
theorem blake2sQuery_absorb (r : ℕ) (x z1 z2 z3 cv0 cv1 md : E)
    (h1 : cellBits z1 = 0) (h2 : cellBits z2 = 0) (h3 : cellBits z3 = 0)
    (hmd : cellBits md = BitVec.ofNat 128 (2 + r)) :
    blake2sQuery ![x, z1, z2, z3] cv0 cv1 md =
      hashInput (cellBits cv1 ++ cellBits cv0) ((cellBits x).setWidth 512)
        (BitVec.ofNat 128 (2 + r)) :=
  blake2sQuery_absorb_gen r ![x, z1, z2, z3] cv0 cv1 md h1 h2 h3 hmd

/-! ## 3. The root -/

theorem hi_append_lo (a : BitVec 256) : a.extractLsb' 128 128 ++ a.extractLsb' 0 128 = a := by
  have h := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := a) (start₁ := 0)
    (len₁ := 128) (start₂ := 128) (len₂ := 128) rfl
  exact h.trans BitVec.extractLsb'_eq_self

/-- The committed output pair of a `BLAKE2S` is the whole answer, high cell first. -/
theorem out_pair (lo hi : E) (ans : BitVec 256) (hlo : cellBits lo = ans.extractLsb' 0 128)
    (hhi : cellBits hi = ans.extractLsb' 128 128) : cellBits hi ++ cellBits lo = ans := by
  rw [hlo, hhi]
  exact hi_append_lo ans

/-- `rootValueFold` over `List.ofFn` is any state sequence satisfying the absorb recursion. -/
theorem rootValueFold_ofFn (f : HashTable) (n : ℕ) : ∀ (w : ℕ → Word) (c : ℕ → BitVec 256),
    (∀ k < n, c (k + 1) = f ⟨896, hashInput (c k) ((w k).setWidth 512)
      (BitVec.ofNat 128 (2 + (n - 1 - k)))⟩) →
    rootValueFold f (List.ofFn fun i : Fin n => w i) (c 0) = c n := by
  induction n with
  | zero =>
    intro w c _
    rfl
  | succ n ih =>
    intro w c hc
    have e0 : f ⟨896, hashInput (c 0) ((w 0).setWidth 512) (BitVec.ofNat 128 (2 + n))⟩ = c 1 := by
      have h := hc 0 (Nat.succ_pos n)
      rw [show n + 1 - 1 - 0 = n by omega, Nat.zero_add] at h
      exact h.symm
    have hrest := ih (fun k => w (k + 1)) (fun k => c (k + 1)) (fun k hk => by
      have h := hc (k + 1) (by omega)
      rw [show n + 1 - 1 - (k + 1) = n - 1 - k by omega] at h
      exact h)
    -- `hrest : rootValueFold f (List.ofFn fun i => w (↑i + 1)) (c 1) = c (n + 1)`
    simp only [Nat.zero_add] at hrest
    -- The list length sits inside the query index, and the answer's type depends on the query,
    -- so it cannot be rewritten under `f`. Generalise it instead (`subst`, not `rw`).
    have e0' : ∀ L : ℕ, L = n →
        (f ⟨896, hashInput (c 0) ((w 0).setWidth 512) (BitVec.ofNat 128 (2 + L))⟩ :
          BitVec 256) = c 1 := by
      intro L hL
      subst hL
      exact e0
    have key : (f ⟨896, hashInput (c 0) ((w 0).setWidth 512)
        (BitVec.ofNat 128 (2 + (List.ofFn fun i : Fin n => w ((i : ℕ) + 1)).length))⟩ :
          BitVec 256) = c 1 :=
      e0' _ List.length_ofFn
    rw [List.ofFn_succ]
    -- `Fin.val_zero` / `Fin.val_succ` are `rfl` lemmas, so `simp` applies them under `f`.
    simp only [rootValueFold, Fin.val_zero, Fin.val_succ]
    exact (congrArg (rootValueFold f (List.ofFn fun i : Fin n => w ((i : ℕ) + 1))) key).trans
      hrest

/-- Soundness of the root. States `(lo k, hi k)` start at zero; absorb `k` hashes endpoint
`e k` with metadata `2 + (33 - k)`; then `lo 34` holds `rootValue f xs`. -/
theorem root_sound (f : HashTable) (xs : Fin 34 → Word) (e lo hi : ℕ → E)
    (hxs : ∀ i : Fin 34, xs i = cellBits (e i))
    (hlo0 : cellBits (lo 0) = 0) (hhi0 : cellBits (hi 0) = 0)
    (hlo : ∀ k < 34, cellBits (lo (k + 1)) =
      (f ⟨896, hashInput (cellBits (hi k) ++ cellBits (lo k)) ((cellBits (e k)).setWidth 512)
        (BitVec.ofNat 128 (2 + (33 - k)))⟩).extractLsb' 0 128)
    (hhi : ∀ k < 34, cellBits (hi (k + 1)) =
      (f ⟨896, hashInput (cellBits (hi k) ++ cellBits (lo k)) ((cellBits (e k)).setWidth 512)
        (BitVec.ofNat 128 (2 + (33 - k)))⟩).extractLsb' 128 128) :
    cellBits (lo 34) = rootValue f xs := by
  have h0 : cellBits (hi 0) ++ cellBits (lo 0) = (0 : BitVec 256) := by
    rw [hhi0, hlo0, zero_append_zero_128]
  have hfold := rootValueFold_ofFn f 34 (fun k => cellBits (e k))
    (fun k => cellBits (hi k) ++ cellBits (lo k))
    (fun k hk => out_pair (lo (k + 1)) (hi (k + 1)) _ (hlo k hk) (hhi k hk))
  simp only [h0] at hfold
  have hxs' : xs = fun i : Fin 34 => cellBits (e i) := funext hxs
  have key : (rootValueFold f (List.ofFn xs) 0).extractLsb' 0 128 = cellBits (lo 34) := by
    rw [hxs', hfold, BitVec.extractLsb'_append_eq_right]
  exact key.symm

/-! ## 4. Bytes and the loader -/

/-- `XOR` with a block above the low `n` bits is addition. -/
theorem xor_shiftLeft_eq_add {N a n : ℕ} (hN : N < 2 ^ n) : N ^^^ (a <<< n) = N + 2 ^ n * a := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.add_comm N, Nat.testBit_two_pow_mul_add a hN j]
  by_cases hj : j < n
  · rw [if_pos hj, decide_eq_false (show ¬ (j ≥ n) by omega), Bool.false_and, Bool.xor_false]
  · have hNj : N.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num)
        (by omega)))
    rw [if_neg hj, decide_eq_true (show j ≥ n by omega), Bool.true_and, hNj, Bool.false_xor]

theorem two_pow_eight_mul (p : ℕ) : 2 ^ (8 * p) = 256 ^ p := by
  rw [pow_mul]
  norm_num

/-- `cellOfBits` turns `XOR` into field addition. -/
theorem cellOfBits_add (a b : BitVec 128) :
    cellOfBits a + cellOfBits b = cellOfBits (a ^^^ b) := by
  unfold cellOfBits
  rw [add_limbs, BitVec.extractLsb'_xor, BitVec.extractLsb'_xor]
  rfl

theorem cellOfBits_zero : cellOfBits 0 = 0 := by
  have h := cellOfBits_add 0 0
  rw [add_self_E, BitVec.xor_self] at h
  exact h.symm

theorem pack_lt (d : ℕ → ℕ) (k : ℕ) (hd : ∀ p < k, d p < 256) :
    ∑ p ∈ Finset.range k, 256 ^ p * d p < 256 ^ k := by
  induction k with
  | zero =>
    norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk : d k ≤ 255 := by
      have := hd k (by omega)
      omega
    have h1 := ih (fun p hp => hd p (by omega))
    have h2 : 256 ^ k * d k ≤ 256 ^ k * 255 := Nat.mul_le_mul (le_refl _) hk
    calc ∑ p ∈ Finset.range k, 256 ^ p * d p + 256 ^ k * d k
        < 256 ^ k + 256 ^ k * 255 := Nat.add_lt_add_of_lt_of_le h1 h2
      _ = 256 ^ (k + 1) := by ring

/-- Packing: the field sum of the byte words `d p <<< 8p` is the word of `Σ 256^p d p`. -/
theorem pack_sum_eq (d : ℕ → ℕ) (k : ℕ) (hd : ∀ p < k, d p < 256) :
    ∑ p ∈ Finset.range k, cellOfBits (BitVec.ofNat 128 (d p <<< (8 * p))) =
      cellOfBits (BitVec.ofNat 128 (∑ p ∈ Finset.range k, 256 ^ p * d p)) := by
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, Finset.sum_range_zero]
    exact cellOfBits_zero.symm
  | succ k ih =>
    have hlt : ∑ p ∈ Finset.range k, 256 ^ p * d p < 2 ^ (8 * k) := by
      rw [two_pow_eight_mul]
      exact pack_lt d k (fun p hp => hd p (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (fun p hp => hd p (by omega)),
      cellOfBits_add, ← BitVec.ofNat_xor, xor_shiftLeft_eq_add hlt, two_pow_eight_mul]

theorem pack_div (d : ℕ → ℕ) (p : ℕ) : ∀ k, (∀ q < k, d q < 256) → p < k →
    (∑ q ∈ Finset.range k, 256 ^ q * d q) / 256 ^ p % 256 = d p := by
  intro k
  induction k with
  | zero =>
    intro _ h
    exact absurd h (Nat.not_lt_zero p)
  | succ k ih =>
    intro hd hpk
    rw [Finset.sum_range_succ]
    by_cases hlt : p < k
    · have hpos : 0 < 256 ^ p := by
        exact pow_pos (by norm_num) p
      have e : 256 ^ k = 256 ^ p * 256 * 256 ^ (k - p - 1) := by
        rw [← pow_succ, ← pow_add, show p + 1 + (k - p - 1) = k by omega]
      have hsplit : 256 ^ k * d k = 256 ^ p * (256 * (256 ^ (k - p - 1) * d k)) := by
        rw [e]
        ring
      rw [hsplit, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
      exact ih (fun q hq => hd q (by omega)) hlt
    · have hpk' : p = k := by omega
      have hpos : 0 < 256 ^ k := by
        exact pow_pos (by norm_num) k
      rw [hpk', Nat.add_mul_div_left _ _ hpos,
        Nat.div_eq_of_lt (pack_lt d k (fun q hq => hd q (by omega))), Nat.zero_add,
        Nat.mod_eq_of_lt (hd k (by omega))]

/-- Injectivity of packing: a packed word of sixteen bytes determines each byte. -/
theorem byte_of_pack (d : ℕ → ℕ) (hd : ∀ p < 16, d p < 256) (w : BitVec 128)
    (h : cellOfBits (BitVec.ofNat 128 (∑ p ∈ Finset.range 16, 256 ^ p * d p)) = cellOfBits w)
    (p : ℕ) (hp : p < 16) : d p = w.toNat / 256 ^ p % 256 := by
  have hbits := congrArg cellBits h
  rw [cellBits_cellOfBits, cellBits_cellOfBits] at hbits
  have hlt : ∑ q ∈ Finset.range 16, 256 ^ q * d q < 2 ^ 128 :=
    lt_of_lt_of_eq (pack_lt d 16 hd) (by norm_num)
  have hw : w.toNat = ∑ q ∈ Finset.range 16, 256 ^ q * d q := by
    rw [← hbits, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlt
  rw [hw]
  exact (pack_div d p 16 hd hp).symm

theorem pack_bytes (n k : ℕ) :
    ∑ p ∈ Finset.range k, 256 ^ p * (n / 256 ^ p % 256) = n % 256 ^ k := by
  induction k with
  | zero => rw [Finset.sum_range_zero, pow_zero, Nat.mod_one]
  | succ k ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]

theorem ofNat_pack_bytes (w : BitVec 128) :
    BitVec.ofNat 128 (∑ p ∈ Finset.range 16, 256 ^ p * (w.toNat / 256 ^ p % 256)) = w := by
  have hmod : w.toNat % 256 ^ 16 = w.toNat :=
    Nat.mod_eq_of_lt (lt_of_lt_of_eq w.isLt (by norm_num))
  rw [pack_bytes, hmod]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt w.isLt

/-- The honest direction of packing: the byte words of `w` sum to `w`. -/
theorem pack_sum_of_bytes (w : BitVec 128) :
    ∑ p ∈ Finset.range 16, cellOfBits (BitVec.ofNat 128 ((w.toNat / 256 ^ p % 256) <<< (8 * p))) =
      cellOfBits w := by
  have h := pack_sum_eq (fun p => w.toNat / 256 ^ p % 256) 16
    (fun p _ => Nat.mod_lt _ (by norm_num))
  rw [ofNat_pack_bytes] at h
  exact h

theorem extract_lo_toNat {n : ℕ} (m : BitVec n) :
    (m.extractLsb' 0 128).toNat = m.toNat % 256 ^ 16 := by
  have e : (2 : ℕ) ^ 128 = 256 ^ 16 := by norm_num
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rw [e]

theorem extract_hi_toNat {n : ℕ} (m : BitVec n) :
    (m.extractLsb' 128 128).toNat = m.toNat / 256 ^ 16 % 256 ^ 16 := by
  have e : (2 : ℕ) ^ 128 = 256 ^ 16 := by norm_num
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [e]

theorem byte_lo (n p : ℕ) (hp : p < 16) : n % 256 ^ 16 / 256 ^ p % 256 = n / 256 ^ p % 256 := by
  have e : (256 : ℕ) ^ 16 = 256 ^ p * (256 * 256 ^ (15 - p)) := by
    rw [← pow_succ', ← pow_add, show p + (15 - p + 1) = 16 by omega]
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 256 _)]

theorem byte_hi (n p : ℕ) : n / 256 ^ 16 / 256 ^ p % 256 = n / 256 ^ (16 + p) % 256 := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- Byte `p` of message cell 1 is byte `p` of the message. -/
theorem cell1_byte {n : ℕ} (m : BitVec n) (p : ℕ) (hp : p < 16) :
    (m.extractLsb' 0 128).toNat / 256 ^ p % 256 = m.toNat / 256 ^ p % 256 := by
  rw [extract_lo_toNat, byte_lo _ _ hp]

/-- Byte `p` of message cell 2 is byte `16 + p` of the message. -/
theorem cell2_byte {n : ℕ} (m : BitVec n) (p : ℕ) (hp : p < 16) :
    (m.extractLsb' 128 128).toNat / 256 ^ p % 256 = m.toNat / 256 ^ (16 + p) % 256 := by
  rw [extract_hi_toNat, byte_lo _ _ hp, byte_hi]

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
  have hm1 : 128 ≤ (toBits m).length := by
    rw [hm]
    omega
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
  have hm1 : 128 ≤ (toBits m).length := by
    rw [hm]
    omega
  have hm2 : 128 ≤ ((toBits m).drop 128).length := by
    rw [List.length_drop, hm]
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

theorem cellBits_zero_E : cellBits (0 : E) = 0 := by
  rw [← cellOfBits_zero, cellBits_cellOfBits]

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
    inputWord pk msg σ 3 =
      cellOfBits (BitVec.ofNat 128 (min σ.length (maxSignatureBits + 1))) := by
  have hpre : (toBits pk ++ toBits msg).length = 3 * 128 := by
    rw [List.length_append, length_bits, length_bits]
    all_goals rfl
  have h : ((statementBits pk msg σ).drop (3 * 128)).take 128 =
      toBits (BitVec.ofNat 128 (min σ.length (maxSignatureBits + 1))) := by
    unfold statementBits
    rw [List.append_assoc, List.drop_left' hpre]
    exact List.take_left' (length_bits _)
  unfold inputWord
  rw [h, ofBits_bits]

/-- For a signature of the admitted length, cell `4 + i` holds the `i`-th revealed word. -/
theorem inputWord_sigDecode (pk : PublicKey) (msg : Message) (σ : List Bool)
    (hlen : σ.length = 4352) (i : Fin 34) :
    inputWord pk msg σ (4 + i.val) = cellOfBits (decode σ i) := by
  have hpre : (toBits pk ++ toBits msg ++
      toBits (BitVec.ofNat 128 (min σ.length (maxSignatureBits + 1)))).length = 512 := by
    rw [List.length_append, List.length_append, length_bits, length_bits, length_bits]
    all_goals rfl
  have htake : σ.take maxSignatureBits = σ :=
    List.take_of_length_le (by rw [hlen]; unfold maxSignatureBits; omega)
  unfold inputWord statementBits
  rw [show (4 + i.val) * 128 = 512 + 128 * i.val by omega, ← List.drop_drop, List.drop_left' hpre,
    htake]
  rfl

/-- The length cell pins the admitted length: `4352 < 5505`, so the capped length is exact. -/
theorem length_of_inputWord_len (pk : PublicKey) (msg : Message) (σ : List Bool)
    (h : inputWord pk msg σ 3 = cellOfBits (BitVec.ofNat 128 4352)) : σ.length = 4352 := by
  rw [inputWord_len] at h
  have hb := congrArg cellBits h
  rw [cellBits_cellOfBits, cellBits_cellOfBits] at hb
  have hn := congrArg BitVec.toNat hb
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hn
  unfold maxSignatureBits at hn
  have h1 : min σ.length (5504 + 1) < 2 ^ 128 := by
    have : min σ.length (5504 + 1) ≤ 5505 := Nat.min_le_right _ _
    have h2 : (5505 : ℕ) < 2 ^ 128 := by norm_num
    omega
  have h3 : (4352 : ℕ) < 2 ^ 128 := by norm_num
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3] at hn
  omega

/-- With `|σ| = 4352` the statement is `4864 = 38 · 128` bits, so cells `38 … 46` are zero. -/
theorem inputWord_pad_zero (pk : PublicKey) (m : Message) (σ : List Bool)
    (hlen : σ.length = 4352) {i : ℕ} (h38 : 38 ≤ i) (_h47 : i < 47) :
    inputWord pk m σ i = 0 := by
  have hl : (statementBits pk m σ).length ≤ i * 128 := by
    unfold statementBits
    simp only [List.length_append, length_bits, List.length_take, hlen]
    unfold maxSignatureBits pkBits msgBits
    omega
  unfold inputWord
  rw [List.drop_eq_nil_of_le hl, List.take_nil]
  exact cellOfBits_zero

/-- The tie of one half: chain `b0 + i` contributes its digit at in-cell byte `15 - i`, so the
half's field sum is the packed word of the bytes `b ↦ D (b0 + 15 - b)`. -/
theorem tie_sum_half (D : ℕ → ℕ) (b0 : ℕ) (hD : ∀ i < 16, D (b0 + i) < 256) :
    ∑ i ∈ Finset.range 16, cellOfBits (BitVec.ofNat 128 (D (b0 + i) <<< (8 * (15 - i)))) =
      cellOfBits (BitVec.ofNat 128 (∑ b ∈ Finset.range 16, 256 ^ b * D (b0 + 15 - b))) := by
  refine (Finset.sum_range_reflect _ 16).symm.trans ((Finset.sum_congr rfl ?_).trans
    (pack_sum_eq (fun b => D (b0 + 15 - b)) 16 (fun b hb => by
      have h := hD (15 - b) (by omega)
      rwa [show b0 + (15 - b) = b0 + 15 - b by omega] at h)))
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [show 16 - 1 - j = 15 - j by omega, show 15 - (15 - j) = j by omega,
    show b0 + (15 - j) = b0 + 15 - j by omega]

/-- Element `i` of a big-endian digit list. -/
theorem getElem_digitsOfBaseW (n w : ℕ) : ∀ (len i : ℕ)
    (h : i < (Checksum.digitsOfBaseW n w len).length),
    (Checksum.digitsOfBaseW n w len)[i]'h = n / w ^ (len - 1 - i) % w := by
  intro len
  induction len with
  | zero =>
    intro i h
    rw [Checksum.digitsOfBaseW_length] at h
    exact absurd h (Nat.not_lt_zero i)
  | succ len ih =>
    intro i h
    cases i with
    | zero =>
      simp only [Checksum.digitsOfBaseW, List.getElem_cons_zero,
        show len + 1 - 1 - 0 = len by omega]
    | succ i =>
      have hi : i < (Checksum.digitsOfBaseW n w len).length := by
        rw [Checksum.digitsOfBaseW_length] at h ⊢
        omega
      simp only [Checksum.digitsOfBaseW, List.getElem_cons_succ,
        show len + 1 - 1 - (i + 1) = len - 1 - i by omega]
      exact ih i hi

/-- The two checksum digits, most significant first. -/
theorem digitsOfBaseW_two (C : ℕ) :
    Checksum.digitsOfBaseW C 256 2 = [C / 256 % 256, C % 256] := by
  simp only [Checksum.digitsOfBaseW, pow_one, pow_zero, Nat.div_one]

/-- Message digit `i < 32` is byte `31 - i` of the message (little-endian byte index). -/
theorem digit_of_lt (m : Message) (i : Fin 34) (hi : i.val < 32) :
    digit m i = m.toNat / 256 ^ (31 - i.val) % 256 := by
  have hlt : i.val < (messageDigits m).length := by
    rw [messageDigits_length]
    exact hi
  have hlt' : i.val < (Checksum.digitsOfBaseW m.toNat 256 32).length := by
    rw [Checksum.digitsOfBaseW_length]
    exact hi
  have h1 : digit m i = (messageDigits m)[i.val]'hlt := by
    exact List.getElem_append_left hlt
  have h2 : (Checksum.digitsOfBaseW m.toNat 256 32)[i.val]'hlt' =
      m.toNat / 256 ^ (31 - i.val) % 256 := by
    rw [getElem_digitsOfBaseW, show 32 - 1 - i.val = 31 - i.val by omega]
  exact h1.trans h2

/-- Digits `16 ≤ i < 32` are bytes of message cell 1, at in-cell byte `31 - i`. -/
theorem digit_cell1 (m : Message) (i : Fin 34) (h1 : 16 ≤ i.val) (h2 : i.val < 32) :
    digit m i = (m.extractLsb' 0 128).toNat / 256 ^ (31 - i.val) % 256 := by
  rw [digit_of_lt m i h2, cell1_byte m (31 - i.val) (by omega)]

/-- Digits `i < 16` are bytes of message cell 2, at in-cell byte `15 - i`. -/
theorem digit_cell2 (m : Message) (i : Fin 34) (h : i.val < 16) :
    digit m i = (m.extractLsb' 128 128).toNat / 256 ^ (15 - i.val) % 256 := by
  rw [digit_of_lt m i (by omega), cell2_byte m (15 - i.val) (by omega),
    show 16 + (15 - i.val) = 31 - i.val by omega]

/-! ## 5. The checksum -/

theorem sum_map_digitsOfBaseW (f : ℕ → ℕ) (n w : ℕ) : ∀ len,
    ((Checksum.digitsOfBaseW n w len).map f).sum = ∑ j ∈ Finset.range len, f (n / w ^ j % w) := by
  intro len
  induction len with
  | zero =>
    simp only [Checksum.digitsOfBaseW_nil, List.map_nil, List.sum_nil, Finset.sum_range_zero]
  | succ len ih =>
    simp only [Checksum.digitsOfBaseW, List.map_cons, List.sum_cons, Finset.sum_range_succ, ih]
    omega

/-- The scheme's checksum value, as a sum over the message bytes. -/
theorem checksum_eq_sum (m : Message) :
    Checksum.wotsChecksumValue 256 (messageDigits m) =
      ∑ i ∈ Finset.range 32, (255 - m.toNat / 256 ^ (31 - i) % 256) := by
  have h1 := sum_map_digitsOfBaseW (fun d => 256 - 1 - d) m.toNat 256 32
  have h2 := Finset.sum_range_reflect (fun j => 255 - m.toNat / 256 ^ j % 256) 32
  exact h1.trans h2.symm

theorem wotsChecksum_le (m : Message) :
    Checksum.wotsChecksumValue 256 (messageDigits m) ≤ 255 * 32 :=
  (Checksum.wotsChecksumValue_le (messageDigits_length m) (messageDigits_lt m)).trans
    (by norm_num)

/-- The high checksum digit. -/
theorem digit_hi_checksum (m : Message) (i : Fin 34) (hi : i.val = 32) :
    digit m i = Checksum.wotsChecksumValue 256 (messageDigits m) / 256 := by
  have hC := wotsChecksum_le m
  have hle : (messageDigits m).length ≤ i.val := by
    rw [messageDigits_length]
    omega
  have hlt : i.val - (messageDigits m).length <
      (Checksum.digitsOfBaseW (Checksum.wotsChecksumValue 256 (messageDigits m)) 256 2).length := by
    rw [Checksum.digitsOfBaseW_length, messageDigits_length]
    omega
  have h1 : digit m i = (Checksum.digitsOfBaseW (Checksum.wotsChecksumValue 256 (messageDigits m))
      256 2)[i.val - (messageDigits m).length]'hlt := by
    exact List.getElem_append_right hle
  have e : 2 - 1 - (i.val - (messageDigits m).length) = 1 := by
    rw [messageDigits_length]
    omega
  rw [h1, getElem_digitsOfBaseW, e, pow_one]
  exact Nat.mod_eq_of_lt (by omega)

/-- The low checksum digit. -/
theorem digit_lo_checksum (m : Message) (i : Fin 34) (hi : i.val = 33) :
    digit m i = Checksum.wotsChecksumValue 256 (messageDigits m) % 256 := by
  have hle : (messageDigits m).length ≤ i.val := by
    rw [messageDigits_length]
    omega
  have hlt : i.val - (messageDigits m).length <
      (Checksum.digitsOfBaseW (Checksum.wotsChecksumValue 256 (messageDigits m)) 256 2).length := by
    rw [Checksum.digitsOfBaseW_length, messageDigits_length]
    omega
  have h1 : digit m i = (Checksum.digitsOfBaseW (Checksum.wotsChecksumValue 256 (messageDigits m))
      256 2)[i.val - (messageDigits m).length]'hlt := by
    exact List.getElem_append_right hle
  have e : 2 - 1 - (i.val - (messageDigits m).length) = 0 := by
    rw [messageDigits_length]
    omega
  rw [h1, getElem_digitsOfBaseW, e, pow_zero, Nat.div_one]

/-- The checksum plus the message digits is `32 · 255`. -/
theorem checksum_add_digits (m : Message) (d : ℕ → ℕ)
    (hd : ∀ k (hk : k < 32), d k = digit m ⟨k, by omega⟩) :
    Checksum.wotsChecksumValue 256 (messageDigits m) + ∑ k ∈ Finset.range 32, d k = 8160 := by
  rw [checksum_eq_sum, ← Finset.sum_add_distrib]
  have h : ∀ k ∈ Finset.range 32, 255 - m.toNat / 256 ^ (31 - k) % 256 + d k = 255 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have h1 : digit m ⟨k, by omega⟩ = m.toNat / 256 ^ (31 - k) % 256 :=
      digit_of_lt m ⟨k, by omega⟩ hk'
    have h2 : m.toNat / 256 ^ (31 - k) % 256 < 256 := Nat.mod_lt _ (by norm_num)
    rw [hd k hk', h1]
    omega
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The checksum identity recovers the two checksum digits: if the message chains carry the
message digits, `E 33 ≤ 255` and `Σ_{k<32} E k + 256 · E 32 + E 33 = 8160`, then `E 32` and
`E 33` are digits 32 and 33. -/
theorem checksum_digits (m : Message) (D : ℕ → ℕ)
    (hd : ∀ k (hk : k < 32), D k = digit m ⟨k, by omega⟩) (h33 : D 33 ≤ 255)
    (hsum : ∑ k ∈ Finset.range 32, D k + 256 * D 32 + D 33 = 8160) :
    D 32 = digit m ⟨32, by norm_num⟩ ∧ D 33 = digit m ⟨33, by norm_num⟩ := by
  have hC := checksum_add_digits m D hd
  rw [digit_hi_checksum m _ rfl, digit_lo_checksum m _ rfl]
  omega

/-- The honest direction: the true digits satisfy the checksum identity. -/
theorem checksum_honest_sum (m : Message) (d : ℕ → ℕ)
    (hd : ∀ k (hk : k < 32), d k = digit m ⟨k, by omega⟩) :
    ∑ k ∈ Finset.range 32, d k +
      256 * (Checksum.wotsChecksumValue 256 (messageDigits m) / 256) +
      Checksum.wotsChecksumValue 256 (messageDigits m) % 256 = 8160 := by
  have hC := checksum_add_digits m d hd
  omega

end OptimalOTS.LeanIsaBaseline.Machine
