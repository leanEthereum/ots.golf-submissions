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
4. The tie: the field sums of the shifted digit words the leaves assert (`tieHi`, `tieLo`) are
   the message cells exactly when the digits are the message's base-128 digits (`tie_iff`), and
   the loader's cells (`inputWord_*`, including the zero padding `inputWord_pad_zero`).
5. The checksum identity `Σ_{k<37} E k + 128 · E 37 + E 38 = 4699` recovers the two checksum
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

/-- A chain entered at position `e`: step `e` hashes `σ` (when `e < 127`), steps
`j ∈ (e, 126]` hash the previous output, and for `e = 127` the endpoint is `σ` itself. Then the
endpoint `x 127` is `chainValue f i e (127 - e) σ`. -/
theorem chain_from (f : HashTable) (i e : ℕ) (he : e ≤ 127) (σ : Word) (x : ℕ → Word)
    (hleaf : e < 127 → x (e + 1) = (f ⟨896, chainInput i e σ⟩).extractLsb' 0 128)
    (hbody : ∀ j, e < j → j ≤ 126 →
      x (j + 1) = (f ⟨896, chainInput i j (x j)⟩).extractLsb' 0 128)
    (h127 : e = 127 → x 127 = σ) :
    x 127 = chainValue f i e (127 - e) σ := by
  rcases Nat.lt_or_ge e 127 with hlt | hge
  · have key : ∀ n, e + n ≤ 126 → x (e + n + 1) = chainValue f i e (n + 1) σ := by
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
    have h := key (126 - e) (by omega)
    rwa [show e + (126 - e) + 1 = 127 by omega, show 126 - e + 1 = 127 - e by omega] at h
  · obtain rfl : e = 127 := by omega
    rw [h127 rfl, Nat.sub_self, chainValue_zero']

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
`e k` with metadata `2 + (38 - k)`; then `lo 39` holds `rootValue f xs`. -/
theorem root_sound (f : HashTable) (xs : Fin 39 → Word) (e lo hi : ℕ → E)
    (hxs : ∀ i : Fin 39, xs i = cellBits (e i))
    (hlo0 : cellBits (lo 0) = 0) (hhi0 : cellBits (hi 0) = 0)
    (hlo : ∀ k < 39, cellBits (lo (k + 1)) =
      (f ⟨896, hashInput (cellBits (hi k) ++ cellBits (lo k)) ((cellBits (e k)).setWidth 512)
        (BitVec.ofNat 128 (2 + (38 - k)))⟩).extractLsb' 0 128)
    (hhi : ∀ k < 39, cellBits (hi (k + 1)) =
      (f ⟨896, hashInput (cellBits (hi k) ++ cellBits (lo k)) ((cellBits (e k)).setWidth 512)
        (BitVec.ofNat 128 (2 + (38 - k)))⟩).extractLsb' 128 128) :
    cellBits (lo 39) = rootValue f xs := by
  have h0 : cellBits (hi 0) ++ cellBits (lo 0) = (0 : BitVec 256) := by
    rw [hhi0, hlo0, zero_append_zero_128]
  have hfold := rootValueFold_ofFn f 39 (fun k => cellBits (e k))
    (fun k => cellBits (hi k) ++ cellBits (lo k))
    (fun k hk => out_pair (lo (k + 1)) (hi (k + 1)) _ (hlo k hk) (hhi k hk))
  simp only [h0] at hfold
  have hxs' : xs = fun i : Fin 39 => cellBits (e i) := funext hxs
  have key : (rootValueFold f (List.ofFn xs) 0).extractLsb' 0 128 = cellBits (lo 39) := by
    rw [hxs', hfold, BitVec.extractLsb'_append_eq_right]
  exact key.symm

/-! ## 4. The tie and the loader -/

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

theorem two_pow_seven_mul (p : ℕ) : 2 ^ (7 * p) = 128 ^ p := by
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

theorem pack_lt (d : ℕ → ℕ) (k : ℕ) (hd : ∀ p < k, d p < 128) :
    ∑ p ∈ Finset.range k, 128 ^ p * d p < 128 ^ k := by
  induction k with
  | zero =>
    norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk : d k ≤ 127 := by
      have := hd k (by omega)
      omega
    have h1 := ih (fun p hp => hd p (by omega))
    have h2 : 128 ^ k * d k ≤ 128 ^ k * 127 := Nat.mul_le_mul (le_refl _) hk
    calc ∑ p ∈ Finset.range k, 128 ^ p * d p + 128 ^ k * d k
        < 128 ^ k + 128 ^ k * 127 := Nat.add_lt_add_of_lt_of_le h1 h2
      _ = 128 ^ (k + 1) := by ring

/-- Packing at bit offset `b`: the field sum of the digit words `d p <<< (7p + b)` is the word of
`(Σ 128^p d p) <<< b`. -/
theorem pack_sum_shift (d : ℕ → ℕ) (b k : ℕ) (hd : ∀ p < k, d p < 128) :
    ∑ p ∈ Finset.range k, cellOfBits (BitVec.ofNat 128 (d p <<< (7 * p + b))) =
      cellOfBits (BitVec.ofNat 128 ((∑ p ∈ Finset.range k, 128 ^ p * d p) <<< b)) := by
  induction k with
  | zero =>
    rw [Finset.sum_range_zero, Finset.sum_range_zero, Nat.zero_shiftLeft]
    exact cellOfBits_zero.symm
  | succ k ih =>
    have hlt : ∑ p ∈ Finset.range k, 128 ^ p * d p < 2 ^ (7 * k) := by
      rw [two_pow_seven_mul]
      exact pack_lt d k (fun p hp => hd p (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (fun p hp => hd p (by omega)),
      cellOfBits_add, ← BitVec.ofNat_xor, Nat.shiftLeft_add, ← Nat.shiftLeft_xor_distrib,
      xor_shiftLeft_eq_add hlt, two_pow_seven_mul]

theorem pack_div (d : ℕ → ℕ) (p : ℕ) : ∀ k, (∀ q < k, d q < 128) → p < k →
    (∑ q ∈ Finset.range k, 128 ^ q * d q) / 128 ^ p % 128 = d p := by
  intro k
  induction k with
  | zero =>
    intro _ h
    exact absurd h (Nat.not_lt_zero p)
  | succ k ih =>
    intro hd hpk
    rw [Finset.sum_range_succ]
    by_cases hlt : p < k
    · have hpos : 0 < 128 ^ p := by
        exact pow_pos (by norm_num) p
      have e : 128 ^ k = 128 ^ p * 128 * 128 ^ (k - p - 1) := by
        rw [← pow_succ, ← pow_add, show p + 1 + (k - p - 1) = k by omega]
      have hsplit : 128 ^ k * d k = 128 ^ p * (128 * (128 ^ (k - p - 1) * d k)) := by
        rw [e]
        ring
      rw [hsplit, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
      exact ih (fun q hq => hd q (by omega)) hlt
    · have hpk' : p = k := by omega
      have hpos : 0 < 128 ^ k := by
        exact pow_pos (by norm_num) k
      rw [hpk', Nat.add_mul_div_left _ _ hpos,
        Nat.div_eq_of_lt (pack_lt d k (fun q hq => hd q (by omega))), Nat.zero_add,
        Nat.mod_eq_of_lt (hd k (by omega))]

theorem pack_digits (n k : ℕ) :
    ∑ p ∈ Finset.range k, 128 ^ p * (n / 128 ^ p % 128) = n % 128 ^ k := by
  induction k with
  | zero => rw [Finset.sum_range_zero, pow_zero, Nat.mod_one]
  | succ k ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]

theorem cellOfBits_ofNat_inj {x : ℕ} {b : BitVec 128} (hx : x < 2 ^ 128) :
    cellOfBits (BitVec.ofNat 128 x) = cellOfBits b ↔ x = b.toNat := by
  constructor
  · intro h
    have hb := congrArg cellBits h
    rw [cellBits_cellOfBits, cellBits_cellOfBits] at hb
    rw [← hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  · intro h
    rw [h]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt b.isLt

theorem extract_hi_toNat (m : Message) : (m.extractLsb' 128 128).toNat = m.toNat / 2 ^ 128 := by
  have hm : m.toNat < 2 ^ 256 := m.isLt
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (by omega)

theorem extract_lo_toNat (m : Message) : (m.extractLsb' 0 128).toNat = m.toNat % 2 ^ 128 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- The field sum the tie ops of chains `0 … 18` assert equal to message cell 2: digit `k < 18`
at in-cell bit offset `124 - 7k`, then the high five bits `e 18 / 4` of the straddling digit 18 at
offset 0. -/
noncomputable def tieHi (e : ℕ → ℕ) : E :=
  ∑ k ∈ Finset.range 18, cellOfBits (BitVec.ofNat 128 (e k <<< (124 - 7 * k))) +
    cellOfBits (BitVec.ofNat 128 (e 18 / 4))

/-- The field sum the tie ops of chains `18 … 36` assert equal to message cell 1: the low two bits
`e 18 % 4` of digit 18 at offset 126, then digit `19 ≤ k ≤ 36` at offset `7 (36 - k)`. -/
noncomputable def tieLo (e : ℕ → ℕ) : E :=
  cellOfBits (BitVec.ofNat 128 ((e 18 % 4) <<< 126)) +
    ∑ k ∈ Finset.Ico 19 37, cellOfBits (BitVec.ofNat 128 (e k <<< (7 * (36 - k))))

/-- The digits `0 … 17`, little-endian, as a number. -/
def packHi (e : ℕ → ℕ) : ℕ := ∑ p ∈ Finset.range 18, 128 ^ p * e (17 - p)

/-- The digits `19 … 36`, little-endian, as a number. -/
def packLo (e : ℕ → ℕ) : ℕ := ∑ p ∈ Finset.range 18, 128 ^ p * e (36 - p)

/-- All 37 digits, little-endian, as a number. -/
def packAll (e : ℕ → ℕ) : ℕ := ∑ p ∈ Finset.range 37, 128 ^ p * e (36 - p)

theorem tieHi_eq (e : ℕ → ℕ) (he : ∀ k < 37, e k < 128) :
    tieHi e = cellOfBits (BitVec.ofNat 128 (e 18 / 4 + 2 ^ 5 * packHi e)) := by
  have hr : ∑ k ∈ Finset.range 18, cellOfBits (BitVec.ofNat 128 (e k <<< (124 - 7 * k))) =
      ∑ p ∈ Finset.range 18, cellOfBits (BitVec.ofNat 128 (e (17 - p) <<< (7 * p + 5))) := by
    refine (Finset.sum_range_reflect _ 18).symm.trans (Finset.sum_congr rfl fun p hp => ?_)
    have := Finset.mem_range.mp hp
    rw [show 18 - 1 - p = 17 - p by omega, show 124 - 7 * (17 - p) = 7 * p + 5 by omega]
  have hp : ∑ p ∈ Finset.range 18, cellOfBits (BitVec.ofNat 128 (e (17 - p) <<< (7 * p + 5))) =
      cellOfBits (BitVec.ofNat 128 (packHi e <<< 5)) :=
    pack_sum_shift (fun p => e (17 - p)) 5 18 (fun p hp => he _ (by omega))
  have hq : e 18 / 4 < 2 ^ 5 := by
    have := he 18 (by norm_num)
    omega
  unfold tieHi
  rw [hr, hp, cellOfBits_add, ← BitVec.ofNat_xor, Nat.xor_comm, xor_shiftLeft_eq_add hq]

theorem tieLo_eq (e : ℕ → ℕ) (he : ∀ k < 37, e k < 128) :
    tieLo e = cellOfBits (BitVec.ofNat 128 (packLo e + 2 ^ 126 * (e 18 % 4))) := by
  have hr : ∑ k ∈ Finset.Ico 19 37, cellOfBits (BitVec.ofNat 128 (e k <<< (7 * (36 - k)))) =
      ∑ p ∈ Finset.range 18, cellOfBits (BitVec.ofNat 128 (e (36 - p) <<< (7 * p + 0))) := by
    rw [Finset.sum_Ico_eq_sum_range, show 37 - 19 = 18 from rfl]
    refine (Finset.sum_range_reflect _ 18).symm.trans (Finset.sum_congr rfl fun p hp => ?_)
    have := Finset.mem_range.mp hp
    rw [show 19 + (18 - 1 - p) = 36 - p by omega, show 7 * (36 - (36 - p)) = 7 * p + 0 by omega]
  have hp : ∑ p ∈ Finset.range 18, cellOfBits (BitVec.ofNat 128 (e (36 - p) <<< (7 * p + 0))) =
      cellOfBits (BitVec.ofNat 128 (packLo e <<< 0)) :=
    pack_sum_shift (fun p => e (36 - p)) 0 18 (fun p hp => he _ (by omega))
  have hQ : packLo e < 2 ^ 126 :=
    lt_of_lt_of_eq (pack_lt (fun p => e (36 - p)) 18 (fun p hp => he _ (by omega)))
      (by norm_num)
  unfold tieLo
  rw [hr, hp, Nat.shiftLeft_zero, cellOfBits_add, ← BitVec.ofNat_xor, Nat.xor_comm,
    xor_shiftLeft_eq_add (N := packLo e) (a := e 18 % 4) (n := 126) hQ]

/-- Cell 2 above cell 1 is the whole message number: the straddling digit 18 splits at bit 128. -/
theorem pack_split (e : ℕ → ℕ) :
    2 ^ 128 * (e 18 / 4 + 2 ^ 5 * packHi e) + (packLo e + 2 ^ 126 * (e 18 % 4)) = packAll e := by
  have h1 : ∑ x ∈ Finset.range 18, 128 ^ (18 + (x + 1)) * e (36 - (18 + (x + 1))) =
      2 ^ 133 * packHi e := by
    unfold packHi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_range.mp hx
    rw [show 36 - (18 + (x + 1)) = 17 - x by omega, show 18 + (x + 1) = 19 + x by omega, pow_add,
      show (128 : ℕ) ^ 19 = 2 ^ 133 by norm_num]
    ring
  have h2 : 128 ^ (18 + 0) * e (36 - (18 + 0)) = 2 ^ 126 * e 18 := by norm_num
  have h3 := Nat.div_add_mod (e 18) 4
  have h4 : packAll e = packLo e + (∑ x ∈ Finset.range 18,
      128 ^ (18 + (x + 1)) * e (36 - (18 + (x + 1))) + 128 ^ (18 + 0) * e (36 - (18 + 0))) := by
    unfold packAll packLo
    rw [show 37 = 18 + (18 + 1) from rfl, Finset.sum_range_add,
      Finset.sum_range_succ' (fun x => 128 ^ (18 + x) * e (36 - (18 + x))) 18]
  rw [h4, h1, h2]
  omega

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
    (hlen : σ.length = 4992) (i : Fin 39) :
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

/-- The length cell pins the admitted length: `4992 < 5505`, so the capped length is exact. -/
theorem length_of_inputWord_len (pk : PublicKey) (msg : Message) (σ : List Bool)
    (h : inputWord pk msg σ 3 = cellOfBits (BitVec.ofNat 128 4992)) : σ.length = 4992 := by
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
  have h3 : (4992 : ℕ) < 2 ^ 128 := by norm_num
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3] at hn
  omega

/-- With `|σ| = 4992` the statement is `5504 = 43 · 128` bits, so cells `43 … 46` are zero. -/
theorem inputWord_pad_zero (pk : PublicKey) (m : Message) (σ : List Bool)
    (hlen : σ.length = 4992) {i : ℕ} (h43 : 43 ≤ i) (_h47 : i < 47) :
    inputWord pk m σ i = 0 := by
  have hl : (statementBits pk m σ).length ≤ i * 128 := by
    unfold statementBits
    simp only [List.length_append, length_bits, List.length_take, hlen]
    unfold maxSignatureBits pkBits msgBits
    omega
  unfold inputWord
  rw [List.drop_eq_nil_of_le hl, List.take_nil]
  exact cellOfBits_zero

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

/-- Message digit `i < 37` is the base-128 digit `36 - i` of the message (little-endian index). -/
theorem digit_of_lt (m : Message) (i : Fin 39) (hi : i.val < 37) :
    digit m i = m.toNat / 128 ^ (36 - i.val) % 128 := by
  have hlt : i.val < (messageDigits m).length := by
    rw [messageDigits_length]
    exact hi
  have hlt' : i.val < (Checksum.digitsOfBaseW m.toNat 128 37).length := by
    rw [Checksum.digitsOfBaseW_length]
    exact hi
  have h1 : digit m i = (messageDigits m)[i.val]'hlt := by
    exact List.getElem_append_left hlt
  have h2 : (Checksum.digitsOfBaseW m.toNat 128 37)[i.val]'hlt' =
      m.toNat / 128 ^ (36 - i.val) % 128 := by
    rw [getElem_digitsOfBaseW, show 37 - 1 - i.val = 36 - i.val by omega]
  exact h1.trans h2

/-- The top digit has four significant bits: `256 = 36 · 7 + 4`. -/
theorem digit_zero_lt (m : Message) : digit m ⟨0, by norm_num⟩ < 16 := by
  rw [digit_of_lt m _ (by norm_num)]
  have hm : m.toNat < 2 ^ 256 := m.isLt
  show m.toNat / 128 ^ 36 % 128 < 16
  omega

/-- **The tie.** For digits `e k < 128` (`k < 37`) with `e 0 < 16`, the tie sums are the two
message cells exactly when `e` is the message's digit vector. -/
theorem tie_iff (m : Message) (e : ℕ → ℕ) (he : ∀ k < 37, e k < 128) (he0 : e 0 < 16) :
    (tieHi e = cellOfBits (m.extractLsb' 128 128) ∧ tieLo e = cellOfBits (m.extractLsb' 0 128)) ↔
      ∀ k (hk : k < 37), e k = digit m ⟨k, by omega⟩ := by
  have hP : packHi e < 16 * 128 ^ 17 := by
    unfold packHi
    rw [Finset.sum_range_succ]
    have h1 := pack_lt (fun p => e (17 - p)) 17 (fun p hp => he _ (by omega))
    have h3 : 128 ^ 17 * e (17 - 17) ≤ 128 ^ 17 * 15 := Nat.mul_le_mul_left _ (by
      show e 0 ≤ 15
      omega)
    exact lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le h1 h3) (by norm_num)
  have hQ : packLo e < 128 ^ 18 := pack_lt (fun p => e (36 - p)) 18 (fun p hp => he _ (by omega))
  have hsplit := pack_split e
  have hr : e 18 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h18 := he 18 (by norm_num)
  have hm : m.toNat < 2 ^ 256 := m.isLt
  have hHi : e 18 / 4 + 2 ^ 5 * packHi e < 2 ^ 128 := by omega
  have hLo : packLo e + 2 ^ 126 * (e 18 % 4) < 2 ^ 128 := by omega
  have hdig : ∀ k (hk : k < 37), digit m ⟨k, by omega⟩ = m.toNat / 128 ^ (36 - k) % 128 :=
    fun k hk => digit_of_lt m ⟨k, by omega⟩ hk
  rw [tieHi_eq e he, tieLo_eq e he, cellOfBits_ofNat_inj hHi, cellOfBits_ofNat_inj hLo,
    extract_hi_toNat, extract_lo_toNat]
  constructor
  · rintro ⟨h1, h2⟩ k hk
    have hN : packAll e = m.toNat := by omega
    have h := pack_div (fun p => e (36 - p)) (36 - k) 37 (fun q hq => he _ (by omega)) (by omega)
    rw [show 36 - (36 - k) = k by omega] at h
    unfold packAll at hN
    rw [hdig k hk, ← h, hN]
  · intro h
    have hN : packAll e = m.toNat := by
      have hmN : m.toNat = ∑ p ∈ Finset.range 37, 128 ^ p * (m.toNat / 128 ^ p % 128) := by
        rw [pack_digits, Nat.mod_eq_of_lt (by omega)]
      rw [hmN]
      unfold packAll
      refine Finset.sum_congr rfl fun p hp => ?_
      have := Finset.mem_range.mp hp
      rw [h (36 - p) (by omega), hdig _ (by omega), show 36 - (36 - p) = p by omega]
    omega

/-- The tie accumulator after chain `k ≤ 35`: the partial sum of `tieHi` for `k < 18`, and of
`tieLo` from chain 18 on. -/
noncomputable def tieAcc (e : ℕ → ℕ) (k : ℕ) : E :=
  if k < 18 then ∑ i ∈ Finset.range (k + 1), cellOfBits (BitVec.ofNat 128 (e i <<< (124 - 7 * i)))
  else cellOfBits (BitVec.ofNat 128 ((e 18 % 4) <<< 126)) +
    ∑ i ∈ Finset.Ico 19 (k + 1), cellOfBits (BitVec.ofNat 128 (e i <<< (7 * (36 - i))))

theorem tieAcc_zero (e : ℕ → ℕ) : tieAcc e 0 = cellOfBits (BitVec.ofNat 128 (e 0 <<< 124)) := by
  unfold tieAcc
  rw [if_pos (by norm_num), Finset.sum_range_one]

theorem tieAcc_succ_lo (e : ℕ → ℕ) {k : ℕ} (h1 : 1 ≤ k) (h17 : k ≤ 17) :
    tieAcc e k = tieAcc e (k - 1) + cellOfBits (BitVec.ofNat 128 (e k <<< (124 - 7 * k))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold tieAcc
  rw [if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel, Finset.sum_range_succ _ (j + 1)]

theorem tieAcc_18 (e : ℕ → ℕ) : tieAcc e 18 = cellOfBits (BitVec.ofNat 128 ((e 18 % 4) <<< 126)) := by
  unfold tieAcc
  rw [if_neg (by norm_num), Finset.Ico_self, Finset.sum_empty, add_zero]

theorem tieAcc_succ_hi (e : ℕ → ℕ) {k : ℕ} (h19 : 19 ≤ k) :
    tieAcc e k = tieAcc e (k - 1) + cellOfBits (BitVec.ofNat 128 (e k <<< (7 * (36 - k)))) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold tieAcc
  rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel, Finset.sum_Ico_succ_top (by omega),
    add_assoc]

theorem tieHi_acc (e : ℕ → ℕ) : tieHi e = tieAcc e 17 + cellOfBits (BitVec.ofNat 128 (e 18 / 4)) := by
  unfold tieAcc
  rw [if_pos (by norm_num)]
  rfl

theorem tieLo_acc (e : ℕ → ℕ) : tieLo e = tieAcc e 35 + cellOfBits (BitVec.ofNat 128 (e 36)) := by
  have h := tieAcc_succ_hi e (k := 36) (by norm_num)
  rw [show 7 * (36 - 36) = 0 from rfl, Nat.shiftLeft_zero] at h
  rw [← h]
  unfold tieAcc
  rw [if_neg (by norm_num)]
  rfl

/-- Accumulator cells obeying the tie ops of chains `0 … 36` close the message cells `c2`, `c1`
on the tie sums. -/
theorem tie_chain (e : ℕ → ℕ) (acc : ℕ → E) (c1 c2 : E)
    (h0 : acc 0 = cellOfBits (BitVec.ofNat 128 (e 0 <<< 124)))
    (hlo : ∀ k, 1 ≤ k → k ≤ 17 →
      acc k = acc (k - 1) + cellOfBits (BitVec.ofNat 128 (e k <<< (124 - 7 * k))))
    (h18a : c2 = acc 17 + cellOfBits (BitVec.ofNat 128 (e 18 / 4)))
    (h18b : acc 18 = cellOfBits (BitVec.ofNat 128 ((e 18 % 4) <<< 126)))
    (hhi : ∀ k, 19 ≤ k → k ≤ 35 →
      acc k = acc (k - 1) + cellOfBits (BitVec.ofNat 128 (e k <<< (7 * (36 - k)))))
    (h36 : c1 = acc 35 + cellOfBits (BitVec.ofNat 128 (e 36))) :
    c2 = tieHi e ∧ c1 = tieLo e := by
  have hL : ∀ k, k ≤ 17 → acc k = tieAcc e k := by
    intro k
    induction k with
    | zero => intro _; rw [h0, tieAcc_zero]
    | succ k ih =>
      intro hk
      rw [hlo (k + 1) (by omega) hk, tieAcc_succ_lo e (by omega) hk, Nat.add_sub_cancel,
        ih (by omega)]
  have hH : ∀ n, 18 + n ≤ 35 → acc (18 + n) = tieAcc e (18 + n) := by
    intro n
    induction n with
    | zero => intro _; rw [Nat.add_zero, h18b, tieAcc_18]
    | succ n ih =>
      intro hn
      rw [hhi (18 + (n + 1)) (by omega) hn, tieAcc_succ_hi e (by omega),
        show 18 + (n + 1) - 1 = 18 + n by omega, ih (by omega)]
  refine ⟨?_, ?_⟩
  · rw [h18a, hL 17 le_rfl, tieHi_acc]
  · rw [h36, show (35 : ℕ) = 18 + 17 from rfl, hH 17 le_rfl, tieLo_acc]

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

/-- The scheme's checksum value, as a sum over the message digits. -/
theorem checksum_eq_sum (m : Message) :
    Checksum.wotsChecksumValue 128 (messageDigits m) =
      ∑ i ∈ Finset.range 37, (127 - m.toNat / 128 ^ (36 - i) % 128) := by
  have h1 := sum_map_digitsOfBaseW (fun d => 128 - 1 - d) m.toNat 128 37
  have h2 := Finset.sum_range_reflect (fun j => 127 - m.toNat / 128 ^ j % 128) 37
  exact h1.trans h2.symm

theorem wotsChecksum_le (m : Message) :
    Checksum.wotsChecksumValue 128 (messageDigits m) ≤ 127 * 37 :=
  (Checksum.wotsChecksumValue_le (messageDigits_length m) (messageDigits_lt m)).trans
    (by norm_num)

/-- The high checksum digit. -/
theorem digit_hi_checksum (m : Message) (i : Fin 39) (hi : i.val = 37) :
    digit m i = Checksum.wotsChecksumValue 128 (messageDigits m) / 128 := by
  have hC := wotsChecksum_le m
  have hle : (messageDigits m).length ≤ i.val := by
    rw [messageDigits_length]
    omega
  have hlt : i.val - (messageDigits m).length <
      (Checksum.digitsOfBaseW (Checksum.wotsChecksumValue 128 (messageDigits m)) 128 2).length := by
    rw [Checksum.digitsOfBaseW_length, messageDigits_length]
    omega
  have h1 : digit m i = (Checksum.digitsOfBaseW (Checksum.wotsChecksumValue 128 (messageDigits m))
      128 2)[i.val - (messageDigits m).length]'hlt := by
    exact List.getElem_append_right hle
  have e : 2 - 1 - (i.val - (messageDigits m).length) = 1 := by
    rw [messageDigits_length]
    omega
  rw [h1, getElem_digitsOfBaseW, e, pow_one]
  exact Nat.mod_eq_of_lt (by omega)

/-- The low checksum digit. -/
theorem digit_lo_checksum (m : Message) (i : Fin 39) (hi : i.val = 38) :
    digit m i = Checksum.wotsChecksumValue 128 (messageDigits m) % 128 := by
  have hle : (messageDigits m).length ≤ i.val := by
    rw [messageDigits_length]
    omega
  have hlt : i.val - (messageDigits m).length <
      (Checksum.digitsOfBaseW (Checksum.wotsChecksumValue 128 (messageDigits m)) 128 2).length := by
    rw [Checksum.digitsOfBaseW_length, messageDigits_length]
    omega
  have h1 : digit m i = (Checksum.digitsOfBaseW (Checksum.wotsChecksumValue 128 (messageDigits m))
      128 2)[i.val - (messageDigits m).length]'hlt := by
    exact List.getElem_append_right hle
  have e : 2 - 1 - (i.val - (messageDigits m).length) = 0 := by
    rw [messageDigits_length]
    omega
  rw [h1, getElem_digitsOfBaseW, e, pow_zero, Nat.div_one]

/-- The checksum plus the message digits is `37 · 127`. -/
theorem checksum_add_digits (m : Message) (d : ℕ → ℕ)
    (hd : ∀ k (hk : k < 37), d k = digit m ⟨k, by omega⟩) :
    Checksum.wotsChecksumValue 128 (messageDigits m) + ∑ k ∈ Finset.range 37, d k = 4699 := by
  rw [checksum_eq_sum, ← Finset.sum_add_distrib]
  have h : ∀ k ∈ Finset.range 37, 127 - m.toNat / 128 ^ (36 - k) % 128 + d k = 127 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have h1 : digit m ⟨k, by omega⟩ = m.toNat / 128 ^ (36 - k) % 128 :=
      digit_of_lt m ⟨k, by omega⟩ hk'
    have h2 : m.toNat / 128 ^ (36 - k) % 128 < 128 := Nat.mod_lt _ (by norm_num)
    rw [hd k hk', h1]
    omega
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The checksum identity recovers the two checksum digits: if the message chains carry the
message digits, `E 38 ≤ 127` and `Σ_{k<37} E k + 128 · E 37 + E 38 = 4699`, then `E 37` and
`E 38` are digits 37 and 38. -/
theorem checksum_digits (m : Message) (D : ℕ → ℕ)
    (hd : ∀ k (hk : k < 37), D k = digit m ⟨k, by omega⟩) (h38 : D 38 ≤ 127)
    (hsum : ∑ k ∈ Finset.range 37, D k + 128 * D 37 + D 38 = 4699) :
    D 37 = digit m ⟨37, by norm_num⟩ ∧ D 38 = digit m ⟨38, by norm_num⟩ := by
  have hC := checksum_add_digits m D hd
  rw [digit_hi_checksum m _ rfl, digit_lo_checksum m _ rfl]
  omega

/-- The honest direction: the true digits satisfy the checksum identity. -/
theorem checksum_honest_sum (m : Message) (d : ℕ → ℕ)
    (hd : ∀ k (hk : k < 37), d k = digit m ⟨k, by omega⟩) :
    ∑ k ∈ Finset.range 37, d k +
      128 * (Checksum.wotsChecksumValue 128 (messageDigits m) / 128) +
      Checksum.wotsChecksumValue 128 (messageDigits m) % 128 = 4699 := by
  have hC := checksum_add_digits m d hd
  omega

end OptimalOTS.LeanIsaBaseline.Machine
