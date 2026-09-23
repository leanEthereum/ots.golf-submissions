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

The machine program (design `M-machine-design.md`, §2–§4) checks a Winternitz signature with
straight-line `MUL` / `XOR` / `BLAKE2S` constraints. This file proves, over plain functions and
values, the facts that turn those constraints into the scheme's fixed-table verifier. Nothing
here mentions the program or its execution, so the lemmas can be glued to any layout.

1. `E` has characteristic two, and a Boolean cell (`t = t * t`) is `0` or `1`.
2. Boolean and monotone cells form a thermometer with zero-count `d`.
3. A thermometer-weighted accumulator telescopes to `U d`.
4. The multiplexer `σ + t · (x + σ)` selects `σ` or `x`.
5. The chain cells compute `chainValue`; `BLAKE2S` operands give `chainInput` and absorb inputs.
6. The absorb states compute `rootValue`.
7. Packing the `V` links recovers message bytes, and `digit m i` is a message byte.
8. The `gpow` product check recovers the two checksum digits.
-/

namespace OptimalOTS.LeanIsaBaseline.Machine

open LeanerVM.Parameters
open OptimalOTS.LeanIsa (cellBits cellOfBits cellBits_cellOfBits blake2sQuery hashInput
  inputWord statementBits)

/-! ## 1. Characteristic two and Boolean cells -/

/-- Addition in `E` is limb-wise `XOR`, so every word is its own negative. -/
theorem add_self_E (a : E) : a + a = 0 := by
  first
  | exact CharTwo.add_self_eq_zero a
  | exact E.ext fun i => by rw [limb_add, limb_zero]; exact BF64.add_self _

/-- Addition in `K` is `XOR`. -/
theorem add_self_K (a : K) : a + a = 0 := BF64.add_self a

/-- A Boolean cell of a field is `0` or `1`. -/
theorem eq_zero_or_one_of_mul_self {F : Type*} [Field F] {t : F} (h : t = t * t) :
    t = 0 ∨ t = 1 := by
  have h1 : t * (t - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (sub_eq_zero.mp h2)

/-! ## 2. Thermometers -/

/-- Boolean cells `t 0, …, t (n-1)` with `t j = t j · t (j+1)` are a thermometer: zeros, then
ones, with `d ≤ n` zeros. -/
theorem exists_thermo {F : Type*} [Field F] (t : ℕ → F) (n : ℕ)
    (hb : ∀ j < n, t j = t j * t j) (hm : ∀ j, j + 1 < n → t j = t j * t (j + 1)) :
    ∃ d ≤ n, ∀ j < n, t j = if d ≤ j then 1 else 0 := by
  induction n with
  | zero => exact ⟨0, le_refl 0, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    obtain ⟨d, hd, ht⟩ := ih (fun j hj => hb j (by omega)) (fun j hj => hm j (by omega))
    rcases eq_zero_or_one_of_mul_self (hb n (by omega)) with h0 | h1
    · refine ⟨n + 1, le_refl _, fun j hj => ?_⟩
      rw [if_neg (show ¬ (n + 1 ≤ j) by omega)]
      by_cases hjn : j < n
      · rw [ht j hjn]
        by_cases hdj : d ≤ j
        · exfalso
          have hprev : t (n - 1) = 1 := by
            rw [ht (n - 1) (by omega), if_pos (show d ≤ n - 1 by omega)]
          have hm' := hm (n - 1) (by omega)
          rw [show n - 1 + 1 = n by omega, hprev, h0, mul_zero] at hm'
          exact one_ne_zero hm'
        · rw [if_neg hdj]
      · rw [show j = n by omega]
        exact h0
    · refine ⟨d, by omega, fun j hj => ?_⟩
      by_cases hjn : j < n
      · exact ht j hjn
      · rw [show j = n by omega, if_pos hd]
        exact h1

/-- `exists_thermo` with the monotonicity constraint indexed as in the program: the constraint
of step `j ≥ 1` reads `t (j-1) = t (j-1) · t j`. -/
theorem exists_thermo_pred {F : Type*} [Field F] (t : ℕ → F) (n : ℕ)
    (hb : ∀ j < n, t j = t j * t j)
    (hm : ∀ j, 1 ≤ j → j < n → t (j - 1) = t (j - 1) * t j) :
    ∃ d ≤ n, ∀ j < n, t j = if d ≤ j then 1 else 0 :=
  exists_thermo t n hb (fun j hj => by
    have h := hm (j + 1) (by omega) hj
    rwa [Nat.add_sub_cancel] at h)

/-- The honest thermometer satisfies the Boolean constraint. -/
theorem thermo_idem {F : Type*} [Field F] (d j : ℕ) :
    (if d ≤ j then (1 : F) else 0) =
      (if d ≤ j then (1 : F) else 0) * (if d ≤ j then (1 : F) else 0) := by
  by_cases h : d ≤ j
  · rw [if_pos h, mul_one]
  · rw [if_neg h, mul_zero]

/-- The honest thermometer satisfies the monotonicity constraint. -/
theorem thermo_mono {F : Type*} [Field F] (d j : ℕ) :
    (if d ≤ j then (1 : F) else 0) =
      (if d ≤ j then (1 : F) else 0) * (if d ≤ j + 1 then (1 : F) else 0) := by
  by_cases h : d ≤ j
  · rw [if_pos h, if_pos (show d ≤ j + 1 by omega), mul_one]
  · rw [if_neg h, zero_mul]

/-! ## 3. Telescoping links -/

/-- The accumulator invariant: before `d` it still holds the base `U n`, after `d` it holds
`U n + U d + U k`. -/
theorem telescope_inv {F : Type*} [Field F] (h2 : ∀ a : F, a + a = 0) (U acc t : ℕ → F)
    (d n : ℕ) (ht : ∀ j < n, t j = if d ≤ j then 1 else 0) (h0 : acc 0 = U n)
    (hs : ∀ j < n, acc (j + 1) = acc j + t j * (U j + U (j + 1))) :
    ∀ k ≤ n, acc k = if k ≤ d then U n else U n + U d + U k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [if_pos (Nat.zero_le d)]
    exact h0
  | succ k ih =>
    intro hk
    rw [hs k (by omega), ih (by omega), ht k (by omega)]
    by_cases hkd : k + 1 ≤ d
    · rw [if_pos (show k ≤ d by omega), if_neg (show ¬ d ≤ k by omega), if_pos hkd, zero_mul,
        add_zero]
    · by_cases hkd' : k ≤ d
      · have hdk : d = k := by omega
        rw [if_pos hkd', if_pos (show d ≤ k by omega), if_neg hkd, one_mul, hdk]
        ring
      · rw [if_neg hkd', if_pos (show d ≤ k by omega), if_neg hkd, one_mul]
        linear_combination h2 (U k)

/-- Telescoping in characteristic two: an accumulator started at `U n` and advanced by
`t j · (U j + U (j+1))` along a thermometer with `d ≤ n` zeros ends at `U d`. -/
theorem telescope {F : Type*} [Field F] (h2 : ∀ a : F, a + a = 0) (U acc t : ℕ → F)
    (d n : ℕ) (hd : d ≤ n) (ht : ∀ j < n, t j = if d ≤ j then 1 else 0) (h0 : acc 0 = U n)
    (hs : ∀ j < n, acc (j + 1) = acc j + t j * (U j + U (j + 1))) :
    acc n = U d := by
  rw [telescope_inv h2 U acc t d n ht h0 hs n (le_refl n)]
  by_cases hnd : n ≤ d
  · rw [if_pos hnd, show n = d by omega]
  · rw [if_neg hnd]
    linear_combination h2 (U n)

/-- `telescope` as a closed sum. -/
theorem telescope_sum {F : Type*} [Field F] (h2 : ∀ a : F, a + a = 0) (U t : ℕ → F) (d n : ℕ)
    (hd : d ≤ n) (ht : ∀ j < n, t j = if d ≤ j then 1 else 0) :
    U n + ∑ j ∈ Finset.range n, t j * (U j + U (j + 1)) = U d :=
  telescope h2 U (fun k => U n + ∑ j ∈ Finset.range k, t j * (U j + U (j + 1))) t d n hd ht
    (by simp only [Finset.sum_range_zero, add_zero])
    (fun j _ => by simp only [Finset.sum_range_succ, add_assoc])

/-! ## 4. The multiplexer -/

/-- `σ + t · (x + σ)` with a thermometer bit is `x` past the threshold and `σ` before it. The
chain step `j + 1` input and the endpoint (`j = 254`) are both this. -/
theorem mux_step {F : Type*} [Field F] (h2 : ∀ a : F, a + a = 0) (σ x : F) (d j : ℕ) :
    σ + (if d ≤ j then (1 : F) else 0) * (x + σ) = if d ≤ j then x else σ := by
  by_cases h : d ≤ j
  · rw [if_pos h, if_pos h, one_mul]
    linear_combination h2 σ
  · rw [if_neg h, if_neg h, zero_mul, add_zero]

/-- The hash input of chain step `j + 1`: `σ` while `j + 1 ≤ d`, the previous output after. -/
theorem mux_in {F : Type*} [Field F] (h2 : ∀ a : F, a + a = 0) (σ x : F) (d j : ℕ) :
    σ + (if d ≤ j then (1 : F) else 0) * (x + σ) = if j + 1 ≤ d then σ else x := by
  rw [mux_step h2]
  by_cases hdj : d ≤ j
  · rw [if_pos hdj, if_neg (show ¬ (j + 1 ≤ d) by omega)]
  · rw [if_neg hdj, if_pos (show j + 1 ≤ d by omega)]

/-! ## 5. Chains -/

theorem chainValue_zero' (f : HashTable) (i j : ℕ) (x : Word) : chainValue f i j 0 x = x := by
  first
  | rfl
  | simp only [chainValue]

/-- One more chain step, appended at the end. -/
theorem chainValue_succ' (f : HashTable) (i j n : ℕ) (x : Word) :
    chainValue f i j (n + 1) x =
      (f ⟨896, chainInput i (j + n) (chainValue f i j n x)⟩).extractLsb' 0 128 := by
  rw [← chainValue_add f i j n 1 x]
  all_goals first
    | rfl
    | simp only [chainValue]

/-- Soundness of one chain of length `n + 1` (the program uses `n = 254`). The thermometer
`t` has `d` zeros; `inp j` is the multiplexed hash input of step `j` (`inp 0 = σ`, since the
program reads `t (-1)` from a zero cell); `x (j+1)` is the low output cell of step `j`; `e` is
the endpoint multiplexer. Then `e` holds `chainValue f i d (n + 1 - d) σ`. -/
theorem chain_sound (f : HashTable) (i n d : ℕ) (hd : d ≤ n + 1) (σ e : E) (t x inp : ℕ → E)
    (ht : ∀ j < n + 1, t j = if d ≤ j then 1 else 0)
    (hin0 : inp 0 = σ)
    (hin : ∀ j < n, inp (j + 1) = σ + t j * (x (j + 1) + σ))
    (hx : ∀ j < n + 1, cellBits (x (j + 1)) =
      (f ⟨896, chainInput i j (cellBits (inp j))⟩).extractLsb' 0 128)
    (he : e = σ + t n * (x (n + 1) + σ)) :
    cellBits e = chainValue f i d (n + 1 - d) (cellBits σ) := by
  have h2 : ∀ a : E, a + a = 0 := add_self_E
  have hinp : ∀ j ≤ n, inp j = if j ≤ d then σ else x j := by
    intro j hj
    cases j with
    | zero =>
      rw [if_pos (Nat.zero_le d)]
      exact hin0
    | succ j =>
      rw [hin j (by omega), ht j (by omega), mux_in h2]
  have key : ∀ k, d + k ≤ n →
      cellBits (x (d + k + 1)) = chainValue f i d (k + 1) (cellBits σ) := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [hx (d + 0) (by omega), chainValue_succ', hinp (d + 0) (by omega),
        if_pos (show d + 0 ≤ d by omega), chainValue_zero']
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      rw [Nat.add_assoc d k 1] at hprev
      rw [hx (d + (k + 1)) (by omega), chainValue_succ', hinp (d + (k + 1)) (by omega),
        if_neg (show ¬ (d + (k + 1) ≤ d) by omega), hprev]
  rw [he, ht n (by omega), mux_step h2]
  by_cases hdn : d ≤ n
  · rw [if_pos hdn]
    have hk := key (n - d) (by omega)
    rw [show d + (n - d) + 1 = n + 1 by omega, show n - d + 1 = n + 1 - d by omega] at hk
    exact hk
  · rw [if_neg hdn, show n + 1 - d = 0 by omega, chainValue_zero']

/-- `chain_sound` at the program's length, 255 positions. -/
theorem chain_sound_255 (f : HashTable) (i d : ℕ) (hd : d ≤ 255) (σ e : E) (t x inp : ℕ → E)
    (ht : ∀ j < 255, t j = if d ≤ j then 1 else 0)
    (hin0 : inp 0 = σ)
    (hin : ∀ j < 254, inp (j + 1) = σ + t j * (x (j + 1) + σ))
    (hx : ∀ j < 255, cellBits (x (j + 1)) =
      (f ⟨896, chainInput i j (cellBits (inp j))⟩).extractLsb' 0 128)
    (he : e = σ + t 254 * (x 255 + σ)) :
    cellBits e = chainValue f i d (255 - d) (cellBits σ) :=
  chain_sound f i 254 d hd σ e t x inp ht hin0 hin hx he

/-! ### `BLAKE2S` operands as scheme queries -/

theorem zero_append_zero_128 : (0 : BitVec 128) ++ (0 : BitVec 128) = (0 : BitVec 256) := by
  first
  | exact BitVec.zero_append_zero
  | decide
  | rfl

theorem zero_append_three (y : BitVec 128) :
    (0 : BitVec 128) ++ (0 : BitVec 128) ++ (0 : BitVec 128) ++ y = y.setWidth 512 := by
  apply BitVec.eq_of_toNat_eq
  have h0 : (0 : BitVec 128).toNat = 0 := by
    first
    | rfl
    | simp
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

/-! ## 6. The root -/

theorem hi_append_lo (a : BitVec 256) : a.extractLsb' 128 128 ++ a.extractLsb' 0 128 = a := by
  first
  | (have h := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := a) (start₁ := 0)
        (len₁ := 128) (start₂ := 128) (len₂ := 128) rfl
     exact h.trans BitVec.extractLsb'_eq_self)
  | simp [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (start₁ := 0) (len₁ := 128) rfl]

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
    first
    | rfl
    | simp only [List.ofFn_zero, rootValueFold]
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

/-! ## 7. Bytes -/

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
  first
  | rfl
  | (congr 1 <;> first | rfl | exact add_zero _)

theorem cellOfBits_zero : cellOfBits 0 = 0 := by
  have h := cellOfBits_add 0 0
  rw [add_self_E, BitVec.xor_self] at h
  exact h.symm

/-- The `WV` constants are sums of two `V` words. -/
theorem cellOfBits_shift_xor (a b s : ℕ) :
    cellOfBits (BitVec.ofNat 128 ((a ^^^ b) <<< s)) =
      cellOfBits (BitVec.ofNat 128 (a <<< s)) + cellOfBits (BitVec.ofNat 128 (b <<< s)) := by
  rw [cellOfBits_add, ← BitVec.ofNat_xor, Nat.shiftLeft_xor_distrib]

theorem pack_lt (d : ℕ → ℕ) (k : ℕ) (hd : ∀ p < k, d p < 256) :
    ∑ p ∈ Finset.range k, 256 ^ p * d p < 256 ^ k := by
  induction k with
  | zero =>
    first
    | norm_num
    | simp
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
        first
        | exact pow_pos (by norm_num) p
        | positivity
      have e : 256 ^ k = 256 ^ p * 256 * 256 ^ (k - p - 1) := by
        rw [← pow_succ, ← pow_add, show p + 1 + (k - p - 1) = k by omega]
      have hsplit : 256 ^ k * d k = 256 ^ p * (256 * (256 ^ (k - p - 1) * d k)) := by
        rw [e]
        ring
      rw [hsplit, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
      exact ih (fun q hq => hd q (by omega)) hlt
    · have hpk' : p = k := by omega
      have hpos : 0 < 256 ^ k := by
        first
        | exact pow_pos (by norm_num) k
        | positivity
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
  first
  | rw [e]
  | norm_num

theorem extract_hi_toNat {n : ℕ} (m : BitVec n) :
    (m.extractLsb' 128 128).toNat = m.toNat / 256 ^ 16 % 256 ^ 16 := by
  have e : (2 : ℕ) ^ 128 = 256 ^ 16 := by norm_num
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  first
  | rw [e]
  | norm_num

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
    first
    | (simp only [List.getElem_take, List.getElem_drop, toBits, List.getElem_ofFn,
        BitVec.getLsbD_extractLsb', decide_eq_true hiw, Bool.true_and]; done)
    | simp [toBits, hiw]

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
    all_goals omega
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
  first
  | (simp only [Checksum.digitsOfBaseW, pow_one, pow_zero, Nat.div_one]; done)
  | simp [Checksum.digitsOfBaseW]

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
    first
    | exact List.getElem_append_left hlt
    | (unfold digit digits Checksum.wotsFullDigits
       exact List.getElem_append_left hlt)
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

/-! ## 8. The checksum -/

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
    first
    | exact List.getElem_append_right hle
    | (unfold digit digits Checksum.wotsFullDigits
       exact List.getElem_append_right hle)
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
    first
    | exact List.getElem_append_right hle
    | (unfold digit digits Checksum.wotsFullDigits
       exact List.getElem_append_right hle)
  have e : 2 - 1 - (i.val - (messageDigits m).length) = 0 := by
    rw [messageDigits_length]
    omega
  rw [h1, getElem_digitsOfBaseW, e, pow_zero, Nat.div_one]

theorem sum_sub_le (d : ℕ → ℕ) (k : ℕ) : ∑ i ∈ Finset.range k, (255 - d i) ≤ 255 * k := by
  induction k with
  | zero =>
    rw [Finset.sum_range_zero]
    exact Nat.zero_le _
  | succ k ih =>
    rw [Finset.sum_range_succ]
    omega

theorem gpow_mul_gpow (a b : ℕ) : gpow a * gpow b = gpow (a + b) := (pow_add g a b).symm

/-- A product of `ofK (gpow ·)` words is `ofK (gpow ·)` of the summed exponents. -/
theorem ofK_gpow_prod (d : ℕ → ℕ) (k : ℕ) :
    ∏ i ∈ Finset.range k, ofK (gpow (d i)) = ofK (gpow (∑ i ∈ Finset.range k, d i)) := by
  induction k with
  | zero =>
    rw [Finset.prod_range_zero, Finset.sum_range_zero]
    have h1 : ofK (gpow 0) = 1 := by
      rw [show gpow 0 = 1 from pow_zero g]
      exact map_one (algebraMap K E)
    exact h1.symm
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, ih, ← ofK_mul]
    exact congrArg ofK (gpow_mul_gpow _ _)

/-- The checksum product check in `K`: exponents below the group order are recovered, and a
`(a, b)` pair of base-256 digits is the quotient and remainder. -/
theorem checksum_of_gpow (C a b : ℕ) (hC : C ≤ 255 * 32) (ha : a ≤ 255) (hb : b ≤ 255)
    (h : gpow C = gpow (256 * a) * gpow b) : a = C / 256 ∧ b = C % 256 := by
  have h' : gpow C = gpow (256 * a + b) := h.trans (gpow_mul_gpow _ _)
  have hbig : (65536 : ℕ) < 2 ^ 64 - 1 := by norm_num
  have hC' : C ∈ Set.Iio (2 ^ 64 - 1) :=
    Set.mem_Iio.mpr (lt_of_le_of_lt (by omega : C ≤ 65536) hbig)
  have hab : 256 * a + b ∈ Set.Iio (2 ^ 64 - 1) :=
    Set.mem_Iio.mpr (lt_of_le_of_lt (by omega : 256 * a + b ≤ 65536) hbig)
  have hEq : C = 256 * a + b := gpow_injOn hC' hab h'
  exact ⟨by omega, by omega⟩

/-- The checksum product check in `E`. -/
theorem checksum_of_E (C a b : ℕ) (hC : C ≤ 255 * 32) (ha : a ≤ 255) (hb : b ≤ 255)
    (h : ofK (gpow C) = ofK (gpow (256 * a)) * ofK (gpow b)) : a = C / 256 ∧ b = C % 256 := by
  rw [← ofK_mul] at h
  exact checksum_of_gpow C a b hC ha hb (ofK_injective h)

/-- The honest direction: the true checksum digits pass the product check. -/
theorem checksum_honest (C : ℕ) :
    ofK (gpow (256 * (C / 256))) * ofK (gpow (C % 256)) = ofK (gpow C) := by
  rw [← ofK_mul, gpow_mul_gpow, Nat.div_add_mod]

/-- The checksum link: if chain `i < 32` carries message byte `31 - i` and the product check
holds for `(a, b)`, then `a` and `b` are the scheme's digits 32 and 33. -/
theorem checksum_link (m : Message) (d : ℕ → ℕ)
    (hd : ∀ i < 32, d i = m.toNat / 256 ^ (31 - i) % 256) (a b : ℕ) (ha : a ≤ 255)
    (hb : b ≤ 255) (h : gpow (∑ i ∈ Finset.range 32, (255 - d i)) = gpow (256 * a) * gpow b)
    (i32 i33 : Fin 34) (h32 : i32.val = 32) (h33 : i33.val = 33) :
    a = digit m i32 ∧ b = digit m i33 := by
  have hsum : ∑ i ∈ Finset.range 32, (255 - d i) =
      Checksum.wotsChecksumValue 256 (messageDigits m) := by
    rw [checksum_eq_sum]
    exact Finset.sum_congr rfl (fun i hi => by rw [hd i (Finset.mem_range.mp hi)])
  obtain ⟨h1, h2⟩ := checksum_of_gpow _ a b (sum_sub_le d 32) ha hb h
  rw [hsum] at h1 h2
  rw [digit_hi_checksum m i32 h32, digit_lo_checksum m i33 h33]
  exact ⟨h1, h2⟩

/-- `checksum_link` for the constraint as the machine checks it, in `E`. -/
theorem checksum_link_E (m : Message) (d : ℕ → ℕ)
    (hd : ∀ i < 32, d i = m.toNat / 256 ^ (31 - i) % 256) (a b : ℕ) (ha : a ≤ 255)
    (hb : b ≤ 255)
    (h : ofK (gpow (∑ i ∈ Finset.range 32, (255 - d i))) = ofK (gpow (256 * a)) * ofK (gpow b))
    (i32 i33 : Fin 34) (h32 : i32.val = 32) (h33 : i33.val = 33) :
    a = digit m i32 ∧ b = digit m i33 := by
  rw [← ofK_mul] at h
  exact checksum_link m d hd a b ha hb (ofK_injective h) i32 i33 h32 h33

/-- `checksum_link` with the message chains stated through `digit`. -/
theorem checksum_link_digit (m : Message) (d : ℕ → ℕ)
    (hd : ∀ i (hi : i < 32), d i = digit m ⟨i, by omega⟩) (a b : ℕ) (ha : a ≤ 255)
    (hb : b ≤ 255) (h : gpow (∑ i ∈ Finset.range 32, (255 - d i)) = gpow (256 * a) * gpow b)
    (i32 i33 : Fin 34) (h32 : i32.val = 32) (h33 : i33.val = 33) :
    a = digit m i32 ∧ b = digit m i33 :=
  checksum_link m d (fun i hi => (hd i hi).trans (digit_of_lt m ⟨i, by omega⟩ hi)) a b ha hb h
    i32 i33 h32 h33

end OptimalOTS.LeanIsaBaseline.Machine
