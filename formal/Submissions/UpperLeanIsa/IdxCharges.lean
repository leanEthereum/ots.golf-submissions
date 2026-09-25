import Submissions.UpperLeanIsa.IdxLoop

/-!
# Charges of index queries

Ported from UpperRiscv `EncCharges.lean`. The number of index entries `encCount` and the event
`IdxPost` (a new index entry with a given index) only change at index queries:

* `encCount` grows by at most one per query (`encCount_cacheQuery_le`);
* a fresh index answer has a given index with probability `1 / 2 ^ 127` (`idxPost_charge`).

Every leanISA query has 896 bits; a query that is not an index query is recognised by its
content (`∀ u, q ≠ encQuery u`), not by its length.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Params.validSet Params.encQuery

namespace Params

variable (P : Params)






/-- Number of encoding entries of a cache. -/
def encCount (d : Cache) : ℕ :=
  (Finset.univ.filter fun u : EncInput => (d (P.encQuery u)).isSome).card

/-- An encoding entry absent from `d'` is present in `c` with index `i`. -/
def IdxPost (d' c : Cache) (i : ℕ) : Prop :=
  ∃ u, d' (P.encQuery u) = none ∧ ∃ w, c (P.encQuery u) = some w ∧ idxOf w = i

theorem encCount_empty : P.encCount ∅ = 0 := by
  simp [Params.encCount]

theorem encCount_cacheQuery_of_ne (d : Cache) {q : Query}
    (hq : ∀ u : EncInput, q ≠ P.encQuery u) (w : BitVec hashBits) :
    P.encCount (d.cacheQuery q w) = P.encCount d := by
  unfold encCount
  congr 1
  apply Finset.filter_congr
  intro u _
  rw [QueryCache.cacheQuery_of_ne _ _ (hq u).symm]

theorem encCount_cacheQuery_le (d : Cache) (q : Query) (w : BitVec hashBits) :
    P.encCount (d.cacheQuery q w) ≤ P.encCount d + 1 := by
  unfold Params.encCount
  by_cases hq : ∃ u₀ : EncInput, q = P.encQuery u₀
  · obtain ⟨u₀, rfl⟩ := hq
    calc (Finset.univ.filter fun u : EncInput =>
          ((d.cacheQuery (P.encQuery u₀) w) (P.encQuery u)).isSome).card
        ≤ (insert u₀ (Finset.univ.filter fun u : EncInput =>
            (d (P.encQuery u)).isSome)).card := by
          apply Finset.card_le_card
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          rw [Finset.mem_insert, Finset.mem_filter]
          by_cases h : u = u₀
          · exact Or.inl h
          · right
            refine ⟨Finset.mem_univ _, ?_⟩
            rwa [QueryCache.cacheQuery_of_ne _ _ (fun e => h (P.encQuery_inj e))] at hu
      _ ≤ _ := Finset.card_insert_le _ _
  · simp only [not_exists] at hq
    have h : (Finset.univ.filter fun u : EncInput =>
        ((d.cacheQuery q w) (P.encQuery u)).isSome) =
        Finset.univ.filter fun u : EncInput => (d (P.encQuery u)).isSome := by
      apply Finset.filter_congr
      intro u _
      rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm (hq u))]
    rw [h]
    exact Nat.le_succ _

theorem idxPost_cacheQuery_of_ne_enc (d' d : Cache) {q : Query}
    (hq : ∀ u : EncInput, q ≠ P.encQuery u) (w : BitVec hashBits) (i : ℕ) :
    P.IdxPost d' (d.cacheQuery q w) i ↔ P.IdxPost d' d i := by
  have h : ∀ u : EncInput, (d.cacheQuery q w) (P.encQuery u) = d (P.encQuery u) :=
    fun u => QueryCache.cacheQuery_of_ne _ _ (hq u).symm
  simp only [Params.IdxPost, h]

theorem not_idxPost_extend_of_enc_none (d' f : Cache) (hf : ∀ u : EncInput, f (P.encQuery u) = none)
    (i : ℕ) : ¬ P.IdxPost d' (Cache.extend d' f) i := by
  rintro ⟨u, hu, w, hw, -⟩
  rw [Cache.extend_apply, hu, hf] at hw
  simp at hw

/-! ### Auxiliary counting facts -/


/-- Averaging `a * 2 ^ (hashBits - 127)` over the `2 ^ hashBits` answers gives `a / 2 ^ 127`. -/
theorem inv_card_mul_pow (hidx : 127 ≤ hashBits) (a : ℝ≥0∞) :
    (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (a * (2 ^ (hashBits - 127) : ℕ)) =
      a / 2 ^ 127 := by
  have hc : (Fintype.card (BitVec hashBits) : ℝ≥0∞) =
      2 ^ 127 * 2 ^ (hashBits - 127) := by
    rw [Fintype.card_bitVec, ← pow_add, Nat.add_sub_cancel' hidx]
    push_cast
    rfl
  have h2 : ((2 : ℝ≥0∞) ^ (hashBits - 127))⁻¹ * 2 ^ (hashBits - 127) = 1 :=
    ENNReal.inv_mul_cancel (by simp) (by simp)
  rw [hc, Nat.cast_pow, Nat.cast_ofNat, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
    div_eq_mul_inv]
  calc ((2 : ℝ≥0∞) ^ 127)⁻¹ * ((2 : ℝ≥0∞) ^ (hashBits - 127))⁻¹ *
        (a * 2 ^ (hashBits - 127))
      = a * ((2 : ℝ≥0∞) ^ 127)⁻¹ *
          (((2 : ℝ≥0∞) ^ (hashBits - 127))⁻¹ * 2 ^ (hashBits - 127)) := by ring
    _ = a * ((2 : ℝ≥0∞) ^ 127)⁻¹ := by rw [h2, mul_one]

/-- The number of answers with a given index is at most `2 ^ (hashBits - 127)`. -/
theorem card_idxOf_eq_le (hidx : 127 ≤ hashBits) (i : ℕ) :
    (Finset.univ.filter fun w : BitVec hashBits => idxOf w = i).card ≤
      2 ^ (hashBits - 127) := by
  have h1 : (Finset.univ.filter fun w : BitVec hashBits => idxOf w = i) =
      Finset.univ.filter fun w : BitVec hashBits =>
        idxOf w ∈ ({i} : Finset ℕ).filter fun n => n < 2 ^ 127 := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, idxOf_lt w⟩
    · rintro ⟨h, -⟩
      exact h
  rw [h1, card_idxOf_mem _ (fun n hn => (Finset.mem_filter.1 hn).2)]
  calc _ ≤ 1 * 2 ^ (hashBits - 127) :=
        Nat.mul_le_mul_right _ (le_trans (Finset.card_filter_le _ _) (by simp))
    _ = _ := one_mul _

/-! ### `P.IdxPost` -/

/-- A fresh encoding answer at `u` realises `P.IdxPost` (when it did not hold before) iff `u` is
absent from `d'` and the answer has index `i`. -/
theorem idxPost_cacheQuery_enc {d' d : Cache} (u : EncInput) (w : BitVec hashBits) {i : ℕ}
    (h : ¬ P.IdxPost d' d i) :
    P.IdxPost d' (d.cacheQuery (P.encQuery u) w) i ↔ d' (P.encQuery u) = none ∧ idxOf w = i := by
  constructor
  · rintro ⟨u', hu', w', hw', hi⟩
    by_cases hu : u' = u
    · subst hu
      rw [QueryCache.cacheQuery_self] at hw'
      exact ⟨hu', by rw [Option.some.inj hw']; exact hi⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ (fun e => hu (P.encQuery_inj e))] at hw'
      exact absurd ⟨u', hu', w', hw', hi⟩ h
  · rintro ⟨hu, hi⟩
    exact ⟨u, hu, w, QueryCache.cacheQuery_self _ _ _, hi⟩

-- The bound does not use that `u` is fresh in `d` (`hq` is part of the fixed interface).
set_option linter.unusedVariables false in
/-- A fresh encoding answer has index `i` with probability `1 / 2 ^ 127`. -/
theorem idxPost_charge (hidx : 127 ≤ hashBits) (d' d : Cache) (u : EncInput)
    (hq : d (P.encQuery u) = none) (i : ℕ) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        (if P.IdxPost d' (d.cacheQuery (P.encQuery u) w) i then 1 else 0) ≤
      (if P.IdxPost d' d i then 1 else 0) + ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
  by_cases h : P.IdxPost d' d i
  · rw [if_pos h]
    calc ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          (if P.IdxPost d' (d.cacheQuery (P.encQuery u) w) i then 1 else 0)
        ≤ ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * 1 :=
          Finset.sum_le_sum fun w _ => mul_le_mul_right (by split_ifs <;> simp) _
      _ = 1 := sum_inv_card_mul 1
      _ ≤ 1 + ((2 : ℝ≥0∞) ^ 127)⁻¹ := le_self_add
  · rw [if_neg h, zero_add]
    have hle : ∀ w : BitVec hashBits,
        (if P.IdxPost d' (d.cacheQuery (P.encQuery u) w) i then (1 : ℝ≥0∞) else 0) ≤
          if idxOf w = i then 1 else 0 := by
      intro w
      rw [P.idxPost_cacheQuery_enc u w h]
      split_ifs with h₁ h₂ h₂
      · exact le_rfl
      · exact absurd h₁.2 h₂
      · exact zero_le
      · exact le_rfl
    calc ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          (if P.IdxPost d' (d.cacheQuery (P.encQuery u) w) i then 1 else 0)
        ≤ ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
            (if idxOf w = i then 1 else 0) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_right (hle w) _
      _ = (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
            ((Finset.univ.filter fun w : BitVec hashBits => idxOf w = i).card : ℝ≥0∞) := by
          rw [← Finset.mul_sum, Finset.sum_boole]
      _ ≤ (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
            (1 * (2 ^ (hashBits - 127) : ℕ)) := by
          rw [one_mul]
          exact mul_le_mul_right (Nat.cast_le.2 (card_idxOf_eq_le hidx i)) _
      _ = ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
          rw [inv_card_mul_pow hidx, one_div]


end Params

end OptimalOTS.LeanIsaBaseline.Layer
