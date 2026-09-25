import Submissions.UpperLeanIsa.IdxLoop
import Submissions.UpperLeanIsa.TierCodec

/-!
# Charges of index queries

Ported from UpperRiscv `EncCharges.lean`. The number of index entries `encCount` and the event
`IdxPost` (a new index entry with a given class) only change at index queries:

* `encCount` grows by at most one per query (`encCount_cacheQuery_le`);
* a fresh index answer has class `v` with probability `cweight v / 2 ^ 127`
  (`idxPost_charge`).

Every leanISA query has 896 bits; a query that is not an index query is recognised by its
content (`∀ u, q ≠ encQuery u`), not by its length.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Params.encQuery

namespace Params

variable (P : Params)

/-- Number of encoding entries of a cache. -/
def encCount (d : Cache) : ℕ :=
  (Finset.univ.filter fun u : EncInput => (d (P.encQuery u)).isSome).card

/-- An encoding entry absent from `d'` is present in `c` with class `v`. -/
def IdxPost (d' c : Cache) (v : Cls) : Prop :=
  ∃ u, d' (P.encQuery u) = none ∧ ∃ w, c (P.encQuery u) = some w ∧ P.cls w = some v

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
    (hq : ∀ u : EncInput, q ≠ P.encQuery u) (w : BitVec hashBits) (v : Cls) :
    P.IdxPost d' (d.cacheQuery q w) v ↔ P.IdxPost d' d v := by
  have h : ∀ u : EncInput, (d.cacheQuery q w) (P.encQuery u) = d (P.encQuery u) :=
    fun u => QueryCache.cacheQuery_of_ne _ _ (hq u).symm
  simp only [Params.IdxPost, h]

theorem not_idxPost_extend_of_enc_none (d' f : Cache) (hf : ∀ u : EncInput, f (P.encQuery u) = none)
    (v : Cls) : ¬ P.IdxPost d' (Cache.extend d' f) v := by
  rintro ⟨u, hu, w, hw, -⟩
  rw [Cache.extend_apply, hu, hf] at hw
  simp at hw

/-- A fresh encoding answer at `u` realises `P.IdxPost` (when it did not hold before) iff `u` is
absent from `d'` and the answer has class `v`. -/
theorem idxPost_cacheQuery_enc {d' d : Cache} (u : EncInput) (w : BitVec hashBits) {v : Cls}
    (h : ¬ P.IdxPost d' d v) :
    P.IdxPost d' (d.cacheQuery (P.encQuery u) w) v ↔ d' (P.encQuery u) = none ∧ P.cls w = some v := by
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

theorem two_pow_129_mul_inv' :
    (2 : ℝ≥0∞) ^ 129 * ((Fintype.card (BitVec hashBits) : ℝ≥0∞))⁻¹ = ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
  rw [Fintype.card_bitVec]
  unfold hashBits
  rw [show (256 : ℕ) = 129 + 127 from rfl, Nat.cast_pow, Nat.cast_ofNat, pow_add,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
    ← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]

-- The bound does not use that `u` is fresh in `d` (`hq` is part of the fixed interface).
set_option linter.unusedVariables false in
/-- A fresh encoding answer has class `v` with probability `cweight v / 2 ^ 127`. -/
theorem idxPost_charge (d' d : Cache) (u : EncInput) (hq : d (P.encQuery u) = none) (v : Cls) :
    ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        (if P.IdxPost d' (d.cacheQuery (P.encQuery u) w) v then 1 else 0) ≤
      (if P.IdxPost d' d v then 1 else 0) + (P.cweight v : ℝ≥0∞) / 2 ^ 127 := by
  by_cases h : P.IdxPost d' d v
  · rw [if_pos h]
    calc ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          (if P.IdxPost d' (d.cacheQuery (P.encQuery u) w) v then 1 else 0)
        ≤ ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * 1 :=
          Finset.sum_le_sum fun w _ => mul_le_mul_right (by split_ifs <;> simp) _
      _ = 1 := sum_inv_card_mul 1
      _ ≤ 1 + (P.cweight v : ℝ≥0∞) / 2 ^ 127 := le_self_add
  · rw [if_neg h, zero_add]
    have hle : ∀ w : BitVec hashBits,
        (if P.IdxPost d' (d.cacheQuery (P.encQuery u) w) v then (1 : ℝ≥0∞) else 0) ≤
          if P.cls w = some v then 1 else 0 := by
      intro w
      rw [P.idxPost_cacheQuery_enc u w h]
      split_ifs with h₁ h₂ h₂
      · exact le_rfl
      · exact absurd h₁.2 h₂
      · exact zero_le
      · exact le_rfl
    calc ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          (if P.IdxPost d' (d.cacheQuery (P.encQuery u) w) v then 1 else 0)
        ≤ ∑ w : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
            (if P.cls w = some v then 1 else 0) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_right (hle w) _
      _ = (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
            ((Finset.univ.filter fun w : BitVec hashBits => P.cls w = some v).card : ℝ≥0∞) := by
          rw [← Finset.mul_sum, Finset.sum_boole]
      _ = (P.cweight v : ℝ≥0∞) / 2 ^ 127 := by
          rw [P.card_cls, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_comm,
            mul_assoc, two_pow_129_mul_inv']

end Params

end OptimalOTS.LeanIsaBaseline.Layer
