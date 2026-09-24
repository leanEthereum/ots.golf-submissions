import Submissions.UpperLeanIsa.Records
import Submissions.UpperLeanIsa.TargetBound

/-! Adaptive second-preimage bounds for the concrete tagged query layouts. -/

namespace OptimalOTS.LeanIsaBaseline

open OracleComp OracleComp.EvalDist OracleSpec ENNReal
open scoped Classical
noncomputable section

/-- Adapted from `UpperRiscv.Values.card_filter_setWidth_le`. -/
theorem card_filter_low_le (n m : ℕ) (hm : m ≤ n) (a : BitVec m) :
    (Finset.univ.filter fun w : BitVec n => w.setWidth m = a).card ≤ 2 ^ (n - m) := by
  have key : (Finset.univ.filter fun w : BitVec n => w.setWidth m = a).card ≤
      (Finset.univ : Finset (BitVec (n - m))).card := by
    refine Finset.card_le_card_of_injOn (fun w => (w >>> m).setWidth (n - m))
      (fun _ _ => Finset.mem_univ _) ?_
    intro w hw w' hw' e
    rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
    have hlow : ∀ i, i < m → w.getLsbD i = w'.getLsbD i := by
      intro i hi
      have := congrArg (fun x : BitVec m => x.getLsbD i) (hw.2.trans hw'.2.symm)
      simpa [BitVec.getLsbD_setWidth, hi] using this
    have hhigh : ∀ i, m ≤ i → i < n → w.getLsbD i = w'.getLsbD i := by
      intro i hi1 hi2
      have := congrArg (fun x : BitVec (n - m) => x.getLsbD (i - m)) e
      have h1 : i - m < n - m := by omega
      have h2 : m + (i - m) = i := by omega
      simpa [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, h1, h2] using this
    apply BitVec.eq_of_getLsbD_eq
    intro i hi2
    by_cases hi : i < m
    · exact hlow i hi
    · exact hhigh i (by omega) hi2
  rw [Finset.card_univ, Fintype.card_bitVec] at key
  exact key

def AnswerMatches (ξ : Record) (a : HashLocation) (u : BitVec hashBits) : Prop :=
  match a with
  | .inl _ => u.setWidth 128 = (ξ.2 a).setWidth 128
  | .inr i => if i = 38 then u.setWidth 128 = (ξ.2 a).setWidth 128 else u = ξ.2 a

def lowAnswers (v : BitVec hashBits) : Finset (BitVec hashBits) :=
  Finset.univ.filter (fun w => w.setWidth 128 = v.setWidth 128)

theorem lowAnswers_card (v : BitVec hashBits) : (lowAnswers v).card ≤ 2 ^ 128 := by
  have h := card_filter_low_le hashBits 128 (by norm_num [hashBits]) (v.setWidth 128)
  have hn : hashBits - 128 = 128 := rfl
  rw [hn] at h
  exact h

def matchingAnswers (ξ : Record) (a : HashLocation) : Finset (BitVec hashBits) :=
  match a with
  | .inl _ => lowAnswers (ξ.2 a)
  | .inr i => if i = 38 then lowAnswers (ξ.2 a) else {ξ.2 a}

theorem matchingAnswers_card (ξ : Record) (a : HashLocation) :
    (matchingAnswers ξ a).card ≤ 2 ^ 128 := by
  cases a with
  | inl a => exact lowAnswers_card _
  | inr i =>
    change (if i = 38 then lowAnswers (ξ.2 (.inr i)) else {ξ.2 (.inr i)}).card ≤ _
    split
    · exact lowAnswers_card _
    · rw [Finset.card_singleton]
      exact Nat.one_le_pow _ _ (by decide)

attribute [local irreducible] hashBits matchingAnswers Record.query queryLocation

def secondPreimageTargets (ξ : Record) (q : Query) : Finset (BitVec hashBits) :=
  match queryLocation q with
  | none => ∅
  | some a => if ξ.query a = q then ∅ else matchingAnswers ξ a

theorem secondPreimageTargets_query (ξ : Record) (a : HashLocation) :
    secondPreimageTargets ξ (ξ.query a) = ∅ := by
  unfold secondPreimageTargets
  rw [queryLocation_query]
  exact if_pos rfl

theorem no_secondPreimage_initial (ξ : Record) : ¬ TargetHit (secondPreimageTargets ξ) ξ.cache := by
  rintro ⟨q, u, hc, ht⟩
  obtain ⟨a, rfl, _⟩ := (ξ.cache_some_iff q u).mp hc
  rw [secondPreimageTargets_query] at ht
  exact Finset.notMem_empty _ ht

def secondPreimageRate : ℝ≥0∞ := (2 ^ 129)⁻¹

theorem secondPreimage_charge (ξ : Record) (q : Query) :
    (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (secondPreimageTargets ξ q).card ≤
      secondPreimageRate * queryCost (.inr q) := by
  cases hl : queryLocation q with
  | none => simp only [secondPreimageTargets, hl, Finset.card_empty, Nat.cast_zero, mul_zero]; exact bot_le
  | some a =>
    simp only [secondPreimageTargets, hl]
    by_cases ha : ξ.query a = q
    · rw [if_pos ha, Finset.card_empty, Nat.cast_zero, mul_zero]; exact bot_le
    · rw [if_neg ha]
      have hw := queryLocation_some_width hl
      have hc := matchingAnswers_card ξ a
      calc
        _ ≤ (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (2 ^ 128 : ℕ) :=
          mul_le_mul' le_rfl (Nat.cast_le.mpr hc)
        _ = secondPreimageRate * queryCost (.inr q) := by
          have hcost : queryCost (.inr q) = 2 := by
            norm_num [queryCost, blockCost, blockBits, hw]
          rw [hcost, Fintype.card_bitVec]
          rw [show hashBits = 256 by unfold hashBits; rfl]
          simp only [Nat.cast_pow, Nat.cast_ofNat, secondPreimageRate]
          have h0 : (2 : ℝ≥0∞) ^ 127 ≠ 0 := by simp
          have ht : (2 : ℝ≥0∞) ^ 127 ≠ ⊤ := by simp
          rw [show (2 : ℝ≥0∞) ^ 256 = 2 ^ 129 * 2 ^ 127 by rw [← pow_add],
            ENNReal.mul_inv (Or.inr ht) (Or.inr h0),
            show (2 : ℝ≥0∞) ^ 128 = 2 ^ 127 * 2 by rw [← pow_succ],
            mul_assoc, ← mul_assoc ((2 : ℝ≥0∞) ^ 127)⁻¹, ENNReal.inv_mul_cancel h0 ht, one_mul]

/-- For a fixed honest record, all subsequent adaptive oracle computations together
hit a new matching output with probability at most one per 2^129 compressions.
The record-to-real-keygen distributional bridge is a separate obligation. -/
theorem secondPreimage_bound {α : Type} (ξ : Record) (oa : OracleComp Spec α)
    (B : ℕ) (hB : CostAtMost oa B) :
    Pr[fun p => TargetHit (secondPreimageTargets ξ) p.2 | run oa ξ.cache] ≤
      secondPreimageRate * B := by
  have h := target_hit_bound (secondPreimageTargets ξ) secondPreimageRate
    (secondPreimage_charge ξ) oa ξ.cache B hB (no_secondPreimage_initial ξ)
  simpa only [E, targetPotential, expectedValue_ite_one] using h

end
end OptimalOTS.LeanIsaBaseline
