import Submissions.UpperLeanIsa.Replay

/-!
# The experiment in stages

The strong-unforgeability experiment of `scheme` against an adversary `A` is
`keygen >>= rest A` (`experiment_eq`), where `rest` runs the first attacker stage, signing
(`rest₂`), the second attacker stage and verification (`stB`).

This file also fixes the notation of the security proof: the success indicator `g`, the uniform
record weight `w`, the weight `sumW` of a set of records, the indicator `ind`, and the charge
`κ = 2 · 2⁻¹²⁹` per compression; together with small cache and public-data facts.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

attribute [local irreducible] hashBits blockBits msgBits securityBits maxSignatureBits
attribute [local irreducible] keygenBudget signBudget verifyBudget

local instance instDecEqRecordStages : DecidableEq Record := Classical.decEq Record

variable (A : OracleAlgorithm.Adversary)

/-! ## The experiment in stages -/

/-- Second attacker stage, verification, and the final check. -/
def stB (pk : PublicKey) (m₁ : Message) (st : A.State) (σ : Option OracleAlgorithm.Signature) :
    OracleComp Spec Bool := do
  let (m₂, σ₂) ← A.forge st σ
  let ok ← verify pk m₂ σ₂
  return ok && decide (σ.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

/-- Signing followed by the second stage. -/
def rest₂ (pk : PublicKey) (sk : Words) (y : Message × A.State) : OracleComp Spec Bool :=
  sign sk y.1 >>= stB A pk y.1 y.2

/-- Everything after key generation. -/
def rest (x : PublicKey × Words) : OracleComp Spec Bool := A.choose x.1 >>= rest₂ A x.1 x.2

theorem experiment_eq : OracleAlgorithm.experiment scheme A = keygen >>= rest A := by
  unfold OracleAlgorithm.experiment rest rest₂ stB
  first
  | rfl
  | (congr 1; funext x; rcases x with ⟨pk, sk⟩; congr 1; funext y; rcases y with ⟨m₁, st⟩; rfl)

/-! ## Notation of the security proof -/

/-- The success indicator. -/
def g (p : Bool × Cache) : ℝ≥0∞ := if p.1 = true then 1 else 0

theorem g_le_one (p : Bool × Cache) : g p ≤ 1 := by
  unfold g
  split_ifs <;> simp

/-- `probTrue` as an expectation over the lazy-oracle run from the empty cache. -/
theorem probTrue_eq_E_run (oa : OracleComp Spec Bool) : probTrue oa = E (run oa ∅) g := by
  unfold probTrue
  rw [run'_eq, probOutput_map_eq_tsum_ite, E, expectedValue_def]
  refine tsum_congr fun x => ?_
  rcases x with ⟨b, c⟩
  cases b <;> simp [g]

/-- The uniform weight of a record. -/
def w : ℝ≥0∞ := (Fintype.card Record : ℝ≥0∞)⁻¹

/-- The weight of a set of records. -/
def sumW (T : Finset Record) : ℝ≥0∞ := ∑ _ξ ∈ T, w

/-- An indicator. -/
def ind (p : Prop) : ℝ≥0∞ := if p then 1 else 0

theorem ind_of {p : Prop} (h : p) : ind p = 1 := by
  unfold ind
  exact if_pos h

theorem ind_not {p : Prop} (h : ¬ p) : ind p = 0 := by
  unfold ind
  exact if_neg h

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  by_cases h : p
  · exact le_of_eq (ind_of h)
  · exact (ind_not h).trans_le zero_le

theorem card_record_pos_stg : 0 < Fintype.card Record :=
  Fintype.card_pos_iff.2 ⟨((fun _ => 0), (fun _ => 0))⟩

theorem card_record_ne_zero_stg : (Fintype.card Record : ℝ≥0∞) ≠ 0 := by
  have h : Fintype.card Record ≠ 0 := Nat.pos_iff_ne_zero.1 card_record_pos_stg
  exact_mod_cast h

theorem w_ne_zero_stg : w ≠ 0 := by
  unfold w
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

theorem sum_w : ∑ _ξ : Record, w = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold w
  exact ENNReal.mul_inv_cancel card_record_ne_zero_stg (ENNReal.natCast_ne_top _)

/-- The charge per compression: a hidden-input charge plus a second-preimage charge. -/
def κ : ℝ≥0∞ := 2 * secondPreimageRate

theorem κ_eq : κ = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  unfold κ secondPreimageRate
  rw [show (2 : ℝ≥0∞) ^ 129 = 2 * 2 ^ 128 by rw [← pow_succ']]
  rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-! ## Cache facts -/

theorem Cache.disjoint_of_not_hits {c f : Cache} (h : ¬ Cache.Hits c f) :
    Cache.Disjoint c f := by
  intro q hq
  rcases hc : c q with _ | u
  · rfl
  · exact (h ⟨q, hq, by simp [hc]⟩).elim

theorem Cache.sub_extend_left (c f : Cache) : Cache.Sub c (Cache.extend c f) :=
  fun _ _ h => Cache.extend_apply_of_some h

/-- Monotonicity of `extend` in its first argument. The disjointness hypothesis is needed:
without it a point of `f` absent from `c` could carry a different answer in `c'`. -/
theorem Cache.extend_mono_left {c c' : Cache} (f : Cache) (h : Cache.Sub c c')
    (hd : Cache.Disjoint c' f) :
    Cache.Sub (Cache.extend c f) (Cache.extend c' f) := by
  intro q u hq
  rcases hc : c q with _ | v
  · rw [Cache.extend_apply_of_none hc] at hq
    have hfq : (f q).isSome := by simp [hq]
    rw [Cache.extend_apply_of_none (hd q hfq)]
    exact hq
  · rw [Cache.extend_apply_of_some hc] at hq
    rw [Cache.extend_apply_of_some (h q v hc)]
    exact hq

theorem Cache.disjoint_extend {c f h : Cache} (hc : Cache.Disjoint c h)
    (hf : Cache.Disjoint f h) : Cache.Disjoint (Cache.extend c f) h := by
  intro q hq
  rw [Cache.extend_apply_of_none (hc q hq)]
  exact hf q hq

/-- The honest cache of `ξ` survives when the exposed part is replaced by any extension `c` that
avoids the hidden points. -/
theorem record_cache_sub_extend_hidden (d : Cut) (ξ : Record) (c : Cache)
    (hc : Cache.Sub (exposedCache d ξ) c) (hh : ¬ Cache.Hits c (hiddenCache d ξ)) :
    Cache.Sub ξ.cache (Cache.extend c (hiddenCache d ξ)) := by
  rw [← exposure_partition d ξ]
  exact Cache.extend_mono_left _ hc (Cache.disjoint_of_not_hits hh)

/-! ## Cuts and public data -/

theorem beforeSigning_val_stg (i : Fin 34) : (beforeSigning i).val = 255 := rfl

theorem afterSigning_val_stg (m : Message) (i : Fin 34) : (afterSigning m i).val = digit m i := rfl

/-- Every point hidden after signing was already hidden before signing. -/
theorem hiddenCache_mono (m : Message) (ξ : Record) (q : Query)
    (hq : (hiddenCache (afterSigning m) ξ q).isSome) :
    (hiddenCache beforeSigning ξ q).isSome := by
  obtain ⟨a, ha, hqa⟩ := (hiddenCache_isSome_iff (afterSigning m) ξ q).1 hq
  refine (hiddenCache_isSome_iff beforeSigning ξ q).2 ⟨a, ?_, hqa⟩
  cases a with
  | inl a =>
    rcases a with ⟨i, j⟩
    show j.val < (beforeSigning i).val
    rw [beforeSigning_val_stg]
    exact j.isLt
  | inr i => exact ha.elim

theorem publicKey_data_eq (d : Cut) (ξ ζ : Record) (h : publicData d ξ = publicData d ζ) :
    ξ.publicKey = ζ.publicKey := by
  have ha : ξ.2 (.inr 33) = ζ.2 (.inr 33) := exposed_answer_eq d ξ ζ h (.inr 33) (fun hh => hh)
  unfold Record.publicKey
  simp only [ha]
  all_goals with_unfolding_all rfl

/-- The public data before signing are part of the public data after signing. -/
theorem publicData_before_of_after (m : Message) (ξ ζ : Record)
    (h : publicData (afterSigning m) ξ = publicData (afterSigning m) ζ) :
    publicData beforeSigning ξ = publicData beforeSigning ζ := by
  have hchain : ∀ (i : Fin 34) (j : Fin 255), (afterSigning m i).val ≤ j.val + 1 →
      ξ.2 (.inl (i, j)) = ζ.2 (.inl (i, j)) := by
    intro i j hj
    have he := congrArg (fun v : PublicData => v.2 (.inl (i, j))) h
    simp only [publicData, if_pos hj, Option.some.injEq] at he
    exact he
  have hroot : ∀ k : Fin 34, ξ.2 (.inr k) = ζ.2 (.inr k) := fun k =>
    Option.some.inj (congrArg (fun v : PublicData => v.2 (.inr k)) h)
  apply Prod.ext
  · funext i
    have hne : (beforeSigning i).val ≠ 0 := by
      rw [beforeSigning_val_stg]
      omega
    simp only [publicData, hne, ↓reduceIte]
  · funext a
    rcases a with ⟨i, j⟩ | k
    · by_cases hj : (beforeSigning i).val ≤ j.val + 1
      · have hj' : (afterSigning m i).val ≤ j.val + 1 := by
          have h1 := digit_le m i
          have h2 := beforeSigning_val_stg i
          have h3 := afterSigning_val_stg m i
          omega
        simp only [publicData, hj, ↓reduceIte, hchain i j hj']
      · simp only [publicData, hj, ↓reduceIte]
    · simp only [publicData, hroot k]

end OptimalOTS.LeanIsaBaseline

end
