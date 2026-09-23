import Submissions.UpperLeanIsa.Stages
import Submissions.UpperLeanIsa.Replay
import Submissions.UpperLeanIsa.HiddenBound

/-!
# Cut-relative second-preimage targets

After the signature at the cut `d = afterSigning m` is released, an accepted forgery either
queries a hidden chain input (bounded in `HiddenBound.lean`), or produces through a fresh input an
answer that matches the honest answer at the same location. `cutTargets d ζ q` collects the
answers of a query `q` that count as such a match:

* at an exposed location (all root positions, and chain positions at or after the cut): every
  answer matching the honest one (`matchingAnswers`), through an input other than the honest one;
* at the boundary location just below the cut, whose honest output is the signed word: every
  answer whose low half is the signed word, whatever the input.

The targets depend only on the public data of the cut (`cutTargets_public`), cost `2⁻¹²⁹` per
compression (`cutTargets_charge`), and have no hit at the start of the second stage
(`no_cutTargets_initial`). `hidden_hit_bound_subset` is `hidden_hit_bound` for a subset of a public
fiber: the resampling charge is paid over the whole fiber, the potential only over the subset.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline

attribute [local irreducible] hashBits publicFiber finiteFiber hiddenCache
attribute [local irreducible] queryLocation Record.query

local instance instDecEqRecordCutTargets : DecidableEq Record := Classical.decEq Record

/-! ## Locations -/

/-- Chain location just below the cut: its answer's low half is the signed word (public). -/
def Boundary (d : Cut) : HashLocation → Prop
  | .inl (i, j) => j.val + 1 = (d i).val
  | .inr _ => False

/-- Every chain location is hidden before signing. -/
theorem hiddenBefore_inl (x : ChainLocation) : Hidden beforeSigning (.inl x) := by
  rcases x with ⟨i, j⟩
  have h255 : (beforeSigning i).val = 255 := rfl
  show j.val < (beforeSigning i).val
  rw [h255]
  exact j.isLt

theorem hiddenBefore_of_hidden {d : Cut} {a : HashLocation} (h : Hidden d a) :
    Hidden beforeSigning a := by
  cases a with
  | inl x => exact hiddenBefore_inl x
  | inr i => exact False.elim h

/-- A cache that does not hit the hidden points of `ξ` before signing is empty at every hidden
query of `ξ`. -/
theorem none_of_not_hits_hidden (d : Cache) (ξ : Record)
    (hh : ¬ Cache.Hits d (hiddenCache beforeSigning ξ)) (a : HashLocation)
    (ha : Hidden beforeSigning a) {q : Query} (hq : ξ.query a = q) : d q = none := by
  rcases hdq : d q with _ | u
  · rfl
  · refine (hh ⟨q, ?_, ?_⟩).elim
    · exact (hiddenCache_isSome_iff beforeSigning ξ q).mpr ⟨a, ha, hq⟩
    · simp only [hdq, Option.isSome_some]

/-! ## The targets -/

/-- Answers of `q` that match the honest answer of `ζ` at the location of `q`, through a
different input (exposed locations) or through any input (the boundary below the cut). -/
def cutTargets (d : Cut) (ζ : Record) (q : Query) : Finset (BitVec hashBits) :=
  match queryLocation q with
  | none => ∅
  | some a =>
    if Hidden d a then (if Boundary d a then matchingAnswers ζ a else ∅)
    else (if ζ.query a = q then ∅ else matchingAnswers ζ a)

theorem cutTargets_of_none (d : Cut) (ζ : Record) {q : Query} (hl : queryLocation q = none) :
    cutTargets d ζ q = ∅ := by
  simp only [cutTargets, hl]

theorem cutTargets_of_location (d : Cut) (ζ : Record) {q : Query} {a : HashLocation}
    (hl : queryLocation q = some a) :
    cutTargets d ζ q =
      if Hidden d a then (if Boundary d a then matchingAnswers ζ a else ∅)
      else (if ζ.query a = q then ∅ else matchingAnswers ζ a) := by
  simp only [cutTargets, hl]

theorem mem_cutTargets_exposed {d : Cut} {ζ : Record} {q : Query} {a : HashLocation}
    (hl : queryLocation q = some a) (ha : ¬ Hidden d a) (hq : ζ.query a ≠ q)
    {u : BitVec hashBits} (hu : u ∈ matchingAnswers ζ a) : u ∈ cutTargets d ζ q := by
  rw [cutTargets_of_location d ζ hl, if_neg ha, if_neg hq]
  exact hu

theorem mem_cutTargets_boundary {d : Cut} {ζ : Record} {q : Query} {a : HashLocation}
    (hl : queryLocation q = some a) (ha : Hidden d a) (hb : Boundary d a)
    {u : BitVec hashBits} (hu : u ∈ matchingAnswers ζ a) : u ∈ cutTargets d ζ q := by
  rw [cutTargets_of_location d ζ hl, if_pos ha, if_pos hb]
  exact hu

/-- Unpacking a target: the location of the query, the matching answer, and which case. -/
theorem mem_cutTargets {d : Cut} {ζ : Record} {q : Query} {u : BitVec hashBits}
    (hu : u ∈ cutTargets d ζ q) :
    ∃ a, queryLocation q = some a ∧ u ∈ matchingAnswers ζ a ∧
      ((¬ Hidden d a ∧ ζ.query a ≠ q) ∨ (Hidden d a ∧ Boundary d a)) := by
  rcases hl : queryLocation q with _ | a
  · rw [cutTargets_of_none d ζ hl] at hu
    exact absurd hu (Finset.notMem_empty u)
  · rw [cutTargets_of_location d ζ hl] at hu
    refine ⟨a, by first | rfl | exact hl, ?_⟩
    by_cases hH : Hidden d a
    · rw [if_pos hH] at hu
      by_cases hb : Boundary d a
      · rw [if_pos hb] at hu
        exact ⟨hu, Or.inr ⟨hH, hb⟩⟩
      · rw [if_neg hb] at hu
        exact absurd hu (Finset.notMem_empty u)
    · rw [if_neg hH] at hu
      by_cases hq : ζ.query a = q
      · rw [if_pos hq] at hu
        exact absurd hu (Finset.notMem_empty u)
      · rw [if_neg hq] at hu
        exact ⟨hu, Or.inl ⟨hH, hq⟩⟩

theorem cutTargets_card_le (d : Cut) (ζ : Record) {q : Query} {a : HashLocation}
    (hl : queryLocation q = some a) : (cutTargets d ζ q).card ≤ 2 ^ 128 := by
  have h0 : (∅ : Finset (BitVec hashBits)).card ≤ 2 ^ 128 := by
    rw [Finset.card_empty]
    exact Nat.zero_le _
  rw [cutTargets_of_location d ζ hl]
  by_cases hH : Hidden d a
  · rw [if_pos hH]
    by_cases hb : Boundary d a
    · rw [if_pos hb]
      exact matchingAnswers_card ζ a
    · rw [if_neg hb]
      exact h0
  · rw [if_neg hH]
    by_cases hq : ζ.query a = q
    · rw [if_pos hq]
      exact h0
    · rw [if_neg hq]
      exact matchingAnswers_card ζ a

/-- A query hits at most `2 ^ 128` of the `2 ^ 256` answers and costs two compressions. -/
theorem cutTargets_charge (d : Cut) (ζ : Record) (q : Query) :
    (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (cutTargets d ζ q).card ≤
      secondPreimageRate * queryCost (.inr q) := by
  cases hl : queryLocation q with
  | none =>
    rw [cutTargets_of_none d ζ hl, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact bot_le
  | some a =>
    have hw := queryLocation_some_width hl
    have hcost : queryCost (.inr q) = 2 := by
      norm_num [queryCost, blockCost, blockBits, hw]
    calc (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (cutTargets d ζ q).card
        ≤ (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (2 ^ 128 : ℕ) :=
          mul_le_mul' le_rfl (Nat.cast_le.mpr (cutTargets_card_le d ζ hl))
      _ = wordGuessRate := uniform_low_rate
      _ = secondPreimageRate * 2 := wordGuessRate_eq
      _ = secondPreimageRate * queryCost (.inr q) := by
          rw [hcost, Nat.cast_ofNat]

/-! ## Public determination -/

private theorem extractLsb'_zero_eq_setWidth' {n : ℕ} (v : BitVec n) :
    v.extractLsb' 0 128 = v.setWidth 128 := by
  rw [← BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.ushiftRight_zero]

private theorem lowAnswers_congr' {v v' : BitVec hashBits}
    (h : v.setWidth 128 = v'.setWidth 128) : lowAnswers v = lowAnswers v' := by
  unfold lowAnswers
  rw [h]

theorem matchingAnswers_congr {ξ ζ : Record} {a : HashLocation} (h : ξ.2 a = ζ.2 a) :
    matchingAnswers ξ a = matchingAnswers ζ a := by
  cases a with
  | inl x => exact congrArg lowAnswers h
  | inr i =>
    change (if i = 33 then lowAnswers (ξ.2 (.inr i)) else {ξ.2 (.inr i)}) =
      (if i = 33 then lowAnswers (ζ.2 (.inr i)) else {ζ.2 (.inr i)})
    rw [h]

/-- The matching answers at an exposed or boundary location are public. -/
theorem matchingAnswers_public (d : Cut) (ξ ζ : Record)
    (h : publicData d ξ = publicData d ζ) (a : HashLocation)
    (ha : ¬ Hidden d a ∨ Boundary d a) : matchingAnswers ξ a = matchingAnswers ζ a := by
  rcases ha with ha | ha
  · exact matchingAnswers_congr (exposed_answer_eq d ξ ζ h a ha)
  · cases a with
    | inr i => exact False.elim ha
    | inl x =>
      rcases x with ⟨i, j⟩
      have hb : j.val + 1 = (d i).val := ha
      have hw := data_word_eq d ξ ζ h i j.succ (by simp only [Fin.val_succ]; omega)
      rw [Record.word_next, Record.word_next, extractLsb'_zero_eq_setWidth',
        extractLsb'_zero_eq_setWidth'] at hw
      change lowAnswers (ξ.2 (.inl (i, j))) = lowAnswers (ζ.2 (.inl (i, j)))
      exact lowAnswers_congr' hw

/-- The targets depend only on the public data of the cut. -/
theorem cutTargets_public (d : Cut) (ξ ζ : Record) (h : publicData d ξ = publicData d ζ) :
    cutTargets d ξ = cutTargets d ζ := by
  funext q
  cases hl : queryLocation q with
  | none => rw [cutTargets_of_none d ξ hl, cutTargets_of_none d ζ hl]
  | some a =>
    rw [cutTargets_of_location d ξ hl, cutTargets_of_location d ζ hl]
    by_cases hH : Hidden d a
    · rw [if_pos hH, if_pos hH]
      by_cases hb : Boundary d a
      · rw [if_pos hb, if_pos hb]
        exact matchingAnswers_public d ξ ζ h a (Or.inr hb)
      · rw [if_neg hb, if_neg hb]
    · rw [if_neg hH, if_neg hH, exposed_query_eq d ξ ζ h a hH,
        matchingAnswers_public d ξ ζ h a (Or.inl hH)]

/-! ## No hit at the start of the second stage -/

theorem secondPreimageTargets_of_ne {ζ : Record} {q : Query} {a : HashLocation}
    (hl : queryLocation q = some a) (hne : ζ.query a ≠ q) :
    secondPreimageTargets ζ q = matchingAnswers ζ a := by
  simp only [secondPreimageTargets, hl]
  exact if_neg hne

/-- If the first stage neither hit a hidden point of `ξ` nor a second-preimage target of `ξ`,
then adding the points exposed by the signature creates no cut-target hit. -/
theorem no_cutTargets_initial (m : Message) (ξ : Record) (d : Cache)
    (hd : ¬ Cache.Hits d (hiddenCache beforeSigning ξ))
    (ht : ¬ TargetHit (secondPreimageTargets ξ) d) :
    ¬ TargetHit (cutTargets (afterSigning m) ξ)
      (Cache.extend d (exposedCache (afterSigning m) ξ)) := by
  rintro ⟨q, u, hq, hu⟩
  obtain ⟨a, hl, hmem, hcase⟩ := mem_cutTargets hu
  rcases hdq : d q with _ | u'
  · -- the answer comes from the exposed honest points: never a target
    rw [Cache.extend_apply_of_none hdq] at hq
    obtain ⟨b, hb, hbq, -⟩ := (exposedCache_some_iff _ ξ q u).mp hq
    have hba : b = a := Option.some.inj ((hbq ▸ queryLocation_query ξ b).symm.trans hl)
    subst hba
    rcases hcase with ⟨-, hne⟩ | ⟨hH, -⟩
    · exact hne hbq
    · exact hb hH
  · -- the answer was already in the first-stage cache
    rw [Cache.extend_apply_of_some hdq] at hq
    have hdu : d q = some u := hdq.trans hq
    rcases hcase with ⟨-, hne⟩ | ⟨hH, -⟩
    · exact ht ⟨q, u, hdu, by rw [secondPreimageTargets_of_ne hl hne]; exact hmem⟩
    · by_cases hqa : ξ.query a = q
      · exact hd ⟨q, (hiddenCache_isSome_iff beforeSigning ξ q).mpr
          ⟨a, hiddenBefore_of_hidden hH, hqa⟩, by simp only [hdu, Option.isSome_some]⟩
      · exact ht ⟨q, u, hdu, by rw [secondPreimageTargets_of_ne hl hqa]; exact hmem⟩

/-! ## Adaptive bounds -/

theorem ind_targetHit_eq (targets : Query → Finset (BitVec hashBits)) (c : Cache) :
    ind (TargetHit targets c) = targetPotential targets c := by
  by_cases h : TargetHit targets c
  · rw [ind_of h, targetPotential, if_pos h]
  · rw [ind_not h, targetPotential, if_neg h]

theorem cutTargets_hit_bound {α : Type} (d : Cut) (ζ : Record) (oa : OracleComp Spec α)
    (c : Cache) (B : ℕ) (hB : CostAtMost oa B) (hc : ¬ TargetHit (cutTargets d ζ) c) :
    E (run oa c) (fun p => ind (TargetHit (cutTargets d ζ) p.2)) ≤ secondPreimageRate * B := by
  have h := target_hit_bound (cutTargets d ζ) secondPreimageRate (cutTargets_charge d ζ) oa c B
    hB hc
  refine le_trans (le_of_eq ?_) h
  exact congrArg (E (run oa c)) (funext fun p => ind_targetHit_eq (cutTargets d ζ) p.2)

/-- Weighted hidden hits of the records of `T`. -/
def hiddenHitPotential (d : Cut) (T : Finset Record) (c : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ T, w * ind (Cache.Hits c (hiddenCache d ξ))

private theorem ind_or_le' (p q : Prop) : ind (p ∨ q) ≤ ind p + ind q := by
  by_cases hp : p
  · rw [ind_of (Or.inl hp : p ∨ q), ind_of hp]
    exact le_self_add
  · by_cases hq : q
    · rw [ind_of (Or.inr hq : p ∨ q), ind_of hq]
      exact le_add_self
    · rw [ind_not (fun h : p ∨ q => h.elim hp hq)]
      exact bot_le

theorem hiddenHitPotential_cacheQuery (d : Cut) (v : PublicData) (T : Finset Record)
    (hT : T ⊆ publicFiber d v) (c : Cache) (q : Query) (u : BitVec hashBits) :
    hiddenHitPotential d T (c.cacheQuery q u) ≤ hiddenHitPotential d T c +
      (secondPreimageRate * sumW (publicFiber d v)) * queryCost (.inr q) := by
  calc hiddenHitPotential d T (c.cacheQuery q u)
      ≤ ∑ ξ ∈ T, (w * ind (Cache.Hits c (hiddenCache d ξ)) +
          w * ind ((hiddenCache d ξ q).isSome)) := by
        unfold hiddenHitPotential
        refine Finset.sum_le_sum fun ξ _ => ?_
        rw [← mul_add, Cache.hits_cacheQuery]
        exact mul_le_mul' le_rfl (ind_or_le' _ _)
    _ = hiddenHitPotential d T c + ∑ ξ ∈ T, w * ind ((hiddenCache d ξ q).isSome) := by
        unfold hiddenHitPotential
        rw [Finset.sum_add_distrib]
    _ ≤ hiddenHitPotential d T c +
          ∑ ξ ∈ publicFiber d v, w * ind ((hiddenCache d ξ q).isSome) :=
        add_le_add le_rfl (Finset.sum_le_sum_of_subset hT)
    _ ≤ hiddenHitPotential d T c +
          ∑ ξ ∈ publicFiber d v, if (hiddenCache d ξ q).isSome then w else 0 := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun ξ _ => ?_)
        by_cases h : (hiddenCache d ξ q).isSome
        · exact le_of_eq (by rw [ind_of h, mul_one, if_pos h])
        · exact le_of_eq (by rw [ind_not h, mul_zero, if_neg h])
    _ ≤ hiddenHitPotential d T c +
          secondPreimageRate * queryCost (.inr q) * ∑ _ξ ∈ publicFiber d v, w :=
        add_le_add le_rfl (hidden_input_charge d v q w)
    _ = hiddenHitPotential d T c +
          (secondPreimageRate * sumW (publicFiber d v)) * queryCost (.inr q) := by
        rw [sumW, mul_right_comm secondPreimageRate]

theorem hiddenHitPotential_charge (d : Cut) (v : PublicData) (T : Finset Record)
    (hT : T ⊆ publicFiber d v) (c : Cache) (q : Query) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      hiddenHitPotential d T (c.cacheQuery q u)) ≤ hiddenHitPotential d T c +
      (secondPreimageRate * sumW (publicFiber d v)) * queryCost (.inr q) := by
  calc
    _ ≤ ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        (hiddenHitPotential d T c +
          (secondPreimageRate * sumW (publicFiber d v)) * queryCost (.inr q)) :=
      Finset.sum_le_sum fun u _ =>
        mul_le_mul' le_rfl (hiddenHitPotential_cacheQuery d v T hT c q u)
    _ = _ := sum_inv_card_mul _

theorem hiddenHitPotential_zero (d : Cut) (T : Finset Record) (c : Cache)
    (hc : ∀ ξ ∈ T, Cache.Disjoint c (hiddenCache d ξ)) : hiddenHitPotential d T c = 0 := by
  unfold hiddenHitPotential
  exact Finset.sum_eq_zero fun ξ hξ => by rw [ind_not (hc ξ hξ).not_hits, mul_zero]

/-- `hidden_hit_bound` for a subset `T` of a public fiber: the potential sums over `T`, the
resampling charge is paid over the whole fiber. -/
theorem hidden_hit_bound_subset {α : Type} (d : Cut) (v : PublicData) (T : Finset Record)
    (hT : T ⊆ publicFiber d v) (oa : OracleComp Spec α) (c : Cache) (B : ℕ)
    (hB : CostAtMost oa B) (hc : ∀ ξ ∈ T, Cache.Disjoint c (hiddenCache d ξ)) :
    E (run oa c) (fun p => ∑ ξ ∈ T, w * ind (Cache.Hits p.2 (hiddenCache d ξ))) ≤
      (secondPreimageRate * sumW (publicFiber d v)) * B := by
  have h := master_single (secondPreimageRate * sumW (publicFiber d v))
    (hiddenHitPotential d T) (fun _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun c' _ q _ _ _ => hiddenHitPotential_charge d v T hT c' q)
    oa (fun _ c' => hiddenHitPotential d T c') (fun _ _ => le_rfl) c B trivial hB
  rw [hiddenHitPotential_zero d T c hc, zero_add] at h
  exact h

end OptimalOTS.LeanIsaBaseline
