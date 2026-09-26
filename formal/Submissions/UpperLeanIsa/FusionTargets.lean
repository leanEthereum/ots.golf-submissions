import Submissions.UpperLeanIsa.FusionExposure
import Submissions.UpperLeanIsa.Master

/-!
# Second-preimage targets and hidden-hit potentials

* `TargetHit targets c`: some cached answer lies in the target set of its query. A fresh query
  hits its targets with probability `|targets q| / 2 ^ 256` (`target_charge`).
* `matchingAnswers ξ a`: the answers matching the honest answer at location `a` (the step's
  slice `P.codec.slice k j` at chain steps, the low half at root calls): at most `2 ^ 128` of them,
  i.e. `2 ^ -129` per compression.
* `secondPreimageTargets ξ`: before signing, a matching answer through a different input at any
  location. `cutTargets d ζ`: at cut `d`, a matching answer through a different input at an
  exposed location, or any answer whose slice is the public word at the boundary step just
  below the cut. Both depend only on public data and cost `2 ^ -129` per compression; neither
  has a target at a query that is not a record location (in particular at an index query).
* `hiddenHitPotential d T c`: the weight of the records of `T` whose hidden points `c` hits;
  it grows by at most `rate · sumW (fiber) · cost` per query, and not at all at a query that is
  not a chain step of any record.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer.Fusion

set_option linter.constructorNameAsVariable false

variable {P : Params}

/-! ## Indicators and weights -/

/-- An indicator. -/
def ind (p : Prop) : ℝ≥0∞ := if p then 1 else 0

theorem ind_of {p : Prop} (h : p) : ind p = 1 := if_pos h

theorem ind_not {p : Prop} (h : ¬ p) : ind p = 0 := if_neg h

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  by_cases h : p
  · exact le_of_eq (ind_of h)
  · exact (ind_not h).trans_le zero_le

theorem ind_mono {p q : Prop} (h : p → q) : ind p ≤ ind q := by
  by_cases hp : p
  · rw [ind_of hp, ind_of (h hp)]
  · rw [ind_not hp]; exact zero_le

theorem ind_or_le (p q : Prop) : ind (p ∨ q) ≤ ind p + ind q := by
  by_cases hp : p
  · rw [ind_of (Or.inl hp : p ∨ q), ind_of hp]
    exact le_self_add
  · by_cases hq : q
    · rw [ind_of (Or.inr hq : p ∨ q), ind_of hq]
      exact le_add_self
    · rw [ind_not (fun h : p ∨ q => h.elim hp hq)]
      exact bot_le

theorem ind_congr {p q : Prop} (h : p ↔ q) : ind p = ind q := by
  rw [show p = q from propext h]

variable (P) in
/-- The weight of a set of records. -/
def sumW (T : Finset (Record P)) : ℝ≥0∞ := ∑ _ξ ∈ T, recW P

theorem sumW_mono {T T' : Finset (Record P)} (h : T ⊆ T') : sumW P T ≤ sumW P T' :=
  Finset.sum_le_sum_of_subset h

/-! ## Target hits -/

def TargetHit (targets : Query → Finset (BitVec hashBits)) (c : Cache) : Prop :=
  ∃ q u, c q = some u ∧ u ∈ targets q

theorem targetHit_cacheQuery (targets : Query → Finset (BitVec hashBits))
    (c : Cache) (q : Query) (u : BitVec hashBits) (hc : c q = none) :
    TargetHit targets (c.cacheQuery q u) ↔ TargetHit targets c ∨ u ∈ targets q := by
  constructor
  · rintro ⟨p, v, hv, ht⟩
    by_cases hp : p = q
    · subst p
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hv
      exact Or.inr (hv ▸ ht)
    · rw [QueryCache.cacheQuery_of_ne _ _ hp] at hv
      exact Or.inl ⟨p, v, hv, ht⟩
  · rintro (⟨p, v, hv, ht⟩ | ht)
    · have hp : p ≠ q := by rintro rfl; simp [hc] at hv
      exact ⟨p, v, by rwa [QueryCache.cacheQuery_of_ne _ _ hp], ht⟩
    · exact ⟨q, u, QueryCache.cacheQuery_self _ _ _, ht⟩

theorem targetHit_cacheQuery_of_empty (targets : Query → Finset (BitVec hashBits))
    (c : Cache) (q : Query) (u : BitVec hashBits) (hq : targets q = ∅) :
    TargetHit targets (c.cacheQuery q u) ↔ TargetHit targets c := by
  constructor
  · rintro ⟨p, v, hv, ht⟩
    by_cases hp : p = q
    · subst p
      rw [hq] at ht
      exact absurd ht (Finset.notMem_empty _)
    · rw [QueryCache.cacheQuery_of_ne _ _ hp] at hv
      exact ⟨p, v, hv, ht⟩
  · rintro ⟨p, v, hv, ht⟩
    by_cases hp : p = q
    · subst p
      rw [hq] at ht
      exact absurd ht (Finset.notMem_empty _)
    · exact ⟨p, v, by rwa [QueryCache.cacheQuery_of_ne _ _ hp], ht⟩

/-- One fresh query: the indicator of a target hit grows on average by the target mass. -/
theorem ind_target_charge (targets : Query → Finset (BitVec hashBits)) (c : Cache) (q : Query)
    (hc : c q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ind (TargetHit targets (c.cacheQuery q u)) ≤
      ind (TargetHit targets c) +
        (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (targets q).card := by
  by_cases hh : TargetHit targets c
  · calc _ ≤ ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * 1 :=
          Finset.sum_le_sum fun u _ => mul_le_mul' le_rfl (ind_le_one _)
      _ = 1 := sum_inv_card_mul 1
      _ ≤ _ := by rw [ind_of hh]; exact le_self_add
  · have he : ∀ u, ind (TargetHit targets (c.cacheQuery q u)) = if u ∈ targets q then 1 else 0 := by
      intro u
      unfold ind
      rw [targetHit_cacheQuery targets c q u hc]
      simp only [hh, false_or]
    simp only [he, ind_not hh, zero_add]
    rw [← Finset.mul_sum, Finset.sum_boole]
    simp

/-! ## Matching answers -/

/-- The answers whose low half equals that of `v`. -/
def lowAnswers (v : BitVec hashBits) : Finset (BitVec hashBits) :=
  Finset.univ.filter fun w => w.extractLsb' 0 128 = v.extractLsb' 0 128

theorem mem_lowAnswers {u v : BitVec hashBits} :
    u ∈ lowAnswers v ↔ u.extractLsb' 0 128 = v.extractLsb' 0 128 := by
  unfold lowAnswers
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem lowAnswers_card (v : BitVec hashBits) : (lowAnswers v).card ≤ 2 ^ 128 :=
  card_low_le _

/-- The answers whose slice at chain step `(k, j)` equals that of `v`. -/
def sliceAnswers (k : Fin numChains) (j : ℕ) (v : BitVec hashBits) : Finset (BitVec hashBits) :=
  Finset.univ.filter fun w => P.codec.slice k j w = P.codec.slice k j v

theorem mem_sliceAnswers {k : Fin numChains} {j : ℕ} {u v : BitVec hashBits} :
    u ∈ sliceAnswers (P := P) k j v ↔ P.codec.slice k j u = P.codec.slice k j v := by
  unfold sliceAnswers
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem sliceAnswers_card (k : Fin numChains) (j : ℕ) (v : BitVec hashBits) :
    (sliceAnswers (P := P) k j v).card ≤ 2 ^ 128 :=
  card_slice_le k j _

/-- Answers matching the honest answer at a location: the slice the step passes on at chain
steps, the low half at root calls (the next call reads the low half of the state; the last
call's low half is the public key). -/
def matchingAnswers (ξ : Record P) : Loc P → Finset (BitVec hashBits)
  | .inl a => sliceAnswers (P := P) a.1 a.2.val (ξ.2 (.inl a))
  | .inr r => lowAnswers (ξ.2 (.inr r))

theorem matchingAnswers_inl (ξ : Record P) (a : ChainLoc P) :
    matchingAnswers ξ (.inl a) = sliceAnswers (P := P) a.1 a.2.val (ξ.2 (.inl a)) := rfl

theorem matchingAnswers_inr (ξ : Record P) (r : Fin 3) :
    matchingAnswers ξ (.inr r) = lowAnswers (ξ.2 (.inr r)) := rfl

theorem matchingAnswers_card (ξ : Record P) (a : Loc P) : (matchingAnswers ξ a).card ≤ 2 ^ 128 := by
  cases a with
  | inl a => exact sliceAnswers_card _ _ _
  | inr r => exact lowAnswers_card _

theorem matchingAnswers_congr {ξ ζ : Record P} {a : Loc P} (h : ξ.2 a = ζ.2 a) :
    matchingAnswers ξ a = matchingAnswers ζ a := by
  cases a with
  | inl a => rw [matchingAnswers_inl, matchingAnswers_inl, h]
  | inr r => rw [matchingAnswers_inr, matchingAnswers_inr, h]

/-- The charge of a target set of at most `2 ^ 128` answers at an 896-bit query. -/
theorem card_charge {q : Query} (hw : q.1 = 896) (S : Finset (BitVec hashBits))
    (hS : S.card ≤ 2 ^ 128) :
    (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * S.card ≤ rate * queryCost (.inr q) := by
  rw [queryCost_896 hw, Nat.cast_ofNat, ← inv_card_mul_two_pow_128]
  exact mul_le_mul' le_rfl (Nat.cast_le.mpr hS)

attribute [local irreducible] hashBits matchingAnswers Record.query queryLocation

/-! ## Targets before signing -/

variable (P) in
/-- Before signing: a matching answer through an input other than the honest one, at any
location of `ξ`. -/
def secondPreimageTargets (ξ : Record P) (q : Query) : Finset (BitVec hashBits) :=
  match queryLocation P q with
  | none => ∅
  | some a => if ξ.query a = q then ∅ else matchingAnswers ξ a

theorem secondPreimageTargets_query (hP : P.Hyp) (ξ : Record P) (a : Loc P) :
    secondPreimageTargets P ξ (ξ.query a) = ∅ := by
  unfold secondPreimageTargets
  rw [queryLocation_query hP]
  exact if_pos rfl

theorem secondPreimageTargets_of_none {ξ : Record P} {q : Query}
    (hl : queryLocation P q = none) : secondPreimageTargets P ξ q = ∅ := by
  simp only [secondPreimageTargets, hl]

theorem secondPreimageTargets_of_ne {ζ : Record P} {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) (hne : ζ.query a ≠ q) :
    secondPreimageTargets P ζ q = matchingAnswers ζ a := by
  simp only [secondPreimageTargets, hl]
  exact if_neg hne

theorem secondPreimage_charge (ξ : Record P) (q : Query) :
    (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (secondPreimageTargets P ξ q).card ≤
      rate * queryCost (.inr q) := by
  cases hl : queryLocation P q with
  | none =>
    rw [secondPreimageTargets_of_none hl, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact bot_le
  | some a =>
    simp only [secondPreimageTargets, hl]
    split
    · rw [Finset.card_empty, Nat.cast_zero, mul_zero]; exact bot_le
    · exact card_charge (queryLocation_some_width hl) _ (matchingAnswers_card ξ a)

/-! ## Targets at a cut -/

/-- The chain step just below the cut: its answer's slice is the public word at the cut. -/
def Boundary (d : Cut) : Loc P → Prop
  | .inl a => a.2.val + 1 = d a.1
  | .inr _ => False

variable (P) in
/-- At cut `d`: a matching answer through a different input at an exposed location, or any
answer matching the public word at the boundary step. -/
def cutTargets (d : Cut) (ζ : Record P) (q : Query) : Finset (BitVec hashBits) :=
  match queryLocation P q with
  | none => ∅
  | some a =>
    if Hidden d a then (if Boundary d a then matchingAnswers ζ a else ∅)
    else (if ζ.query a = q then ∅ else matchingAnswers ζ a)

theorem cutTargets_of_none (d : Cut) (ζ : Record P) {q : Query}
    (hl : queryLocation P q = none) : cutTargets P d ζ q = ∅ := by
  simp only [cutTargets, hl]

theorem cutTargets_of_location (d : Cut) (ζ : Record P) {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) :
    cutTargets P d ζ q =
      if Hidden d a then (if Boundary d a then matchingAnswers ζ a else ∅)
      else (if ζ.query a = q then ∅ else matchingAnswers ζ a) := by
  simp only [cutTargets, hl]

theorem mem_cutTargets_exposed {d : Cut} {ζ : Record P} {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) (ha : ¬ Hidden d a) (hq : ζ.query a ≠ q)
    {u : BitVec hashBits} (hu : u ∈ matchingAnswers ζ a) : u ∈ cutTargets P d ζ q := by
  rw [cutTargets_of_location d ζ hl, if_neg ha, if_neg hq]
  exact hu

theorem mem_cutTargets_boundary {d : Cut} {ζ : Record P} {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) (ha : Hidden d a) (hb : Boundary d a)
    {u : BitVec hashBits} (hu : u ∈ matchingAnswers ζ a) : u ∈ cutTargets P d ζ q := by
  rw [cutTargets_of_location d ζ hl, if_pos ha, if_pos hb]
  exact hu

theorem mem_cutTargets {d : Cut} {ζ : Record P} {q : Query} {u : BitVec hashBits}
    (hu : u ∈ cutTargets P d ζ q) :
    ∃ a, queryLocation P q = some a ∧ u ∈ matchingAnswers ζ a ∧
      ((¬ Hidden d a ∧ ζ.query a ≠ q) ∨ (Hidden d a ∧ Boundary d a)) := by
  rcases hl : queryLocation P q with _ | a
  · rw [cutTargets_of_none d ζ hl] at hu
    exact absurd hu (Finset.notMem_empty u)
  · rw [cutTargets_of_location d ζ hl] at hu
    refine ⟨a, rfl, ?_⟩
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

theorem cutTargets_charge (d : Cut) (ζ : Record P) (q : Query) :
    (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (cutTargets P d ζ q).card ≤
      rate * queryCost (.inr q) := by
  cases hl : queryLocation P q with
  | none =>
    rw [cutTargets_of_none d ζ hl, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact bot_le
  | some a =>
    refine card_charge (queryLocation_some_width hl) _ ?_
    rw [cutTargets_of_location d ζ hl]
    split_ifs
    · exact matchingAnswers_card ζ a
    · simp
    · simp
    · exact matchingAnswers_card ζ a

/-- The matching answers at an exposed or boundary location are public. -/
theorem matchingAnswers_public (d : Cut) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) (a : Loc P)
    (ha : ¬ Hidden d a ∨ Boundary d a) : matchingAnswers ξ a = matchingAnswers ζ a := by
  rcases ha with ha | ha
  · exact matchingAnswers_congr (exposed_answer_eq d ξ ζ h a ha)
  · cases a with
    | inr r => exact False.elim ha
    | inl a =>
      rcases a with ⟨k, j⟩
      have hb : j.val + 1 = d k := ha
      have hw := data_word_eq d ξ ζ h k (j.val + 1) (by omega)
      rw [Record.word_succ _ k j.val j.isLt, Record.word_succ _ k j.val j.isLt] at hw
      rw [matchingAnswers_inl, matchingAnswers_inl]
      unfold sliceAnswers
      rw [hw]

/-- The targets depend only on the public data of the cut. -/
theorem cutTargets_public {d : Cut} (hd : ValidCut P d) (ξ ζ : Record P)
    (h : publicData d ξ = publicData d ζ) : cutTargets P d ξ = cutTargets P d ζ := by
  funext q
  cases hl : queryLocation P q with
  | none => rw [cutTargets_of_none d ξ hl, cutTargets_of_none d ζ hl]
  | some a =>
    rw [cutTargets_of_location d ξ hl, cutTargets_of_location d ζ hl]
    by_cases hH : Hidden d a
    · rw [if_pos hH, if_pos hH]
      by_cases hb : Boundary d a
      · rw [if_pos hb, if_pos hb]
        exact matchingAnswers_public d ξ ζ h a (Or.inr hb)
      · rw [if_neg hb, if_neg hb]
    · rw [if_neg hH, if_neg hH, exposed_query_eq hd ξ ζ h a hH,
        matchingAnswers_public d ξ ζ h a (Or.inl hH)]

/-- Every chain location is hidden before signing. -/
theorem hiddenBefore_inl (a : ChainLoc P) : Hidden (beforeSigning P) (.inl a) := by
  show a.2.val < P.codec.len a.1 - 1
  exact a.2.isLt

theorem hiddenBefore_of_hidden {d : Cut} {a : Loc P} (h : Hidden d a) :
    Hidden (beforeSigning P) a := by
  cases a with
  | inl x => exact hiddenBefore_inl x
  | inr r => exact False.elim h

theorem none_of_not_hits_hidden (hP : P.Hyp) (c : Cache) (ξ : Record P)
    (hh : ¬ Cache.Hits c (hiddenCache (beforeSigning P) ξ)) (a : Loc P)
    (ha : Hidden (beforeSigning P) a) {q : Query} (hq : ξ.query a = q) : c q = none := by
  rcases hdq : c q with _ | u
  · rfl
  · refine (hh ⟨q, ?_, ?_⟩).elim
    · exact (hiddenCache_isSome_iff hP _ ξ q).mpr ⟨a, ha, hq⟩
    · simp only [hdq, Option.isSome_some]

/-- If a cache neither hit a hidden point of `ξ` nor a second-preimage target of `ξ` before
signing, adding the points exposed at any cut creates no cut-target hit. -/
theorem no_cutTargets_initial (hP : P.Hyp) (d₁ : Cut) (ξ : Record P) (c : Cache)
    (hc : ¬ Cache.Hits c (hiddenCache (beforeSigning P) ξ))
    (ht : ¬ TargetHit (secondPreimageTargets P ξ) c) :
    ¬ TargetHit (cutTargets P d₁ ξ) (Cache.extend c (exposedCache d₁ ξ)) := by
  rintro ⟨q, u, hq, hu⟩
  obtain ⟨a, hl, hmem, hcase⟩ := mem_cutTargets hu
  rcases hdq : c q with _ | u'
  · rw [Cache.extend_apply_of_none hdq] at hq
    obtain ⟨b, hb, hbq, -⟩ := (exposedCache_some_iff hP _ ξ q u).mp hq
    have hba : b = a := Option.some.inj ((hbq ▸ queryLocation_query hP ξ b).symm.trans hl)
    subst hba
    rcases hcase with ⟨-, hne⟩ | ⟨hH, -⟩
    · exact hne hbq
    · exact hb hH
  · rw [Cache.extend_apply_of_some hdq] at hq
    have hdu : c q = some u := hdq.trans hq
    rcases hcase with ⟨-, hne⟩ | ⟨hH, -⟩
    · exact ht ⟨q, u, hdu, by rw [secondPreimageTargets_of_ne hl hne]; exact hmem⟩
    · by_cases hqa : ξ.query a = q
      · exact hc ⟨q, (hiddenCache_isSome_iff hP _ ξ q).mpr
          ⟨a, hiddenBefore_of_hidden hH, hqa⟩, by simp only [hdu, Option.isSome_some]⟩
      · exact ht ⟨q, u, hdu, by rw [secondPreimageTargets_of_ne hl hqa]; exact hmem⟩

/-- The targets of a non-location query are empty. -/
theorem targets_of_not_loc {q : Query} (hq : ∀ a : RawInput P, a.query ≠ q)
    (d : Cut) (ζ : Record P) :
    cutTargets P d ζ q = ∅ ∧ secondPreimageTargets P ζ q = ∅ :=
  ⟨cutTargets_of_none d ζ (queryLocation_eq_none hq),
    secondPreimageTargets_of_none (queryLocation_eq_none hq)⟩

/-! ## Hidden-hit potentials -/

/-- Weighted hidden hits of the records of `T`. -/
def hiddenHitPotential (d : Cut) (T : Finset (Record P)) (c : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ T, recW P * ind (Cache.Hits c (hiddenCache d ξ))

theorem hiddenHitPotential_cacheQuery (d : Cut) (T : Finset (Record P)) (c : Cache) (q : Query)
    (u : BitVec hashBits) :
    hiddenHitPotential d T (c.cacheQuery q u) ≤ hiddenHitPotential d T c +
      ∑ ξ ∈ T, recW P * ind ((hiddenCache d ξ q).isSome) := by
  unfold hiddenHitPotential
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [← mul_add, Cache.hits_cacheQuery]
  exact mul_le_mul' le_rfl (ind_or_le _ _)

theorem hiddenHit_increment_le (hP : P.Hyp) {d : Cut} (hd : ValidCut P d) (v : PublicData P)
    (T : Finset (Record P)) (hT : T ⊆ publicFiber d v) (q : Query) :
    ∑ ξ ∈ T, recW P * ind ((hiddenCache d ξ q).isSome) ≤
      rate * sumW P (publicFiber d v) * queryCost (.inr q) := by
  calc ∑ ξ ∈ T, recW P * ind ((hiddenCache d ξ q).isSome)
      ≤ ∑ ξ ∈ publicFiber d v, recW P * ind ((hiddenCache d ξ q).isSome) :=
        Finset.sum_le_sum_of_subset hT
    _ = ∑ ξ ∈ publicFiber d v, if (hiddenCache d ξ q).isSome then recW P else 0 := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        by_cases h : (hiddenCache d ξ q).isSome
        · rw [ind_of h, mul_one, if_pos h]
        · rw [ind_not h, mul_zero, if_neg h]
    _ ≤ rate * queryCost (.inr q) * ∑ _ξ ∈ publicFiber d v, recW P :=
        hidden_input_charge hP d hd v q (recW P)
    _ = _ := by rw [sumW, mul_right_comm]

theorem hiddenHit_increment_zero (hP : P.Hyp) (d : Cut) (T : Finset (Record P)) (q : Query)
    (hq : ∀ (ζ : Record P) (a : Loc P), ζ.query a ≠ q) :
    ∑ ξ ∈ T, recW P * ind ((hiddenCache d ξ q).isSome) = 0 :=
  Finset.sum_eq_zero fun ξ _ => by
    rw [hiddenCache_of_not_loc hP d ξ q hq, ind_not (by simp), mul_zero]

theorem hiddenHitPotential_zero (d : Cut) (T : Finset (Record P)) (c : Cache)
    (hc : ∀ ξ ∈ T, Cache.Disjoint c (hiddenCache d ξ)) : hiddenHitPotential d T c = 0 := by
  unfold hiddenHitPotential
  exact Finset.sum_eq_zero fun ξ hξ => by rw [ind_not (hc ξ hξ).not_hits, mul_zero]

/-- The weighted average of a bounded increment over one fresh uniform answer. -/
theorem avg_le_of_le (f : BitVec hashBits → ℝ≥0∞) (a : ℝ≥0∞) (h : ∀ u, f u ≤ a) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f u ≤ a := by
  calc ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f u
      ≤ ∑ _u : BitVec hashBits, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * a :=
        Finset.sum_le_sum fun u _ => mul_le_mul' le_rfl (h u)
    _ = a := sum_inv_card_mul a

end OptimalOTS.LeanIsaBaseline.Layer.Fusion
