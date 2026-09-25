import Submissions.UpperLeanIsa.Exposure
import Submissions.UpperLeanIsa.Master

/-!
# Second-preimage targets and hidden-hit potentials

* `TargetHit targets c`: some cached answer lies in the target set of its query. A fresh query
  hits its targets with probability `|targets q| / 2 ^ 256` (`target_charge`).
* `matchingAnswers ξ a`: the answers matching the honest answer at location `a` (the step's
  slice `P.slice k j` at chain steps, the low half at root calls): at most `2 ^ 128` of them,
  i.e. `2 ^ -129` per compression.
* `secondPreimageTargets ξ`: before signing, a matching answer through a different input at any
  location. `cutTargets d ζ`: at cut `d`, a matching answer through a different input at an
  exposed location, or any answer whose slice is the public word at the boundary step just
  below the cut. Both add the `extraTargets`: an answer whose low half is the public key at
  every 896-bit non-index query other than the last root call (a candidate last call, whose
  metadata is not a constant), and an answer whose low half is the index metadata at every
  query shaped like root call 6 (so the last call is never an index query). Both depend only on
  public data and cost at most `3 · 2 ^ -129` per compression; neither has a target at an index
  query.
* `Record.Good`: the record is separated and no keygen answer other than the last root call has
  the public key as its low half; then the exposed points hit no target.
* `hiddenHitPotential d T c`: the weight of the records of `T` whose hidden points `c` hits;
  it grows by at most `rate · sumW (fiber) · cost` per query, and not at all at a query that is
  not a chain step of any record.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

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
  Finset.univ.filter fun w => P.slice k j w = P.slice k j v

theorem mem_sliceAnswers {k : Fin numChains} {j : ℕ} {u v : BitVec hashBits} :
    u ∈ sliceAnswers (P := P) k j v ↔ P.slice k j u = P.slice k j v := by
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

theorem matchingAnswers_inr (ξ : Record P) (r : Fin 8) :
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

/-- The answers whose low half is `w`. -/
def lowOf (w : Word) : Finset (BitVec hashBits) :=
  Finset.univ.filter fun u => u.extractLsb' 0 128 = w

theorem mem_lowOf {u : BitVec hashBits} {w : Word} : u ∈ lowOf w ↔ u.extractLsb' 0 128 = w := by
  unfold lowOf
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem lowOf_card (w : Word) : (lowOf w).card ≤ 2 ^ 128 := card_low_le w

/-- The charge of a target set of at most `3 · 2 ^ 128` answers at an 896-bit query. -/
theorem card_charge3 {q : Query} (hw : q.1 = 896) (S : Finset (BitVec hashBits))
    (hS : S.card ≤ 3 * 2 ^ 128) :
    (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * S.card ≤ 3 * (rate * queryCost (.inr q)) := by
  rw [queryCost_896 hw, Nat.cast_ofNat]
  have h : (S.card : ℝ≥0∞) ≤ 3 * ((2 ^ 128 : ℕ) : ℝ≥0∞) := by exact_mod_cast hS
  calc (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * S.card
      ≤ (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (3 * ((2 ^ 128 : ℕ) : ℝ≥0∞)) :=
        mul_le_mul' le_rfl h
    _ = 3 * ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (2 ^ 128 : ℕ)) := by ring
    _ = 3 * (rate * 2) := by rw [inv_card_mul_two_pow_128]

attribute [local irreducible] hashBits matchingAnswers Record.query queryLocation

/-! ## Good records and the extra targets -/

/-- No keygen answer other than the last root call has the public key as its low half. -/
def Record.PkFresh (ξ : Record P) : Prop :=
  ∀ a : Loc P, a ≠ .inr 7 → (ξ.2 a).extractLsb' 0 128 ≠ ξ.pk

/-- A good record: separated, with a fresh public key. -/
def Record.Good (ξ : Record P) : Prop := ξ.Sep ∧ ξ.PkFresh

variable (P) in
/-- The candidate last root calls: every 896-bit non-index query other than the honest one. -/
def PkCand (ζ : Record P) (q : Query) : Prop :=
  q.1 = 896 ∧ ¬ IsIdxQuery P q ∧ q ≠ ζ.query (.inr 7)

variable (P) in
/-- The extra targets: the public key at a candidate last call, the index metadata at a query of
the shape of root call 6. -/
def extraTargets (ζ : Record P) (q : Query) : Finset (BitVec hashBits) :=
  (if PkCand P ζ q then lowOf ζ.pk else ∅) ∪
    (if queryLocation P q = some (.inr 6) then lowOf P.idxMd else ∅)

theorem extraTargets_card (ζ : Record P) (q : Query) :
    (extraTargets P ζ q).card ≤ 2 * 2 ^ 128 := by
  unfold extraTargets
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (if PkCand P ζ q then lowOf ζ.pk else ∅).card ≤ 2 ^ 128 := by
    split_ifs
    · exact lowOf_card _
    · simp
  have h2 : (if queryLocation P q = some (.inr 6) then lowOf P.idxMd else ∅).card ≤ 2 ^ 128 := by
    split_ifs
    · exact lowOf_card _
    · simp
  omega

theorem extraTargets_width {ζ : Record P} {q : Query} {u : BitVec hashBits}
    (hu : u ∈ extraTargets P ζ q) : q.1 = 896 := by
  unfold extraTargets at hu
  rw [Finset.mem_union] at hu
  rcases hu with hu | hu
  · split_ifs at hu with h
    · exact h.1
    · exact absurd hu (Finset.notMem_empty _)
  · split_ifs at hu with h
    · exact queryLocation_some_width h
    · exact absurd hu (Finset.notMem_empty _)

theorem extraTargets_idx (hP : P.Hyp) (ζ : Record P) {q : Query} (hq : IsIdxQuery P q) :
    extraTargets P ζ q = ∅ := by
  unfold extraTargets
  have h1 : ¬ PkCand P ζ q := fun h => h.2.1 hq
  have h2 : queryLocation P q ≠ some (.inr 6) := by
    intro hl
    obtain ⟨m, η, pk, rfl⟩ := hq
    exact not_idx_of_queryLocation hP hl m η pk rfl
  rw [if_neg h1, if_neg h2, Finset.empty_union]

theorem mem_extraTargets_pk {ζ : Record P} {q : Query} (hq : PkCand P ζ q)
    {u : BitVec hashBits} (hu : u.extractLsb' 0 128 = ζ.pk) : u ∈ extraTargets P ζ q := by
  unfold extraTargets
  rw [Finset.mem_union, if_pos hq]
  exact Or.inl (mem_lowOf.mpr hu)

theorem mem_extraTargets_idx {ζ : Record P} {q : Query} (hq : queryLocation P q = some (.inr 6))
    {u : BitVec hashBits} (hu : u.extractLsb' 0 128 = P.idxMd) : u ∈ extraTargets P ζ q := by
  unfold extraTargets
  rw [Finset.mem_union, if_pos hq]
  exact Or.inr (mem_lowOf.mpr hu)

/-- The honest exposed points of a good record hit no extra target. -/
theorem not_mem_extraTargets_honest (hP : P.Hyp) {ζ : Record P} (hζ : ζ.Good) (a : Loc P) :
    ζ.2 a ∉ extraTargets P ζ (ζ.query a) := by
  unfold extraTargets
  rw [Finset.mem_union]
  rintro (h | h)
  · split_ifs at h with hc
    · have ha : a ≠ .inr 7 := by
        rintro rfl
        exact hc.2.2 rfl
      exact hζ.2 a ha (mem_lowOf.mp h)
    · exact Finset.notMem_empty _ h
  · split_ifs at h with hl
    · have ha : a = .inr 6 := Option.some.inj
        ((queryLocation_query hP ζ a (Record.validAt_of_sep hζ.1 a)).symm.trans hl)
      subst ha
      exact hζ.1 (Or.inr (Or.inl (mem_lowOf.mp h)))
    · exact Finset.notMem_empty _ h

/-- The extra targets depend only on the public key and the honest last call. -/
theorem extraTargets_congr {ξ ζ : Record P} (hpk : ξ.pk = ζ.pk)
    (h7 : ξ.query (.inr 7) = ζ.query (.inr 7)) : extraTargets P ξ = extraTargets P ζ := by
  funext q
  unfold extraTargets PkCand
  rw [hpk, h7]

/-! ## Targets before signing -/

variable (P) in
/-- Before signing: a matching answer through an input other than the honest one, at any
location of `ξ`, and the extra targets. -/
def secondPreimageTargets (ξ : Record P) (q : Query) : Finset (BitVec hashBits) :=
  (match queryLocation P q with
    | none => ∅
    | some a => if ξ.query a = q then ∅ else matchingAnswers ξ a) ∪ extraTargets P ξ q

theorem secondPreimageTargets_of_ne {ζ : Record P} {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) (hne : ζ.query a ≠ q) {u : BitVec hashBits}
    (hu : u ∈ matchingAnswers ζ a) : u ∈ secondPreimageTargets P ζ q := by
  unfold secondPreimageTargets
  rw [Finset.mem_union]
  left
  simp only [hl]
  rw [if_neg hne]
  exact hu

theorem secondPreimageTargets_extra {ζ : Record P} {q : Query} {u : BitVec hashBits}
    (hu : u ∈ extraTargets P ζ q) : u ∈ secondPreimageTargets P ζ q := by
  unfold secondPreimageTargets
  rw [Finset.mem_union]
  exact Or.inr hu

theorem secondPreimageTargets_query (hP : P.Hyp) (ξ : Record P) (a : Loc P) (ha : ξ.ValidAt a)
    {u : BitVec hashBits} (hu : u ∈ secondPreimageTargets P ξ (ξ.query a)) :
    u ∈ extraTargets P ξ (ξ.query a) := by
  unfold secondPreimageTargets at hu
  rw [Finset.mem_union, queryLocation_query hP ξ a ha] at hu
  rcases hu with hu | hu
  · simp only [if_pos rfl] at hu
    exact absurd hu (Finset.notMem_empty _)
  · exact hu

theorem secondPreimage_charge (ξ : Record P) (q : Query) :
    (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * (secondPreimageTargets P ξ q).card ≤
      3 * (rate * queryCost (.inr q)) := by
  by_cases hw : q.1 = 896
  · refine card_charge3 hw _ ?_
    unfold secondPreimageTargets
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : (match queryLocation P q with
        | none => ∅
        | some a => if ξ.query a = q then ∅ else matchingAnswers ξ a).card ≤ 2 ^ 128 := by
      split
      · simp
      · split_ifs
        · simp
        · exact matchingAnswers_card ξ _
    have h2 := extraTargets_card ξ q
    omega
  · have he : secondPreimageTargets P ξ q = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      unfold secondPreimageTargets at hu
      rw [Finset.mem_union] at hu
      rcases hu with hu | hu
      · split at hu
        · exact Finset.notMem_empty _ hu
        · rename_i a hl
          exact hw (queryLocation_some_width hl)
      · exact hw (extraTargets_width hu)
    rw [he, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact bot_le

/-! ## Targets at a cut -/

/-- The chain step just below the cut: its answer's slice is the public word at the cut. -/
def Boundary (d : Cut) : Loc P → Prop
  | .inl a => a.2.val + 1 = d a.1
  | .inr _ => False

variable (P) in
/-- The matching part of the cut targets. -/
def cutMatch (d : Cut) (ζ : Record P) (q : Query) : Finset (BitVec hashBits) :=
  match queryLocation P q with
  | none => ∅
  | some a =>
    if Hidden d a then (if Boundary d a then matchingAnswers ζ a else ∅)
    else (if ζ.query a = q then ∅ else matchingAnswers ζ a)

variable (P) in
/-- At cut `d`: a matching answer through a different input at an exposed location, or any
answer matching the public word at the boundary step, and the extra targets. -/
def cutTargets (d : Cut) (ζ : Record P) (q : Query) : Finset (BitVec hashBits) :=
  cutMatch P d ζ q ∪ extraTargets P ζ q

theorem cutMatch_of_location (d : Cut) (ζ : Record P) {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) :
    cutMatch P d ζ q =
      if Hidden d a then (if Boundary d a then matchingAnswers ζ a else ∅)
      else (if ζ.query a = q then ∅ else matchingAnswers ζ a) := by
  simp only [cutMatch, hl]

theorem mem_cutTargets_exposed {d : Cut} {ζ : Record P} {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) (ha : ¬ Hidden d a) (hq : ζ.query a ≠ q)
    {u : BitVec hashBits} (hu : u ∈ matchingAnswers ζ a) : u ∈ cutTargets P d ζ q := by
  unfold cutTargets
  rw [Finset.mem_union, cutMatch_of_location d ζ hl, if_neg ha, if_neg hq]
  exact Or.inl hu

theorem mem_cutTargets_boundary {d : Cut} {ζ : Record P} {q : Query} {a : Loc P}
    (hl : queryLocation P q = some a) (ha : Hidden d a) (hb : Boundary d a)
    {u : BitVec hashBits} (hu : u ∈ matchingAnswers ζ a) : u ∈ cutTargets P d ζ q := by
  unfold cutTargets
  rw [Finset.mem_union, cutMatch_of_location d ζ hl, if_pos ha, if_pos hb]
  exact Or.inl hu

theorem mem_cutTargets_extra {d : Cut} {ζ : Record P} {q : Query} {u : BitVec hashBits}
    (hu : u ∈ extraTargets P ζ q) : u ∈ cutTargets P d ζ q := by
  unfold cutTargets
  rw [Finset.mem_union]
  exact Or.inr hu

theorem mem_cutMatch {d : Cut} {ζ : Record P} {q : Query} {u : BitVec hashBits}
    (hu : u ∈ cutMatch P d ζ q) :
    ∃ a, queryLocation P q = some a ∧ u ∈ matchingAnswers ζ a ∧
      ((¬ Hidden d a ∧ ζ.query a ≠ q) ∨ (Hidden d a ∧ Boundary d a)) := by
  rcases hl : queryLocation P q with _ | a
  · simp only [cutMatch, hl] at hu
    exact absurd hu (Finset.notMem_empty u)
  · rw [cutMatch_of_location d ζ hl] at hu
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
      3 * (rate * queryCost (.inr q)) := by
  by_cases hw : q.1 = 896
  · refine card_charge3 hw _ ?_
    unfold cutTargets
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : (cutMatch P d ζ q).card ≤ 2 ^ 128 := by
      cases hl : queryLocation P q with
      | none => simp [cutMatch, hl]
      | some a =>
        rw [cutMatch_of_location d ζ hl]
        split_ifs
        · exact matchingAnswers_card ζ a
        · simp
        · simp
        · exact matchingAnswers_card ζ a
    have h2 := extraTargets_card ζ q
    omega
  · have he : cutTargets P d ζ q = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      unfold cutTargets at hu
      rw [Finset.mem_union] at hu
      rcases hu with hu | hu
      · obtain ⟨a, hl, -, -⟩ := mem_cutMatch hu
        exact hw (queryLocation_some_width hl)
      · exact hw (extraTargets_width hu)
    rw [he, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact bot_le

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
  unfold cutTargets
  rw [extraTargets_congr (data_pk_eq d ξ ζ h)
    (exposed_query_eq hd ξ ζ h _ (not_hidden_inr d 7))]
  congr 1
  cases hl : queryLocation P q with
  | none => simp only [cutMatch, hl]
  | some a =>
    rw [cutMatch_of_location d ξ hl, cutMatch_of_location d ζ hl]
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
  show a.2.val < P.len a.1 - 1
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

/-- If a cache neither hit a hidden point of a good `ξ` nor a second-preimage target of `ξ` before
signing, adding the points exposed at any cut creates no cut-target hit. -/
theorem no_cutTargets_initial (hP : P.Hyp) (d₁ : Cut) (ξ : Record P) (hξ : ξ.Good) (c : Cache)
    (hc : ¬ Cache.Hits c (hiddenCache (beforeSigning P) ξ))
    (ht : ¬ TargetHit (secondPreimageTargets P ξ) c) :
    ¬ TargetHit (cutTargets P d₁ ξ) (Cache.extend c (exposedCache d₁ ξ)) := by
  rintro ⟨q, u, hq, hu⟩
  unfold cutTargets at hu
  rw [Finset.mem_union] at hu
  rcases hdq : c q with _ | u'
  · rw [Cache.extend_apply_of_none hdq] at hq
    obtain ⟨b, hb, hv, hbq, hbu⟩ := (exposedCache_some_iff hP _ ξ q u).mp hq
    rcases hu with hu | hu
    · obtain ⟨a, hl, -, hcase⟩ := mem_cutMatch hu
      have hba : b = a := Option.some.inj ((hbq ▸ queryLocation_query hP ξ b hv).symm.trans hl)
      subst hba
      rcases hcase with ⟨-, hne⟩ | ⟨hH, -⟩
      · exact hne hbq
      · exact hb hH
    · subst hbq hbu
      exact not_mem_extraTargets_honest hP hξ b hu
  · rw [Cache.extend_apply_of_some hdq] at hq
    have hdu : c q = some u := hdq.trans hq
    rcases hu with hu | hu
    · obtain ⟨a, hl, hmem, hcase⟩ := mem_cutMatch hu
      rcases hcase with ⟨-, hne⟩ | ⟨hH, -⟩
      · exact ht ⟨q, u, hdu, secondPreimageTargets_of_ne hl hne hmem⟩
      · by_cases hqa : ξ.query a = q
        · exact hc ⟨q, (hiddenCache_isSome_iff hP _ ξ q).mpr
            ⟨a, hiddenBefore_of_hidden hH, hqa⟩, by simp only [hdu, Option.isSome_some]⟩
        · exact ht ⟨q, u, hdu, secondPreimageTargets_of_ne hl hqa hmem⟩
    · exact ht ⟨q, u, hdu, secondPreimageTargets_extra hu⟩

/-- The targets of an index query are empty. -/
theorem targets_of_idx (hP : P.Hyp) {q : Query} (hq : IsIdxQuery P q) (d : Cut) (ζ : Record P) :
    cutTargets P d ζ q = ∅ ∧ secondPreimageTargets P ζ q = ∅ := by
  have hl : queryLocation P q = none := by
    rcases h : queryLocation P q with _ | a
    · rfl
    · obtain ⟨m, η, pk, rfl⟩ := hq
      exact absurd rfl (not_idx_of_queryLocation hP h m η pk)
  unfold cutTargets secondPreimageTargets cutMatch
  simp only [hl, extraTargets_idx hP ζ hq, Finset.union_empty, and_self]

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

end OptimalOTS.LeanIsaBaseline.Layer
