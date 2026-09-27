import Submissions.UpperCompressions.LongChain91Empirical
import Submissions.UpperCompressions.LongChain91Auth

/-!
# Actual cached-row bounds for the chain-18 schedule

This file connects the concrete 160-tier empirical kernel to the physical
86-bit signing row.  The public cache is retained exactly: its known row
entries contribute the replay hazard, while every unqueried 342-bit input is
completed by one shared uniform table.  The table exception remains explicit
until it is averaged over the preceding adaptive computation.
-/

noncomputable section

namespace OptimalOTS.WeightedConstruction.LongChain91CachedRow

open OracleSpec OracleComp OracleComp.EvalDist
open WeightedReplacement WeightedCompletion WeightedCacheCounts
open scoped Classical BigOperators ENNReal

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

attribute [local irreducible] Finset.univ Finset.filter

abbrev M := LongChain91Security.M
abbrev decode : BitVec hashBits → Option (Fin M) :=
  LongChain91Empirical.cacheDecode
abbrev tier : Fin M → ℕ := LongChain91Empirical.rank
abbrev classProbability := LongChain91Security.classProbability
abbrev referenceWeight := LongChain91Security.referenceWeight
abbrev securityWeights := LongChain91Security.securityWeights
abbrev excess := LongChain91Security.excess

/-! ## The observed part of one signing row -/

def exposed (m : Message) (c : Cache) : Finset (BitVec 86) :=
  Finset.univ.filter (fun η => (c (WideForest.encQuery (m, η))).isSome)

def fixed (m : Message) (c : Cache) (η : BitVec 86) : Option (Fin M) :=
  (c (WideForest.encQuery (m, η))).bind decode

theorem row_injective (m : Message) :
    Function.Injective (fun η : BitVec 86 => WideForest.encQuery (m, η)) :=
  fun _ _ h => WeightedSampling.Availability.nonce_query_inj m h

theorem exposed_card (m : Message) (c : Cache) :
    (exposed m c).card =
      (seen (WideDomains.rowDomain m) c).card :=
  (WeightedCacheCounts.seen_image_card _ (row_injective m) c).symm

theorem fixed_counts (m : Message) (c : Cache) :
    rowCount (exposed m c) (fixed m c) =
      classCounts (WideDomains.rowDomain m) c decode :=
  (WeightedCacheCounts.counts_image _ (row_injective m) c decode).symm

theorem cached_known (m : Message) (c : Cache)
    (g : BitVec 342 → BitVec hashBits) (η : BitVec 86)
    (hη : η ∈ exposed m c) :
    decode (cachedRow 86 m c g η) = fixed m c η := by
  have hc : (c (WideForest.encQuery (m, η))).isSome :=
    (Finset.mem_filter.mp hη).2
  cases hh : c (WideForest.encQuery (m, η)) with
  | none => simp [hh] at hc
  | some y =>
      change decode ((c (WideForest.encQuery (m, η))).getD _) =
        (c (WideForest.encQuery (m, η))).bind decode
      rw [hh]
      rfl

theorem cached_fresh (m : Message) (c : Cache)
    (g : BitVec 342 → BitVec hashBits) (η : BitVec 86)
    (hη : η ∉ exposed m c) :
    decode (cachedRow 86 m c g η) = decode (g (m ++ η)) := by
  have hc : c (WideForest.encQuery (m, η)) = none := by
    cases hh : c (WideForest.encQuery (m, η)) with
    | none => rfl
    | some y =>
        exact False.elim
          (hη (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hh]⟩))
  change decode ((c (WideForest.encQuery (m, η))).getD _) = _
  rw [hc]
  rfl

theorem cached_fresh_probability (m : Message) (c : Cache)
    (η : BitVec 86) (hη : η ∉ exposed m c) (i : Fin M) :
    uniformMean (fun g : BitVec 342 → BitVec hashBits =>
      if decode (cachedRow 86 m c g η) = some i then 1 else 0) =
        classProbability i := by
  simp only [cached_fresh m c _ η hη]
  exact (uniformMean_coordinate (W := BitVec hashBits) (m ++ η)
    (fun x => if decode x = some i then 1 else 0)).trans
      (LongChain91Empirical.uniform_decode_probability i)

theorem tableKernel_nonneg {D I : Type} [Fintype D] [Nonempty D]
    [DecidableEq D] [Fintype I] [DecidableEq I]
    (k : ℕ) (table : D → Option I) (rank : I → ℕ)
    (f : D → I → ℝ) (hf : ∀ a i, 0 ≤ f a i) :
    0 ≤ tableKernel k table rank f := by
  rw [← iid_selected_score]
  apply iidMean_nonneg
  intro xs
  cases hs : selected table rank xs with
  | none => simp [score, hs]
  | some p => simpa [score, hs] using hf p.1 p.2

/-- Exact payoff of the concrete all-`L` selector from an arbitrary cache. -/
theorem actual_sign_payoff (m : Message) (c : Cache)
    (f : BitVec 86 → Fin M → ℝ) (hf : ∀ a i, 0 ≤ f a i) :
    outE (WeightedSampling.loop 86 decode tier m Chain18Compact.L) c
      (fun s => ENNReal.ofReal (score s (fun r => f r.1 r.2))) =
      ENNReal.ofReal (uniformMean (fun g : BitVec 342 → BitVec hashBits =>
        tableKernel Chain18Compact.L (decode ∘ cachedRow 86 m c g) tier f)) := by
  rw [outE_index342_preload]
  have he (g : BitVec 342 → BitVec hashBits) :
      outE (WeightedSampling.loop 86 decode tier m Chain18Compact.L)
          ((lengthSlice 342).preload c g)
          (fun s => ENNReal.ofReal (score s (fun r => f r.1 r.2))) =
        ENNReal.ofReal
          (tableKernel Chain18Compact.L (decode ∘ cachedRow 86 m c g) tier f) :=
    E_loop_fixed_row_score 86 M Chain18Compact.L decode tier m
      (cachedRow 86 m c g) ((lengthSlice 342).preload c g)
      (length_preload_row 86 m c g) f hf
  calc
    _ = E ($ᵗ (BitVec 342 → BitVec hashBits)) (fun g => ENNReal.ofReal
        (tableKernel Chain18Compact.L (decode ∘ cachedRow 86 m c g) tier f)) := by
      congr 1
      funext g
      exact he g
    _ = _ := E_uniform_ofReal _
      (fun g => tableKernel_nonneg Chain18Compact.L _ tier f hf)

/-! ## Row-local table exception and replay payoff -/

def tableFailure (m : Message) (c : Cache) : ℝ :=
  uniformMean (fun g : BitVec 342 → BitVec hashBits =>
    if LongChain91Empirical.rowGood
      (decode ∘ cachedRow 86 m c g) then 0 else 1)

def replayScore (m : Message) (c : Cache) (η : BitVec 86) (i : Fin M) : ℝ :=
  if η ∈ exposed m c then
    (if 2 ≤ classCounts WideDomains.indexDomain c decode i then 1 else 0)
  else
    (if classCounts WideDomains.indexDomain c decode i = 0 then 0 else 1)

theorem replayScore_nonneg (m : Message) (c : Cache)
    (η : BitVec 86) (i : Fin M) : 0 ≤ replayScore m c η i := by
  unfold replayScore
  split_ifs <;> norm_num

theorem actual_replay_bound (m : Message) (c : Cache) :
    outE (WeightedSampling.loop 86 decode tier m Chain18Compact.L) c
      (fun s => ENNReal.ofReal
        (score s (fun r => replayScore m c r.1 r.2))) ≤
      ENNReal.ofReal ((99 : ℝ) / 98 * securityWeights.hazard ((2 : ℝ)^86)
        (seen (WideDomains.rowDomain m) c).card
        (classCounts WideDomains.indexDomain c decode)
        (classCounts (WideDomains.rowDomain m) c decode) + tableFailure m c) := by
  rw [actual_sign_payoff m c _ (replayScore_nonneg m c)]
  apply ENNReal.ofReal_le_ofReal
  have h := replay_kernel_bound securityWeights Chain18Compact.L tier
    (exposed m c) (fixed m c)
    (fun g : BitVec 342 → BitVec hashBits => decode ∘ cachedRow 86 m c g)
    (classCounts WideDomains.indexDomain c decode)
    (cached_known m c) (cached_fresh_probability m c)
    (fun g => LongChain91Empirical.rowGood
      (decode ∘ cachedRow 86 m c g))
    ((99 : ℝ) / 98) (tableFailure m c) (by norm_num)
    (fun g hg i => LongChain91Empirical.rowGood_kernel _ hg i) le_rfl
  rw [exposed_card, fixed_counts, Fintype.card_bitVec,
    Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-! ## Literal post-sign excess -/

theorem excess_le_one (i : Fin M) : excess i ≤ 1 := by
  have hs : (∑ j : Fin M, classProbability j) < 1 :=
    LongChain91Security.classProbability_sum_lt_one
  have hp : classProbability i ≤ ∑ j : Fin M, classProbability j :=
    Finset.single_le_sum
      (fun j _ => (LongChain91Security.classProbability_pos j).le)
      (Finset.mem_univ i)
  have hr : classProbability i /
      (1 - ∑ j : Fin M, classProbability j) ≤ 1 := by
    apply (div_le_iff₀ (sub_pos.mpr hs)).2
    have ha : (∑ j : Fin M, classProbability j) < 1 / 10000 := by
      rw [LongChain91Security.classProbability_sum]
      exact LongChain91Security.accepted_fraction_lt
    linarith
  exact (LongChain91Empirical.excess_le_probability_ratio i).trans hr

theorem excess_score_identity (r : Fin M → ℕ) :
    (∑ i : Fin M, (r i : ℝ) *
      (referenceWeight i / classProbability i * excess i)) =
      LongChain91Empirical.excessWeights.score r := by
  unfold WeightedRow.Weights.score
  apply Finset.sum_congr rfl
  intro i hi
  change (r i : ℝ) * (referenceWeight i / classProbability i * excess i) =
    (r i : ℝ) * (referenceWeight i * excess i / classProbability i)
  ring

/-- The empirical excess coordinate gives the sharp `47/100 + 1/1000`
conditional-completion bound used after signing. -/
theorem good_excess_payoff (c : Cache) (hc : LongChain91Empirical.Good c)
    (m : Message) :
    (1 - ((seen (WideDomains.rowDomain m) c).card : ℝ) / (2 : ℝ)^86) *
        (∑ i : Fin M, referenceWeight i * excess i) +
      LongChain91Empirical.excessWeights.score
        (classCounts (WideDomains.rowDomain m) c decode) / (2 : ℝ)^86 ≤
        ((471 : ℝ) / 1000) * Chain18Compact.kappa := by
  have hs := LongChain91Empirical.good_row_excess c hc m
  have hn : (0 : ℝ) < 2^86 := by positivity
  have hd := (div_le_div_iff_of_pos_right hn).mpr hs
  have hm := LongChain91Security.postSignExcess_lt
  unfold LongChain91Security.postSignExcess at hm
  have he :
      (1 - ((seen (WideDomains.rowDomain m) c).card : ℝ) / (2 : ℝ)^86) *
          (∑ i : Fin M, referenceWeight i * excess i) +
        (((∑ i : Fin M, referenceWeight i * excess i) *
            (seen (WideDomains.rowDomain m) c).card +
          Chain18Compact.kappa * (2 : ℝ)^86 / 1000) / (2 : ℝ)^86) =
        (∑ i : Fin M, referenceWeight i * excess i) +
          Chain18Compact.kappa / 1000 := by
    ring
  calc
    _ ≤ (1 - ((seen (WideDomains.rowDomain m) c).card : ℝ) / (2 : ℝ)^86) *
          (∑ i : Fin M, referenceWeight i * excess i) +
        (((∑ i : Fin M, referenceWeight i * excess i) *
            (seen (WideDomains.rowDomain m) c).card +
          Chain18Compact.kappa * (2 : ℝ)^86 / 1000) / (2 : ℝ)^86) :=
      add_le_add_right hd _
    _ = (∑ i : Fin M, referenceWeight i * excess i) +
        Chain18Compact.kappa / 1000 := he
    _ ≤ ((471 : ℝ) / 1000) * Chain18Compact.kappa := by
      linarith

theorem actual_excess_bound (m : Message) (c : Cache)
    (hc : LongChain91Empirical.Good c) :
    outE (WeightedSampling.loop 86 decode tier m Chain18Compact.L) c
      (fun s => ENNReal.ofReal (score s (fun r => excess r.2))) ≤
      ENNReal.ofReal ((99 : ℝ) / 98 *
        (((471 : ℝ) / 1000) * Chain18Compact.kappa) + tableFailure m c) := by
  rw [actual_sign_payoff m c (fun _ i => excess i)
    (fun _ i => LongChain91Empirical.excess_nonneg i)]
  apply ENNReal.ofReal_le_ofReal
  have h := excess_kernel_bound securityWeights Chain18Compact.L tier
    (exposed m c) (fixed m c)
    (fun g : BitVec 342 → BitVec hashBits => decode ∘ cachedRow 86 m c g)
    (cached_known m c) (cached_fresh_probability m c)
    excess LongChain91Empirical.excess_nonneg 1 zero_le_one excess_le_one
    (fun g => LongChain91Empirical.rowGood
      (decode ∘ cachedRow 86 m c g))
    ((99 : ℝ) / 98) (tableFailure m c) (by norm_num)
    (fun g hg i => LongChain91Empirical.rowGood_kernel _ hg i) le_rfl
  rw [exposed_card, fixed_counts, Fintype.card_bitVec,
    Nat.cast_pow, Nat.cast_ofNat, one_mul] at h
  change _ ≤ (99 : ℝ) / 98 *
    ((1 - ((seen (WideDomains.rowDomain m) c).card : ℝ) / (2 : ℝ)^86) *
      (∑ i : Fin M, referenceWeight i * excess i) +
      (∑ i : Fin M,
        (classCounts (WideDomains.rowDomain m) c decode i : ℝ) *
          (referenceWeight i / classProbability i * excess i)) / (2 : ℝ)^86) +
      tableFailure m c at h
  rw [excess_score_identity] at h
  have hb := mul_le_mul_of_nonneg_left (good_excess_payoff c hc m)
    (show (0 : ℝ) ≤ 99 / 98 by norm_num)
  exact h.trans (add_le_add hb le_rfl)

/-! ## Adaptive average of the row-local exception -/

theorem tableFailure_average { α : Type } (oa : OracleComp Spec α)
    (message : α → Message) (c : Cache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    E (run oa c)
      (fun out => ENNReal.ofReal (tableFailure (message out.1) out.2)) ≤
        (2 : ℝ≥0∞)⁻¹^760 := by
  convert LongChain91Empirical.actual_rowGood_completion_failure oa c
    (fun x => hf ⟨342, x⟩ rfl) message using 1
  congr 1

/-! ## A global completed-table variant

The row-local predicate above gives the accepted adaptive average directly.
The following stronger predicate records one completion table that is good for
every message.  It exposes the exact `fullTableGood_kernel` bridge for callers
that keep a global completion witness.
-/

/-! ## Cached alternate-class adapter -/

/-- The exact public-cache event used by the LongChain authentication game.
Keeping this local avoids imposing an import direction on the game module;
its planned `AlternateClass` definition is definitionally the same predicate. -/
def alternateClass (c : Cache) (signedInput : LongChain91.EncInput)
    (i : Fin M) : Prop :=
  ∃ u : LongChain91.EncInput, u ≠ signedInput ∧
    ∃ w, c (LongChain91.encQuery u) = some w ∧ decode w = some i

theorem classCount_one (c : Cache) (i : Fin M) (q : Query)
    (hq : q.1 = 342) (y : BitVec hashBits) (hc : c q = some y)
    (hi : decode y = some i) :
    1 ≤ classCounts WideDomains.indexDomain c decode i :=
  WeightedCacheEvidence.one WideDomains.indexDomain c decode i q
    ((WideDomains.mem_indexDomain q).mpr hq) y hc hi

theorem classCount_two (c : Cache) (i : Fin M) (q q' : Query)
    (hne : q ≠ q') (hq : q.1 = 342) (hq' : q'.1 = 342)
    (y y' : BitVec hashBits) (hc : c q = some y) (hc' : c q' = some y')
    (hi : decode y = some i) (hi' : decode y' = some i) :
    2 ≤ classCounts WideDomains.indexDomain c decode i :=
  WeightedCacheEvidence.two WideDomains.indexDomain c decode i q q' hne
    ((WideDomains.mem_indexDomain q).mpr hq)
    ((WideDomains.mem_indexDomain q').mpr hq') y y' hc hc' hi hi'

theorem alternate_replayScore (m : Message) (c : Cache) (η : BitVec 86)
    (i : Fin M)
    (hconsistent : ∀ y, c (LongChain91.encQuery (m, η)) = some y →
      decode y = some i)
    (h : alternateClass c (m, η) i) : replayScore m c η i = 1 := by
  obtain ⟨u, hne, y, hy, hi⟩ := h
  unfold replayScore
  by_cases hη : η ∈ exposed m c
  · rw [if_pos hη]
    have hs := (Finset.mem_filter.mp hη).2
    cases hc : c (WideForest.encQuery (m, η)) with
    | none => simp [hc] at hs
    | some z =>
        have he : LongChain91.encQuery u ≠ LongChain91.encQuery (m, η) := by
          intro heq
          exact hne (WeightedReplacement.indexInput_injective 86 heq)
        have hk := classCount_two c i (LongChain91.encQuery u)
          (LongChain91.encQuery (m, η)) he rfl rfl y z hy hc hi
          (hconsistent z hc)
        exact if_pos hk
  · rw [if_neg hη]
    have hk := classCount_one c i (LongChain91.encQuery u) rfl y hy hi
    exact if_neg (by omega)

private def optionEvent {I : Type} (P : I → Prop) : Option I → ℝ≥0∞
  | none => 0
  | some i => if P i then 1 else 0

private theorem optionEvent_le_score {I : Type} (P : I → Prop)
    (f : I → ℝ) (s : Option I)
    (h : ∀ i, s = some i → P i → f i = 1) :
    optionEvent P s ≤ ENNReal.ofReal (score s f) := by
  cases s with
  | none => exact bot_le
  | some i =>
      change (if P i then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (f i)
      by_cases hi : P i
      · rw [if_pos hi, h i rfl hi, ENNReal.ofReal_one]
      · rw [if_neg hi]
        exact bot_le

def alternatePayoff (m : Message) (c : Cache) :
    Option (WeightedSampling.Winner 86 M) → ℝ≥0∞ :=
  optionEvent (fun r => alternateClass c (m, r.1) r.2)

@[simp] theorem alternatePayoff_some (m : Message) (c : Cache)
    (η : BitVec 86) (i : Fin M) :
    alternatePayoff m c (some (η, i)) =
      (if alternateClass c (m, η) i then 1 else 0) := rfl

attribute [local irreducible] alternatePayoff replayScore optionEvent

theorem alternativePayoff_le (m : Message) (c : Cache)
    (s : Option (WeightedSampling.Winner 86 M))
    (hconsistent : ∀ (η : BitVec 86) (i : Fin M), s = some (η, i) →
      ∀ (y : BitVec hashBits), c (LongChain91.encQuery (m, η)) = some y →
        decode y = some i) :
    alternatePayoff m c s ≤ ENNReal.ofReal
      (score (I := WeightedSampling.Winner 86 M) s
        (fun r => replayScore m c r.1 r.2)) := by
  unfold alternatePayoff
  exact optionEvent_le_score
    (fun r => alternateClass c (m, r.1) r.2)
    (fun r => replayScore m c r.1 r.2) s
    (fun r hs halt => alternate_replayScore m c r.1 r.2
      (hconsistent r.1 r.2 hs) halt)

theorem actual_alternative_bound (m : Message) (c : Cache) :
    outE (WeightedSampling.loop 86 decode tier m Chain18Compact.L) c
      (alternatePayoff m c) ≤
      ENNReal.ofReal ((99 : ℝ) / 98 * securityWeights.hazard ((2 : ℝ)^86)
        (seen (WideDomains.rowDomain m) c).card
        (classCounts WideDomains.indexDomain c decode)
        (classCounts (WideDomains.rowDomain m) c decode) + tableFailure m c) := by
  apply le_trans (b := outE
    (WeightedSampling.loop 86 decode tier m Chain18Compact.L) c
    (fun s => ENNReal.ofReal
      (score s (fun r => replayScore m c r.1 r.2))))
  · apply expectedValue_mono_of_support
    intro p hp
    obtain ⟨hsub, hwin⟩ := WeightedSampling.loop_support
      86 decode tier m Chain18Compact.L c p hp
    apply alternativePayoff_le
    intro η i hs y hy
    obtain ⟨z, hz, hzi⟩ := hwin η i hs
    have he : y = z := Option.some.inj ((hsub _ _ hy).symm.trans hz)
    rw [he]
    exact hzi
  · exact actual_replay_bound m c

end OptimalOTS.WeightedConstruction.LongChain91CachedRow
