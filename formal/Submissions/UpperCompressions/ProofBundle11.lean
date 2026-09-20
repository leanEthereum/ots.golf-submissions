import Submissions.UpperCompressions.ProofBundle10
import Submissions.UpperCompressions.ProofBundle06
import Submissions.UpperCompressions.ProofBundle08
import Submissions.UpperCompressions.ProofBundle07
import Submissions.UpperCompressions.ProofBundle05
import Submissions.UpperCompressions.ProofBundle01
import Submissions.UpperCompressions.ProofBundle09

/- Original module: Submissions.UpperCompressions.ReplacementCompletionTail; SHA256 a7d0011ebea456fb3f88cd261f3e677ef015bbd63229dfa856efec343015f011. -/
section

/-! Adaptive observed-cache completions inherit the unconditional full-table
tail. No pointwise bound is asserted for a particular adversarial transcript. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical
local instance (priority := 100000) stagedLocal_ReplacementCompletionTail_1 {α : Type*} : DecidableEq α := Classical.decEq α
attribute [local irreducible] hashBits msgBits signBudget

def completedTable (b : ℕ) (c : Cache) (g : BitVec b → BitVec hashBits) :
    BitVec b → BitVec hashBits := fun x => (c ⟨b,x⟩).getD (g x)

def readTable (b : ℕ) (c : Cache) : BitVec b → BitVec hashBits :=
  fun x => (c ⟨b,x⟩).getD 0

theorem readTable_preload (b : ℕ) (c : Cache) (g : BitVec b → BitVec hashBits) :
    readTable b ((lengthSlice b).preload c g) = completedTable b c g := by
  funext x
  unfold readTable completedTable QuerySlice.preload
  rw [Cache.extend_apply, lengthSlice_inside]
  cases c ⟨b,x⟩ <;> rfl

theorem preload_complete_initial (b : ℕ) (c : Cache)
    (hc : ∀ x : BitVec b, c ⟨b,x⟩ = none) (g : BitVec b → BitVec hashBits) :
    ∀ x : BitVec b, (lengthSlice b).preload c g ⟨b,x⟩ = some (g x) := by
  intro x
  unfold QuerySlice.preload
  rw [Cache.extend_apply, hc x, lengthSlice_inside]
  rfl

theorem readTable_run_preload {α : Type} (b : ℕ) (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec b, c ⟨b,x⟩ = none)
    (g : BitVec b → BitVec hashBits) (p : α × Cache)
    (hp : p ∈ support (run oa ((lengthSlice b).preload c g))) :
    readTable b p.2 = g := by
  funext x
  have h := sub_of_mem_support_run oa _ p hp _ _ (preload_complete_initial b c hc g x)
  simp only [readTable, h, Option.getD_some]

/-- Averaging the posterior completion of the actual final public cache cannot
increase any unconditional bad-table probability. The program may be adaptive. -/
theorem completed_bad_probability_le {α : Type} (b : ℕ) (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec b, c ⟨b,x⟩ = none)
    (bad : (BitVec b → BitVec hashBits) → Prop) :
    E (run oa c) (fun p => E ($ᵗ (BitVec b → BitVec hashBits))
      (fun g => if bad (completedTable b p.2 g) then 1 else 0)) ≤
      E ($ᵗ (BitVec b → BitVec hashBits)) (fun g => if bad g then 1 else 0) := by
  have h := cacheE_finite_completion (lengthSlice b) oa c
    (fun _ d => if bad (readTable b d) then 1 else 0)
  simp only [cacheE, completePayoff, readTable_preload] at h
  rw [h]
  apply E_mono
  intro g
  calc
    _ ≤ E (run oa ((lengthSlice b).preload c g)) (fun _ => if bad g then 1 else 0) := by
      apply expectedValue_mono_of_support
      intro p hp
      rw [readTable_run_preload b oa c hc g p hp]
    _ ≤ _ := E_const_le _ _

/-- All72 prefix deficits over every message row retain the unconditional tail
after any actual adaptive public computation and its observed cache. -/
theorem completed_full_bad_probability {α : Type} (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec (msgBits+86), c ⟨msgBits+86,x⟩ = none)
    (P : Fin 72 → BitVec hashBits → Prop) :
    E (run oa c) (fun p => E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
      (fun g => if fullRowBad P (completedTable (msgBits+86) p.2 g) then 1 else 0)) ≤
        (2:ℝ≥0∞)⁻¹^761 := by
  apply (completed_bad_probability_le (msgBits+86) oa c hc (fullRowBad P)).trans
  convert full_table_bad_probability P using 1
  · rfl
  · congr 1
    funext g
    unfold fullRowBad
    split_ifs <;> rfl

/-- The message row can itself be chosen by the adaptive computation. This
bounds the average conditional completion failure, not each transcript's value. -/
theorem completed_chosen_row_bad_probability {α : Type} (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec (msgBits+86), c ⟨msgBits+86,x⟩ = none)
    (message : α → Message) (P : Fin 72 → BitVec hashBits → Prop) :
    E (run oa c) (fun p => E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
      (fun g => if ∃ j : Fin 72,
        empirical (P j) (fun η : BitVec 86 => completedTable (msgBits+86) p.2 g (message p.1 ++ η)) ≤
          fraction (P j)-1/(100*(2:ℝ)^20) then 1 else 0)) ≤ (2:ℝ≥0∞)⁻¹^761 := by
  apply (le_trans (b := E (run oa c) (fun p => E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
    (fun g => if fullRowBad P (completedTable (msgBits+86) p.2 g) then 1 else 0))))
  · apply E_mono
    intro p
    apply E_mono
    intro g
    by_cases hh : ∃ j : Fin 72,
        empirical (P j) (fun η : BitVec 86 => completedTable (msgBits+86) p.2 g (message p.1 ++ η)) ≤
          fraction (P j)-1/(100*(2:ℝ)^20)
    · have hb : fullRowBad P (completedTable (msgBits+86) p.2 g) := by
        obtain ⟨j,hj⟩ := hh
        exact ⟨(message p.1,j),hj⟩
      simp only [if_pos hh, if_pos hb]
      exact le_rfl
    · simp only [if_neg hh]
      exact bot_le
  · exact completed_full_bad_probability oa c hc P

#print axioms completed_bad_probability_le
#print axioms completed_full_bad_probability
#print axioms completed_chosen_row_bad_probability
end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.WideTableGood; SHA256 333917dda582bc2f6d79b206c6c3ddf08507ea6507fde9941f16a0495d10f1a9. -/
section

/-! Concrete full-table72-prefix event, exact first-minimum kernel envelope,
and its unconditional tail. This event is never used to recondition the oracle. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped BigOperators Classical
namespace OptimalOTS.WeightedConstruction.WeightedSchedule
open WeightedReplacement WeightedCompletion WeightedReference WeightedConstants
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes

def prefixPredicates (j : Fin 72) : BitVec 256 → Prop := prefixLe j.val

theorem empirical_eq_fraction {D : Type} [Fintype D]
    (P : BitVec 256 → Prop) (row : D → BitVec 256) :
    empirical P row = fraction (P ∘ row) := rfl

theorem fraction_le_one {D : Type} [Fintype D] [Nonempty D] (P : D → Prop) :
    fraction P ≤ 1 := by
  unfold fraction
  exact (uniformMean_mono _ (fun _ => 1) (fun _ => by split_ifs <;> norm_num)).trans_eq
    (uniformMean_const 1)

/-- The empty weak prefix costs nothing; all other weak prefixes and every
strict prefix use one of the72 concentration predicates. -/
theorem prefix_deficits_rowGood {D : Type} [Fintype D] [Nonempty D] [DecidableEq D]
    (row : D → BitVec 256)
    (hgood : ∀ j : Fin 72, fraction (prefixPredicates j)-1/(100*(L:ℝ)) <
      empirical (prefixPredicates j) row) : rowGood (decode ∘ row) := by
  intro i
  have hj : tier i ≤ 71 := by have := tier_lt i; omega
  have hw : weakRank tier i ∘ (decode ∘ row) = fun a => ¬ prefixLt (tier i) (row a) := by
    funext a
    exact congrArg (fun f => f (row a)) (weakRank_prefix i)
  have hs : strictRank tier i ∘ (decode ∘ row) = fun a => ¬ prefixLe (tier i) (row a) := by
    funext a
    exact congrArg (fun f => f (row a)) (strictRank_prefix i)
  constructor
  · by_cases h0 : tier i = 0
    · have hh := fraction_le_one (weakRank tier i ∘ (decode ∘ row))
      simp only [h0, survival, Nat.cast_zero, zero_mul, sub_zero]
      exact hh.trans (le_add_of_nonneg_right (by positivity))
    · let j : Fin 72 := ⟨tier i-1, by omega⟩
      have hp : prefixPredicates j = prefixLt (tier i) := by
        unfold prefixPredicates
        rw [prefixLe_eq]
        congr 1
        dsimp only [j]
        omega
      have hg := hgood j
      rw [hp, prefixLt_probability (tier i) hj, empirical_eq_fraction] at hg
      rw [hw, fraction_not]
      unfold survival
      change 1-fraction (prefixLt (tier i) ∘ row) ≤ _
      linarith
  · have hg := hgood ⟨tier i, tier_lt i⟩
    change fraction (prefixLe (tier i))-1/(100*(L:ℝ)) < empirical (prefixLe (tier i)) row at hg
    rw [prefixLe_probability (tier i) hj, empirical_eq_fraction] at hg
    rw [hs, fraction_not]
    change 1-fraction (prefixLe (tier i) ∘ row) ≤ _
    linarith

def fullTableGood (g : BitVec (msgBits+86) → BitVec hashBits) : Prop :=
  ¬ fullRowBad prefixPredicates g

theorem fullTableGood_row (g : BitVec (msgBits+86) → BitVec hashBits)
    (hg : fullTableGood g) (m : Message) :
    rowGood (decode ∘ (fun η : BitVec 86 => g (m ++ η))) := by
  apply prefix_deficits_rowGood
  intro j
  apply lt_of_not_ge
  intro hj
  apply hg
  refine ⟨(m,j), ?_⟩
  convert hj using 1 <;> norm_num [L]
  all_goals rfl

/-- Pointwise good-table envelope for every message row and actual decoded class. -/
theorem fullTableGood_kernel (g : BitVec (msgBits+86) → BitVec hashBits)
    (hg : fullTableGood g) (m : Message) (i : Fin M) :
    kernel L (fraction (weakRank tier i ∘ decode ∘ (fun η : BitVec 86 => g (m ++ η))))
      (fraction (strictRank tier i ∘ decode ∘ (fun η : BitVec 86 => g (m ++ η)))) ≤
        (99:ℝ)/98 * (referenceWeight i/classProbability i) :=
  rowGood_kernel _ (fullTableGood_row g hg m) i

/-- Unconditional tail across all message rows and all72 actual prefix predicates. -/
theorem fullTableGood_bad_probability :
    E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
      (fun g => if fullTableGood g then 0 else 1) ≤ (2:ℝ≥0∞)⁻¹^761 := by
  have h := full_table_bad_probability prefixPredicates
  convert h using 1
  congr 1
  funext g
  unfold fullTableGood fullRowBad
  split_ifs <;> simp_all

end OptimalOTS.WeightedConstruction.WeightedSchedule
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.fullTableGood_row
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.fullTableGood_kernel
#print axioms OptimalOTS.WeightedConstruction.WeightedSchedule.fullTableGood_bad_probability
end
end

/- Original module: Submissions.UpperCompressions.ReplacementConcreteCompletion; SHA256 df620c123d85a25d02bebf5cb6e9bd4a561c11b6a3c922cf3688468e5760792f. -/
section

/-! Concrete mixed72 row-completion failure after the actual adaptive public
prefix. This is the averaged delta term in the cached replay/excess bounds. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
open OptimalOTS.WeightedConstruction.WeightedSchedule
local instance (priority := 100000) stagedLocal_ReplacementConcreteCompletion_1 {α : Type*} : DecidableEq α := Classical.decEq α

theorem actual_rowGood_completion_failure {α : Type} (oa : OracleComp Spec α)
    (c : Cache) (hc : ∀ x : BitVec 342, c ⟨342,x⟩ = none) (message : α → Message) :
    E (run oa c) (fun p => ENNReal.ofReal (uniformMean
      (fun g : BitVec 342 → BitVec 256 =>
        if rowGood (decode ∘ cachedRow 86 (message p.1) p.2 g) then (0:ℝ) else 1))) ≤
      (2:ℝ≥0∞)⁻¹^761 := by
  apply (le_trans (b := E (run oa c) (fun p => E ($ᵗ (BitVec (msgBits+86) → BitVec hashBits))
    (fun g => if fullRowBad prefixPredicates (completedTable (msgBits+86) p.2 g) then 1 else 0))))
  · apply E_mono
    intro p
    rw [← E_uniform_ofReal
      (fun g : BitVec 342 → BitVec 256 =>
        if rowGood (decode ∘ cachedRow 86 (message p.1) p.2 g) then (0:ℝ) else 1)
      (fun g => by split_ifs <;> norm_num)]
    apply E_mono
    intro g
    by_cases hr : rowGood (decode ∘ cachedRow 86 (message p.1) p.2 g)
    · simp only [if_pos hr, ENNReal.ofReal_zero]
      exact bot_le
    · have hb : fullRowBad prefixPredicates (completedTable (msgBits+86) p.2 g) := by
        by_contra hn
        apply hr
        exact fullTableGood_row _ hn (message p.1)
      simp only [if_neg hr, ENNReal.ofReal_one, if_pos hb]
      exact le_rfl
  · exact completed_full_bad_probability oa c hc prefixPredicates

#print axioms actual_rowGood_completion_failure
end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.WideCachedPayoff; SHA256 f195e8616b43a2fca66306122ae567cfff628afd99a2da585446f85303fce524. -/
section

/-! Actual signing replay/excess bounds from the physical pre-sign cache.
The conditional table exception is explicit and is bounded only after averaging
under the actual adaptive execution. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideCachedRow
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedSchedule WideDomains WideForest WideConcentration WeightedReference WeightedConstants
open WeightedReplacement WeightedCompletion WeightedCacheCounts
open scoped Classical ENNReal
set_option maxHeartbeats 1000000
attribute [local irreducible] Finset.univ Finset.filter

def tableFailure (m : Message) (c : Cache) : ℝ :=
  uniformMean (fun g : BitVec 342 → BitVec 256 =>
    if rowGood (decode ∘ cachedRow 86 m c g) then 0 else 1)

def replayScore (m : Message) (c : Cache) (η : BitVec 86) (i : Fin M) : ℝ :=
  if η ∈ exposed m c then (if 2 ≤ classCounts indexDomain c decode i then 1 else 0)
  else (if classCounts indexDomain c decode i=0 then 0 else 1)

theorem replayScore_nonneg (m : Message) (c : Cache) (η : BitVec 86) (i : Fin M) :
    0≤replayScore m c η i := by unfold replayScore; split_ifs <;> norm_num

theorem actual_replay_bound (m : Message) (c : Cache) :
    outE (WeightedSampling.loop 86 decode tier m L) c
      (fun s => ENNReal.ofReal (score s (fun r => replayScore m c r.1 r.2))) ≤
      ENNReal.ofReal ((99:ℝ)/98*securityWeights.hazard ((2:ℝ)^86)
        (seen (rowDomain m) c).card (classCounts indexDomain c decode)
        (classCounts (rowDomain m) c decode)+tableFailure m c) := by
  rw [actual_sign_payoff m c _ (replayScore_nonneg m c)]
  apply ENNReal.ofReal_le_ofReal
  have h := replay_kernel_bound securityWeights L tier (exposed m c) (fixed m c)
    (fun g : BitVec 342 → BitVec 256 => decode ∘ cachedRow 86 m c g)
    (classCounts indexDomain c decode) (cached_known m c) (cached_fresh_probability m c)
    (fun g => rowGood (decode ∘ cachedRow 86 m c g)) ((99:ℝ)/98) (tableFailure m c)
    (by norm_num) (fun g hg i => rowGood_kernel _ hg i) le_rfl
  rw [exposed_card,fixed_counts,Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat] at h
  exact h

theorem excess_le_one (i : Fin M) : excess i ≤ 1 := by
  have hp : classProbability i ≤ acceptance := by
    rw [← classProbability_sum]
    exact Finset.single_le_sum (fun j _ => (classProbability_pos j).le) (Finset.mem_univ i)
  have ha : 0<1-acceptance := by norm_num [acceptance]
  have hp' : classProbability i/(1-acceptance) ≤ 1 := by
    apply (div_le_iff₀ ha).mpr
    have hx : acceptance≤1-acceptance := by norm_num [acceptance]
    linarith
  unfold excess
  apply max_le
  · have hk : 0≤kappa := by norm_num [kappa]
    linarith
  · norm_num

theorem excess_score_identity (r : Fin M → ℕ) :
    (∑ i : Fin M,(r i:ℝ)*(referenceWeight i/classProbability i*excess i))=
      excessWeights.score r := by
  unfold WeightedRow.Weights.score
  apply Finset.sum_congr rfl
  intro i hi
  change (r i:ℝ)*(referenceWeight i/classProbability i*excess i)=
    (r i:ℝ)*(referenceWeight i*excess i/classProbability i)
  ring

theorem actual_excess_bound (m : Message) (c : Cache) (hc : WideEmpirical.Good c) :
    outE (WeightedSampling.loop 86 decode tier m L) c
      (fun s => ENNReal.ofReal (score s (fun r => excess r.2))) ≤
      ENNReal.ofReal ((99:ℝ)/98*(kappa*(2/5)+kappa/100)+tableFailure m c) := by
  rw [actual_sign_payoff m c (fun _ i => excess i) (fun _ i => le_max_right _ _)]
  apply ENNReal.ofReal_le_ofReal
  have h := excess_kernel_bound securityWeights L tier (exposed m c) (fixed m c)
    (fun g : BitVec 342 → BitVec 256 => decode ∘ cachedRow 86 m c g)
    (cached_known m c) (cached_fresh_probability m c) excess (fun i => le_max_right _ _)
    1 zero_le_one excess_le_one (fun g => rowGood (decode ∘ cachedRow 86 m c g))
    ((99:ℝ)/98) (tableFailure m c) (by norm_num) (fun g hg i => rowGood_kernel _ hg i) le_rfl
  rw [exposed_card,fixed_counts,Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat,one_mul] at h
  change _ ≤ (99:ℝ)/98*((1-((seen (rowDomain m) c).card:ℝ)/(2:ℝ)^86)*
    (∑ i : Fin M,referenceWeight i*excess i)+
      (∑ i : Fin M,(classCounts (rowDomain m) c decode i:ℝ)*
        (referenceWeight i/classProbability i*excess i))/(2:ℝ)^86)+tableFailure m c at h
  rw [excess_score_identity] at h
  have hb := mul_le_mul_of_nonneg_left (WideEmpirical.good_excess_payoff c hc m)
    (show (0:ℝ)≤99/98 by norm_num)
  exact h.trans (add_le_add hb le_rfl)

theorem uniformMean_instances {A : Type} (fa fb : Fintype A) (f : A → ℝ) :
    @uniformMean A fa f=@uniformMean A fb f := by
  cases Subsingleton.elim fa fb
  rfl

theorem tableFailure_average {α : Type} (oa : OracleComp Spec α) (message : α → Message)
    (c : Cache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    E (run oa c) (fun out => ENNReal.ofReal (tableFailure (message out.1) out.2)) ≤
      (2:ℝ≥0∞)⁻¹^761 := by
  convert actual_rowGood_completion_failure oa c (fun x => hf ⟨342,x⟩ rfl) message using 1
  congr 1
  funext out
  congr 1
  exact uniformMean_instances _ _ _

#print axioms actual_replay_bound
#print axioms actual_excess_bound
#print axioms tableFailure_average
end OptimalOTS.WeightedConstruction.WideCachedRow
end
end

/- Original module: Submissions.UpperCompressions.WideReplayEvent; SHA256 00d8260e4fe20b71dd4c9b70327583e97d1fe26623029d6e3f5b3bffbf16e0f3. -/
section

/-! A cached alternate forged input is bounded by the actual selector's replay
payoff. Distinct inputs, rather than cache membership alone, enforce k_i≥2 when
the selected nonce was itself already public. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideCachedRow
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedSchedule WideDomains WideForest WeightedReference WeightedConstants
open WeightedReplacement WeightedCompletion WeightedCacheCounts
open scoped Classical ENNReal
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes
set_option maxRecDepth 10000

theorem classCount_one (c : Cache) (i : Fin M) (q : Query) (hq : q.1=342)
    (y : BitVec 256) (hc : c q=some y) (hi : decode y=some i) :
    1≤classCounts indexDomain c decode i :=
  WeightedCacheEvidence.one indexDomain c decode i q ((mem_indexDomain q).mpr hq) y hc hi

theorem classCount_two (c : Cache) (i : Fin M) (q q' : Query)
    (hne : q≠q') (hq : q.1=342) (hq' : q'.1=342)
    (y y' : BitVec 256) (hc : c q=some y) (hc' : c q'=some y')
    (hi : decode y=some i) (hi' : decode y'=some i) :
    2≤classCounts indexDomain c decode i :=
  WeightedCacheEvidence.two indexDomain c decode i q q' hne
    ((mem_indexDomain q).mpr hq) ((mem_indexDomain q').mpr hq') y y' hc hc' hi hi'

theorem alternative_replayScore (m : Message) (c : Cache) (η : BitVec 86) (i : Fin M)
    (hconsistent : ∀ y,c (WideForest.encQuery (m,η))=some y → decode y=some i)
    (h : AlternateClass c (m,η) i) : replayScore m c η i=1 := by
  obtain ⟨u,hne,y,hy,hi⟩ := h
  unfold replayScore
  by_cases hη : η∈exposed m c
  · rw [if_pos hη]
    have hs := (Finset.mem_filter.mp hη).2
    cases hc : c (WideForest.encQuery (m,η)) with
    | none => simp [hc] at hs
    | some z =>
      have he : WideForest.encQuery u≠WideForest.encQuery (m,η) := by
        intro he
        exact hne (indexInput_injective 86 he)
      have hk := classCount_two c i (WideForest.encQuery u) (WideForest.encQuery (m,η)) he rfl rfl
        y z hy hc hi (hconsistent z hc)
      exact if_pos hk
  · rw [if_neg hη]
    have hk := classCount_one c i (WideForest.encQuery u) rfl y hy hi
    exact if_neg (by omega)

private def optionEvent {I : Type} (P : I → Prop) : Option I → ℝ≥0∞
  | none => 0
  | some i => if P i then 1 else 0

private theorem optionEvent_le_score {I : Type} (P : I → Prop) (f : I → ℝ)
    (s : Option I) (h : ∀ i, s=some i → P i → f i=1) :
    optionEvent P s ≤ ENNReal.ofReal (WeightedCompletion.score s f) := by
  cases s with
  | none => exact bot_le
  | some i =>
    change (if P i then (1:ℝ≥0∞) else 0) ≤ ENNReal.ofReal (f i)
    by_cases hi : P i
    · rw [if_pos hi,h i rfl hi,ENNReal.ofReal_one]
    · rw [if_neg hi]
      exact bot_le

def alternatePayoff (m : Message) (c : Cache) : Option (WeightedSampling.Winner 86 M) → ℝ≥0∞ :=
  optionEvent (fun r => AlternateClass c (m,r.1) r.2)

@[simp] theorem alternatePayoff_none (m : Message) (c : Cache) :
    alternatePayoff m c none=0 := rfl

@[simp] theorem alternatePayoff_some (m : Message) (c : Cache) (η : BitVec 86) (i : Fin M) :
    alternatePayoff m c (some (η,i))=(if AlternateClass c (m,η) i then 1 else 0) := rfl

attribute [local irreducible] alternatePayoff replayScore optionEvent
theorem alternativePayoff_le (m : Message) (c : Cache)
    (s : Option (WeightedSampling.Winner 86 M))
    (hconsistent : ∀ (η : BitVec 86) (i : Fin M),s=some (η,i) →
      ∀ (y : BitVec 256),c (WideForest.encQuery (m,η))=some y → decode y=some i) :
    alternatePayoff m c s ≤ ENNReal.ofReal
      (WeightedCompletion.score (I := WeightedSampling.Winner 86 M) s
        (fun r : WeightedSampling.Winner 86 M => replayScore m c r.1 r.2)) := by
  unfold alternatePayoff
  exact optionEvent_le_score (fun r => AlternateClass c (m,r.1) r.2)
    (fun r => replayScore m c r.1 r.2) s
    (fun r hs halt => alternative_replayScore m c r.1 r.2 (hconsistent r.1 r.2 hs) halt)

theorem actual_alternative_bound (m : Message) (c : Cache) :
    outE (WeightedSampling.loop 86 decode tier m L) c (alternatePayoff m c) ≤
      ENNReal.ofReal ((99:ℝ)/98*securityWeights.hazard ((2:ℝ)^86)
        (seen (rowDomain m) c).card (classCounts indexDomain c decode)
        (classCounts (rowDomain m) c decode)+tableFailure m c) := by
  apply le_trans (b:=outE (WeightedSampling.loop 86 decode tier m L) c
    (fun s => ENNReal.ofReal (score s (fun r => replayScore m c r.1 r.2))))
  · apply expectedValue_mono_of_support
    intro p hp
    obtain ⟨hsub,hwin⟩ := WeightedSampling.loop_support 86 decode tier m L c p hp
    apply alternativePayoff_le
    intro η i hs y hy
    obtain ⟨z,hz,hzi⟩ := hwin η i hs
    have he : y=z := Option.some.inj ((hsub _ _ hy).symm.trans hz)
    rw [he]
    exact hzi
  · exact actual_replay_bound m c

#print axioms alternative_replayScore
#print axioms actual_alternative_bound
end OptimalOTS.WeightedConstruction.WideCachedRow
end
end

/- Original module: Submissions.UpperCompressions.WeightedBudgetClosure; SHA256 b9be00873c692911dc23b47abbb0420987a9b08b88cade51e280cb25e292fda3. -/
section

/-! Final numerical budget implications. The game-to-payoff inequalities and
stochastic moments are explicit hypotheses; this file does not claim Secure. -/
noncomputable section
namespace WeightedBudgetClosure
open WeightedReference WeightedConstants
open OptimalOTS.WeightedConstruction.WeightedSchedule

def C : ℝ := 99/98
def postRate : ℝ := kappa/2+C*(kappa*(2/5)+kappa/100)

theorem postRate_ge_auth : kappa/2 ≤ postRate := by norm_num [postRate,C,kappa]
theorem postRate_le_large : postRate ≤ C*(91/100)*kappa := by norm_num [postRate,C,kappa]
theorem postRate_le_small : postRate ≤ C*(223/250)*(11/10)*kappa := by
  norm_num [postRate,C,kappa]

theorem actual_mean_nonneg : 0 ≤ mean := by
  unfold mean
  exact Finset.sum_nonneg fun i _ => mul_nonneg (classProbability_pos i).le (referenceWeight_nonneg i)

/-- All numerical hypotheses in the small-budget stopped estimate are now
theorems for the concrete decoder. Only its execution moments remain inputs. -/
theorem small_payoff {Ω : Type*} (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ f g, (∀ ω, f ω ≤ g ω) → E f ≤ E g)
    (hnorm : E (fun _ => 1)=1)
    (τ S P : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K) (hKN : K ≤ (2:ℝ)^86/10)
    (hτ0 : ∀ ω,0 ≤ τ ω) (hτK : ∀ ω,τ ω ≤ K)
    (hm1 : E (fun ω => S ω-mean*τ ω)=0)
    (hm2 : E (fun ω => P ω-τ ω*S ω+mean*τ ω*(τ ω+1)/2)=0)
    (hmSq : E (fun ω => (S ω-mean*τ ω)^2) ≤ K*((L:ℝ)*kappa/2)*mean) :
    E (fun ω => C*(S ω+2*P ω/(2:ℝ)^86)+postRate*(K-τ ω))+kappa*K/1000 ≤
      (243337:ℝ)/245000*kappa*K := by
  have hh : mean ≤ kappa := mean_le.trans (by
    have hk : 0 ≤ kappa := by unfold kappa; positivity
    nlinarith)
  have h := WeightedStopping.stopped_mixed72_payoff E hmono hnorm τ S P C mean postRate
    kappa K ((L:ℝ)*kappa/2) (by norm_num [C]) (by norm_num [C])
    actual_mean_nonneg (by unfold kappa; positivity) hK (by unfold kappa; positivity)
    hKN (by norm_num [L]) hh hτ0 hτK hm1 hm2 hmSq
  have hm : 11*C*mean/10 ≤ C*(223/250)*(11/10)*kappa := by
    have h := mul_le_mul_of_nonneg_left mean_le (show 0 ≤ 11*C/10 by norm_num [C])
    nlinarith
  have hb := mul_le_mul_of_nonneg_left (max_le postRate_le_small hm) hK
  have he : K*(C*(223/250)*(11/10)*kappa)+2*(kappa*K/1000) =
      (243337:ℝ)/245000*kappa*K := by unfold C; ring
  linarith

/-- The large-budget payoff combines cached replay, pre-sign authentication,
and the averaged post-sign continuation using their actual common budget. -/
theorem large_payoff (K q a t R : ℝ)
    (hq : 0 ≤ q) (ha : 0 ≤ a) (ht : 0 ≤ t) (hb : q+a+t ≤ K)
    (hR : R ≤ (91:ℝ)/100*kappa*q+(7:ℝ)/100*kappa*K) :
    C*R+(kappa/2)*a+postRate*t+kappa*K/1000 ≤ (991:ℝ)/1000*kappa*K := by
  have hCr := mul_le_mul_of_nonneg_left hR (show 0 ≤ C by norm_num [C])
  have hArate : kappa/2 ≤ C*(91/100)*kappa := by norm_num [C,kappa]
  have hA := mul_le_mul_of_nonneg_right hArate ha
  have hT := mul_le_mul_of_nonneg_right postRate_le_large ht
  have hB := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ C*(91/100)*kappa by norm_num [C,kappa])
  have he : C*(91/100)*kappa*K+C*(7/100)*kappa*K+kappa*K/1000 =
      (991:ℝ)/1000*kappa*K := by unfold C; ring
  nlinarith

theorem small_below_security (K : ℝ) (hK : 0 ≤ K) :
    (243337:ℝ)/245000*kappa*K ≤ kappa*K := by
  have hk : 0 ≤ kappa*K := mul_nonneg (by unfold kappa; positivity) hK
  nlinarith

theorem large_below_security (K : ℝ) (hK : 0 ≤ K) :
    (991:ℝ)/1000*kappa*K ≤ kappa*K := by
  have hk : 0 ≤ kappa*K := mul_nonneg (by unfold kappa; positivity) hK
  nlinarith

#print axioms small_payoff
#print axioms large_payoff
end WeightedBudgetClosure
end
end

/- Original module: Submissions.UpperCompressions.ReplacementPrefixReserve; SHA256 30a78a89ea9790f070632ad4e14c7be3c2012b57d05e37cc16ae968ffa5d2052. -/
section

/-! A mandatory continuation reserve is unavailable to the public prefix on
every raw query-answer path, not just on average. -/
open OracleSpec OracleComp
open OptimalOTS OptimalOTS.AlgorithmCosts
namespace WeightedReplacement
noncomputable section
open scoped Classical

theorem costAtMost_prefix_reserved {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (R : ℕ)
    (hR : ∀ a b, CostAtMost (k a) b → R ≤ b) :
    ∀ b, CostAtMost (oa >>= k) b → R ≤ b ∧ CostAtMost oa (b-R) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro b hB
    rw [pure_bind] at hB
    exact ⟨hR a b hB,costAtMost_pure _ _⟩
  | query_bind t f ih =>
    intro b hB
    rw [bind_assoc,costAtMost_query_bind_iff] at hB
    have hs (u : Spec.Range t) := ih u (b-queryCost t) (hB.2 u)
    haveI : Nonempty (Spec.Range t) := by cases t <;> infer_instance
    have hr := (hs (Classical.arbitrary (Spec.Range t))).1
    refine ⟨by omega,?_⟩
    rw [costAtMost_query_bind_iff]
    refine ⟨by omega,fun u => ?_⟩
    simpa only [Nat.sub_sub,Nat.add_comm] using (hs u).2

#print axioms costAtMost_prefix_reserved
end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.WideInitialReserve; SHA256 29dca4c75b40eaee9a3372c953d24b329d12c2b3815bd63dea1bb86c59d9ce0a. -/
section

/-! The actual adaptive choose program cannot spend the995 keygen cost or any
of the all-L signing reserve, even on a raw oracle-answer path. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

theorem afterChoose_reserve (pk : PublicKey) (ξ : Rec) (x : Message × A.State)
    (b : ℕ) (hB : CostAtMost (afterChoose A pk (graph.evalRec ξ) x) b) : signBudget ≤ b := by
  rw [afterChoose_loop] at hB
  exact (loop_reserve 86 WeightedSchedule.decode WeightedSchedule.tier x.1 index86_cost signBudget
    (fun s => stB A pk x.1 x.2 (signatureFromWinner ξ s)) b hB).1

theorem choose_reserved_budget {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) (pk : PublicKey) :
    signBudget ≤ B-995 ∧ CostAtMost (A.choose pk) (B-995-signBudget) := by
  obtain ⟨ξ,hξ⟩ := fiber_nonempty pk
  have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
  have h := (keygen_remaining A hB).2 ξ
  have hh : CostAtMost (A.choose pk >>= afterChoose A pk (graph.evalRec ξ)) (B-995) := by
    simpa only [afterKeygen,hpk] using h
  exact costAtMost_prefix_reserved (A.choose pk) (afterChoose A pk (graph.evalRec ξ)) signBudget
    (fun x b hb => afterChoose_reserve A pk ξ x b hb) (B-995) hh

theorem experiment_full_reserve {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) : 995+signBudget ≤ B := by
  have hk := (keygen_remaining A hB).1
  have hs := (choose_reserved_budget A hB 0).1
  omega

#print axioms choose_reserved_budget
#print axioms experiment_full_reserve
end OptimalOTS.WeightedConstruction.WideInitialGame
end
end

/- Original module: Submissions.UpperCompressions.ReplacementReservedClock; SHA256 c10adebfb7ca66815b8f22c015115debea202f66ad9b2e30bf64b49135632eef. -/
section

/-! Expected spent public-prefix cost plus its actual post-reserve remaining
budget fits in one initial public budget, without ENNReal subtraction. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open OptimalOTS
namespace WeightedReplacement
noncomputable section
open scoped Classical

theorem expected_spent_reserved_remaining_le {α β : Type} (oa : OracleComp Spec α)
    (k : α → OracleComp Spec β) (R : ℕ)
    (hR : ∀ a b, CostAtMost (k a) b → R ≤ b) :
    ∀ c b, CostAtMost (oa >>= k) b →
      expectedCharge (fun t => queryCost t) oa c +
        E (runRemaining oa c b) (fun r => ((r.2.2-R:ℕ):ℝ≥0∞)) ≤ (b-R:ℕ) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro c b hB; simp
  | query_bind t f ih =>
    intro c b hB
    have hprefix := (costAtMost_prefix_reserved (liftM (Spec.query t) >>= f) k R hR b hB).2
    rw [costAtMost_query_bind_iff] at hprefix
    rw [bind_assoc,costAtMost_query_bind_iff] at hB
    rw [expectedCharge_query,runRemaining_query,E_bind]
    calc
      _ = (queryCost t:ℝ≥0∞) + E ((oracleImpl t).run c) (fun p =>
          expectedCharge (fun t => queryCost t) (f p.1) p.2 +
            E (runRemaining (f p.1) p.2 (b-queryCost t)) (fun r => ((r.2.2-R:ℕ):ℝ≥0∞))) := by
        rw [add_assoc]
        exact congrArg ((queryCost t:ℝ≥0∞) + ·) (expectedValue_add _ _ _).symm
      _ ≤ (queryCost t:ℝ≥0∞) + E ((oracleImpl t).run c)
          (fun _ => ((b-queryCost t-R:ℕ):ℝ≥0∞)) :=
        add_le_add le_rfl (E_mono _ (fun p => ih p.1 p.2 _ (hB.2 p.1)))
      _ ≤ (queryCost t:ℝ≥0∞) + ((b-queryCost t-R:ℕ):ℝ≥0∞) :=
        add_le_add le_rfl (E_const_le _ _)
      _ = _ := by
        rw [← Nat.cast_add]
        congr 1
        omega

#print axioms expected_spent_reserved_remaining_le
end
end WeightedReplacement
end

/- Original module: Submissions.UpperCompressions.WideInitialClock; SHA256 63a2fa1ee7ff957431b72d2470e0def1474c98b32a528fe1c86484acc6613c23. -/
section

/-! The actual first-stage spent budget and actual supported post-sign reserve
share the public experiment budget after995 keygen and all-L signing. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace OptimalOTS.WeightedConstruction.WideInitialGame
open OptimalOTS.Dag WideForest WideForest.Name WeightedReplacement WeightedSampling
attribute [local irreducible] Finset.univ Finset.filter WeightedResearch92.classes
variable (A : forestScheme.toAlgorithm.Adversary)

theorem choose_spent_post_remaining_le {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) (pk : PublicKey) :
    expectedCharge (fun t => queryCost t) (A.choose pk) ∅ +
      E (runRemaining (A.choose pk) ∅ (B-995))
        (fun r => ((r.2.2-signBudget:ℕ):ℝ≥0∞)) ≤ (B-995-signBudget:ℕ) := by
  obtain ⟨ξ,hξ⟩ := fiber_nonempty pk
  have hpk := pkOf_of_subset_fiberA (Finset.Subset.refl _) ξ hξ
  have h := (keygen_remaining A hB).2 ξ
  have hh : CostAtMost (A.choose pk >>= afterChoose A pk (graph.evalRec ξ)) (B-995) := by
    simpa only [afterKeygen,hpk] using h
  exact expected_spent_reserved_remaining_le (A.choose pk) (afterChoose A pk (graph.evalRec ξ)) signBudget
    (fun x b hb => afterChoose_reserve A pk ξ x b hb) ∅ (B-995) hh

theorem sum_fiber_weights : (∑ pk : PublicKey, sumW (fiberA pk)) = 1 := by
  unfold sumW fiberA
  exact (Finset.sum_fiberwise Finset.univ pkOf (fun _ => w)).trans sum_w

/-- The same public clock after averaging over the actual public-key record
fibers. Uniform record weights total one. -/
theorem global_public_clock_le {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B) :
    (∑ pk : PublicKey, sumW (fiberA pk) *
      (expectedCharge (fun t => queryCost t) (A.choose pk) ∅ +
        E (runRemaining (A.choose pk) ∅ (B-995))
          (fun r => ((r.2.2-signBudget:ℕ):ℝ≥0∞)))) ≤ (B-995-signBudget:ℕ) := by
  calc
    _ ≤ ∑ pk : PublicKey, sumW (fiberA pk)*(B-995-signBudget:ℕ) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul' le_rfl (choose_spent_post_remaining_le A hB pk)
    _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

#print axioms choose_spent_post_remaining_le
#print axioms global_public_clock_le
end OptimalOTS.WeightedConstruction.WideInitialGame
end
end

/- Original module: Submissions.UpperCompressions.ActualPayoffExpansion; SHA256 e8fc99f5c7cca9460e9060b81a98ea07cf0bc3de7e867e7732128343a49b502c. -/
section

/-! Concrete replay/excess expansion of the actual full-game payoff. The bad
gate is paid once, while the conditional table error is kept separate and only
bounded after averaging over the actual adaptive public execution. -/
open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option maxRecDepth 10000
namespace OptimalOTS.WeightedConstruction.WideForest
open OptimalOTS.Dag Name WeightedReplacement WeightedSampling WideInitialGame
open WeightedCacheCounts WideDomains WeightedSchedule WeightedBudgetClosure
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ Finset.filter

def cacheHazard (m : Message) (c : Cache) : ℝ :=
  securityWeights.hazard ((2:ℝ)^86) (seen (rowDomain m) c).card
    (classCounts indexDomain c decode) (classCounts (rowDomain m) c decode)

theorem signer_replay_bound (m : Message) (c : Cache) :
    signerAverage m c signBudget (winnerReplay c m) ≤
      ENNReal.ofReal (C*cacheHazard m c)+ENNReal.ofReal (WideCachedRow.tableFailure m c) := by
  rw [signerAverage_eq_actual]
  have he : winnerReplay c m = WideCachedRow.alternatePayoff m c := by
    funext s
    cases s with
    | none => rfl
    | some s =>
      rcases s with ⟨η,i⟩
      rw [WideCachedRow.alternatePayoff_some]
      rfl
  rw [he]
  exact (WideCachedRow.actual_alternative_bound m c).trans ENNReal.ofReal_add_le

theorem signer_excess_bound (m : Message) (c : Cache) (hc : WideEmpirical.Good c) :
    signerAverage m c signBudget winnerExcess ≤
      ENNReal.ofReal (C*(WeightedReference.kappa*(2/5)+WeightedReference.kappa/100)) +
        ENNReal.ofReal (WideCachedRow.tableFailure m c) := by
  rw [signerAverage_eq_actual]
  have he : winnerExcess = (fun s => ENNReal.ofReal (WeightedCompletion.score s
      (fun r : Winner 86 WeightedSchedule.M => WeightedSchedule.excess r.2))) := by
    funext s
    cases s <;> simp [winnerExcess,WeightedCompletion.score]
  rw [he]
  exact (WideCachedRow.actual_excess_bound m c hc).trans ENNReal.ofReal_add_le

theorem concrete_postRate : authRate +
    ENNReal.ofReal (C*(WeightedReference.kappa*(2/5)+WeightedReference.kappa/100)) =
      ENNReal.ofReal postRate := by
  rw [authRate_ofReal,← ENNReal.ofReal_add]
  · rfl
  · unfold WeightedReference.kappa
    positivity
  · unfold C WeightedReference.kappa
    positivity

theorem concrete_continuation_bound (m : Message) (c : Cache) (hc : WideEmpirical.Good c)
    (remaining : ℕ) :
    signerAverage m c signBudget (winnerReplay c m) +
      remaining*(authRate+signerAverage m c signBudget winnerExcess) ≤
      ENNReal.ofReal (C*cacheHazard m c)+ENNReal.ofReal postRate*remaining +
        (1+remaining)*ENNReal.ofReal (WideCachedRow.tableFailure m c) := by
  have he : authRate+signerAverage m c signBudget winnerExcess ≤
      ENNReal.ofReal postRate+ENNReal.ofReal (WideCachedRow.tableFailure m c) := by
    calc
      _ ≤ authRate + (ENNReal.ofReal (C*(WeightedReference.kappa*(2/5)+WeightedReference.kappa/100)) +
          ENNReal.ofReal (WideCachedRow.tableFailure m c)) := add_le_add le_rfl (signer_excess_bound m c hc)
      _ = _ := by rw [← add_assoc,concrete_postRate]
  calc
    _ ≤ (ENNReal.ofReal (C*cacheHazard m c)+ENNReal.ofReal (WideCachedRow.tableFailure m c)) +
        remaining*(ENNReal.ofReal postRate+ENNReal.ofReal (WideCachedRow.tableFailure m c)) :=
      add_le_add (signer_replay_bound m c) (mul_le_mul_right he remaining)
    _ = _ := by ring

def preAuth (A : forestScheme.toAlgorithm.Adversary) : ℝ≥0∞ :=
  ∑ pk : PublicKey, (authRate*sumW (fiberA pk))*
    expectedCharge (otherPaid (isIndexLength (msgBits+86))) (A.choose pk) ∅

def weightedClock (A : forestScheme.toAlgorithm.Adversary) (B : ℕ)
    (F : PublicKey → ((Message × A.State) × Cache × ℕ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ pk : PublicKey, sumW (fiberA pk)*E (runRemaining (A.choose pk) ∅ (B-995)) (F pk)

def gatedHazard (A : forestScheme.toAlgorithm.Adversary)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  if good pk r then ENNReal.ofReal (C*cacheHazard r.1.1 r.2.1) else 0

def badGate (A : forestScheme.toAlgorithm.Adversary)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  if good pk r then 0 else 1

def postRemaining (A : forestScheme.toAlgorithm.Adversary)
    (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ := (r.2.2-signBudget : ℕ)

def tableError (A : forestScheme.toAlgorithm.Adversary)
    (_pk : PublicKey) (r : (Message × A.State) × Cache × ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (WideCachedRow.tableFailure r.1.1 r.2.1)

theorem gated_payoff_pointwise (A : forestScheme.toAlgorithm.Adversary) (B : ℕ)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (hgood : ∀ pk r, good pk r → WideEmpirical.Good r.2.1)
    (pk : PublicKey) (r : (Message × A.State) × Cache × ℕ)
    (hr : r.2.2-signBudget ≤ B) :
    gatedContinuationPayoff A good pk r ≤ sumW (fiberA pk)*
      (gatedHazard A good pk r+ENNReal.ofReal postRate*postRemaining A pk r+
        badGate A good pk r+(1+B)*tableError A pk r) := by
  by_cases hg : good pk r
  · simp only [gatedContinuationPayoff,gatedHazard,badGate,if_pos hg,add_zero,postRemaining,tableError]
    apply mul_le_mul_right
    refine (concrete_continuation_bound r.1.1 r.2.1 (hgood pk r hg) _).trans ?_
    gcongr
  · simp only [gatedContinuationPayoff,gatedHazard,badGate,if_neg hg,zero_add,mul_one]
    calc
      _ = sumW (fiberA pk)*1 := by rw [mul_one]
      _ ≤ _ := mul_le_mul_right (le_add_right le_add_self) _

theorem weightedClock_add (A : forestScheme.toAlgorithm.Adversary) (B : ℕ)
    (F G : PublicKey → ((Message × A.State) × Cache × ℕ) → ℝ≥0∞) :
    weightedClock A B (fun pk r => F pk r+G pk r) = weightedClock A B F+weightedClock A B G := by
  unfold weightedClock
  simp only [auth_E_add,mul_add,Finset.sum_add_distrib]

theorem weightedClock_const_mul (A : forestScheme.toAlgorithm.Adversary) (B : ℕ) (a : ℝ≥0∞)
    (F : PublicKey → ((Message × A.State) × Cache × ℕ) → ℝ≥0∞) :
    weightedClock A B (fun pk r => a*F pk r) = a*weightedClock A B F := by
  unfold weightedClock
  simp_rw [← E_const_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem weightedClock_tableError_le (A : forestScheme.toAlgorithm.Adversary) (B : ℕ) :
    weightedClock A B (tableError A) ≤ (2:ℝ≥0∞)⁻¹^761 := by
  have htail (pk : PublicKey) : E (runRemaining (A.choose pk) ∅ (B-995)) (tableError A pk) ≤
      (2:ℝ≥0∞)⁻¹^761 := by
    have h := WideCachedRow.tableFailure_average (A.choose pk) (fun x => x.1) ∅ (fun _ _ => rfl)
    rw [← runRemaining_project (A.choose pk) ∅ (B-995),E_map] at h
    exact h
  calc
    _ ≤ ∑ pk : PublicKey, sumW (fiberA pk)*((2:ℝ≥0∞)⁻¹^761) :=
      Finset.sum_le_sum fun pk _ => mul_le_mul_right (htail pk) _
    _ = _ := by rw [← Finset.sum_mul,sum_fiber_weights,one_mul]

/-- Shared concrete final-payoff expansion. The good hazard remains gated;
post remaining cost is ungated; bad probability and the averaged completion
tail are each charged once. Small and large numerical closures use this same
actual-game bound. -/
theorem global_actual_payoff_expanded (A : forestScheme.toAlgorithm.Adversary) {B : ℕ}
    (hB : CostAtMost (forestScheme.toAlgorithm.experiment A) B)
    (good : PublicKey → ((Message × A.State) × Cache × ℕ) → Prop)
    (hgood : ∀ pk r, good pk r → WideEmpirical.Good r.2.1) :
    E (run (forestScheme.toAlgorithm.experiment A) ∅) successValue ≤
      preAuth A+weightedClock A B (gatedHazard A good)+
      ENNReal.ofReal postRate*weightedClock A B (postRemaining A)+
      weightedClock A B (badGate A good)+(1+B)*((2:ℝ≥0∞)⁻¹^761) := by
  have h := global_actual_game_payoff_gated A hB good
  have hp : (∑ pk : PublicKey, E (runRemaining (A.choose pk) ∅ (B-995))
      (gatedContinuationPayoff A good pk)) ≤
      weightedClock A B (fun pk r => gatedHazard A good pk r+
        ENNReal.ofReal postRate*postRemaining A pk r+badGate A good pk r+(1+B)*tableError A pk r) := by
    apply Finset.sum_le_sum
    intro pk _
    rw [E_const_mul]
    apply expectedValue_mono_of_support
    intro r hr
    apply gated_payoff_pointwise A B good hgood pk r
    exact (Nat.sub_le _ _).trans ((experiment_choose_reserve A hB pk r hr).2.1.trans (Nat.sub_le _ _))
  refine (h.trans (add_le_add le_rfl hp)).trans ?_
  rw [weightedClock_add,weightedClock_add,weightedClock_add,
    weightedClock_const_mul,weightedClock_const_mul]
  calc
    _ = preAuth A+weightedClock A B (gatedHazard A good)+
        ENNReal.ofReal postRate*weightedClock A B (postRemaining A)+
        weightedClock A B (badGate A good)+(1+B)*weightedClock A B (tableError A) := by unfold preAuth; ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_right (weightedClock_tableError_le A B) (1+B))

#print axioms signer_replay_bound
#print axioms concrete_continuation_bound
#print axioms weightedClock_tableError_le
#print axioms global_actual_payoff_expanded
end OptimalOTS.WeightedConstruction.WideForest
end
end

/- Original module: Submissions.UpperCompressions.WideStoppedPayoff; SHA256 0846d6b61e8bb1efc60a697a8d92cbb36f75abd330a78e836cd77c28a4c6f17d. -/
section

/-! Small-budget stopped payoff on the actual protected shared oracle.
Only a fresh initial index domain and the actual program budget are assumed. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideStoppedPayoff
open OracleSpec OracleComp
open WeightedReference WeightedConstants WeightedBudgetClosure
open WeightedSchedule WideDomains WeightedCacheCounts WeightedRow.Weights
open WeightedRealExecution
open scoped Classical
set_option maxHeartbeats 1000000

def queryCount (c : hashSpec.QueryCache) : ℕ := (seen indexDomain c).card
def counts (c : hashSpec.QueryCache) : Fin M → ℕ := classCounts indexDomain c decode
def score (c : hashSpec.QueryCache) : ℝ := securityWeights.score (counts c)
def pairs (c : hashSpec.QueryCache) : ℝ := securityWeights.pairScore (counts c)

theorem moments {α : Type} (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (c : hashSpec.QueryCache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    let run := (simulateQ oracleImpl oa).run c
    realEval run (fun out => score out.2-mean*(queryCount out.2:ℝ))=0 ∧
    realEval run (fun out => pairs out.2-(queryCount out.2:ℝ)*score out.2+
      mean*(queryCount out.2:ℝ)*((queryCount out.2:ℝ)+1)/2)=0 ∧
    realEval run (fun out => (score out.2-mean*(queryCount out.2:ℝ))^2) ≤
      (B:ℝ)*((L:ℝ)*kappa/2)*mean := by
  obtain ⟨hq,hk⟩ := WidePreSign.index_initial c hf
  exact WeightedProtectedCache.stopped_moments securityWeights indexDomain decode decoder_law
    ((L:ℝ)*kappa/2) (by norm_num [L,kappa]) referenceWeight_le oa B hB c hq hk

theorem realEval_congr_support {α : Type} (oa : ProbComp α) (f g : α → ℝ)
    (h : ∀ a ∈ support oa,f a=g a) : realEval oa f=realEval oa g :=
  le_antisymm (realEval_mono_of_support oa f g (fun a ha => (h a ha).le))
    (realEval_mono_of_support oa g f (fun a ha => (h a ha).symm.le))

theorem small_payoff_actual {α : Type} (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (hBN : (B:ℝ) ≤ (2:ℝ)^86/10)
    (c : hashSpec.QueryCache) (hf : ∀ q : Query,q.1=342 → c q=none) :
    realEval ((simulateQ oracleImpl oa).run c) (fun out =>
      C*(score out.2+2*pairs out.2/(2:ℝ)^86)+postRate*((B:ℝ)-(queryCount out.2:ℝ)))+
        kappa*(B:ℝ)/1000 ≤ (243337:ℝ)/245000*kappa*(B:ℝ) := by
  let run := (simulateQ oracleImpl oa).run c
  let τ : α × hashSpec.QueryCache → ℝ := fun out => min (queryCount out.2:ℝ) (B:ℝ)
  have hq0 := (WidePreSign.index_initial c hf).1
  have hcap (out) (ho : out ∈ support run) : queryCount out.2 ≤ B := by
    have h := WeightedProtectedCache.count_bound indexDomain oa B hB c out ho
    rw [hq0,zero_add] at h
    exact h.trans (min_le_right _ _)
  have hτ (out) (ho : out ∈ support run) : τ out=(queryCount out.2:ℝ) := by
    exact min_eq_left (by exact_mod_cast hcap out ho)
  obtain ⟨hm1,hm2,hmSq⟩ := moments oa B hB c hf
  have hm1' : realEval run (fun out => score out.2-mean*τ out)=0 := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hm1
  have hm2' : realEval run (fun out => pairs out.2-τ out*score out.2+mean*τ out*(τ out+1)/2)=0 := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hm2
  have hmSq' : realEval run (fun out => (score out.2-mean*τ out)^2) ≤
      (B:ℝ)*((L:ℝ)*kappa/2)*mean := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hmSq
  have h := WeightedBudgetClosure.small_payoff (realEval run) (realEval_mono run)
    (realEval_const run 1) τ (fun out => score out.2) (fun out => pairs out.2) (B:ℝ)
    (Nat.cast_nonneg B) hBN
    (fun out => le_min (Nat.cast_nonneg _) (Nat.cast_nonneg B))
    (fun out => min_le_right _ _) hm1' hm2' hmSq'
  rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])] at h
  exact h

#print axioms moments
#print axioms small_payoff_actual
end OptimalOTS.WeightedConstruction.WideStoppedPayoff
end
end

/- Original module: Submissions.UpperCompressions.WeightedRealBridge; SHA256 3e11290d9487968f877dbe62ecbdd01c1d709ee44cceb108680b659a5e8ee147. -/
section

/-! Real/ENNReal expectation transport on the actual supported execution. -/
noncomputable section
namespace WeightedRealExecution
open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal
variable {α : Type}

theorem realEval_congr_on_support (oa : ProbComp α) (f g : α → ℝ)
    (h : ∀ a ∈ support oa,f a=g a) : realEval oa f=realEval oa g :=
  le_antisymm (realEval_mono_of_support oa f g (fun a ha => (h a ha).le))
    (realEval_mono_of_support oa g f (fun a ha => (h a ha).symm.le))

theorem ofReal_realEval_on_support (oa : ProbComp α) (f : α → ℝ)
    (hf : ∀ a ∈ support oa,0≤f a) :
    ENNReal.ofReal (realEval oa f)=expectedValue oa (fun a => ENNReal.ofReal (f a)) := by
  let g := fun a => max (f a) 0
  have hfg : realEval oa f=realEval oa g :=
    realEval_congr_on_support oa f g (fun a ha => (max_eq_left (hf a ha)).symm)
  rw [hfg,ofReal_realEval oa g (fun a => le_max_right _ _)]
  have hg : (fun a => ENNReal.ofReal (g a))=(fun a => ENNReal.ofReal (f a)) := by
    funext a
    by_cases h : 0≤f a
    · rw [show g a=f a from max_eq_left h]
    · have hn : f a≤0 := le_of_not_ge h
      rw [show g a=0 from max_eq_right hn,ENNReal.ofReal_zero,ENNReal.ofReal_of_nonpos hn]
  rw [hg]

theorem E_ofReal_ne_top (oa : ProbComp α) (f : α → ℝ) (hf : ∀ a ∈ support oa,0≤f a) :
    expectedValue oa (fun a => ENNReal.ofReal (f a))≠⊤ := by
  rw [← ofReal_realEval_on_support oa f hf]
  exact ENNReal.ofReal_ne_top

theorem realEval_nonneg_on_support (oa : ProbComp α) (f : α → ℝ)
    (hf : ∀ a ∈ support oa,0≤f a) : 0≤realEval oa f := by
  have h := realEval_mono_of_support oa (fun _ => 0) f hf
  rwa [realEval_const] at h

#print axioms ofReal_realEval_on_support
end WeightedRealExecution
end
end

/- Original module: Submissions.UpperCompressions.WideSmallAggregation; SHA256 85080e9764d7cd2d05a1b4eee298f2df104f5c9345d8572ebe2c489c3f5d9a80. -/
section

/-! Shared-budget aggregation of the checked actual small-budget moments. -/
noncomputable section
namespace OptimalOTS.WeightedConstruction.WideStoppedPayoff
open OracleSpec OracleComp OracleComp.EvalDist
open WeightedReference WeightedConstants WeightedBudgetClosure
open WeightedSchedule WideDomains WeightedCacheCounts WeightedRow.Weights
open WeightedRealExecution
open scoped Classical ENNReal
set_option maxHeartbeats 1000000

def pairEnvelope (c : Cache) : ℝ := score c+2*pairs c/(2:ℝ)^86

theorem score_nonneg (c : Cache) : 0 ≤ score c := by
  unfold score WeightedRow.Weights.score
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (referenceWeight_nonneg i)

theorem pairs_nonneg (c : Cache) : 0≤pairs c := by
  unfold pairs WeightedRow.Weights.pairScore
  exact Finset.sum_nonneg fun i _ => div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (referenceWeight_nonneg i)) (classProbability_pos i).le

theorem pairEnvelope_nonneg (c : Cache) : 0≤pairEnvelope c := by
  unfold pairEnvelope
  exact add_nonneg (score_nonneg c) (div_nonneg (mul_nonneg (by norm_num) (pairs_nonneg c)) (by positivity))

theorem hazard_le_pairEnvelope (m : Message) (c : Cache) :
    securityWeights.hazard ((2:ℝ)^86) (seen (rowDomain m) c).card
      (classCounts indexDomain c decode) (classCounts (rowDomain m) c decode) ≤ pairEnvelope c :=
  securityWeights.hazard_le_score_pair _ (by positivity) _ _ _ (row_class_le_global m c)

theorem actual_small_shared_real {α : Type} (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (hBN : (B:ℝ)≤(2:ℝ)^86/10)
    (c : Cache) (hf : ∀ q : Query,q.1=342 → c q=none)
    (a t : ℝ) (ha : 0≤a) (ht : 0≤t)
    (hclock : realEval (run oa c) (fun out => (queryCount out.2:ℝ))+a+t ≤ B) :
    C*realEval (run oa c) (fun out => pairEnvelope out.2)+(kappa/2)*a+postRate*t+
      kappa*(B:ℝ)/1000 ≤ (243337:ℝ)/245000*kappa*(B:ℝ) := by
  have h := small_payoff_actual oa B hB hBN c hf
  change realEval (run oa c) (fun out => C*pairEnvelope out.2+
    postRate*((B:ℝ)-(queryCount out.2:ℝ)))+_ ≤ _ at h
  rw [realEval_add,realEval_mul,realEval_mul,realEval_sub,realEval_const] at h
  have hp : 0≤postRate := by norm_num [postRate,C,kappa]
  have hshare := mul_le_mul_of_nonneg_left hclock hp
  have hauth := mul_le_mul_of_nonneg_right postRate_ge_auth ha
  nlinarith

theorem actual_small_shared_ennreal {α : Type} (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (hBN : (B:ℝ) ≤ (2:ℝ)^86/10)
    (c : Cache) (hf : ∀ q : Query,q.1=342 → c q=none)
    (a t : ℝ≥0∞)
    (hclock : E (run oa c) (fun out => (queryCount out.2:ℝ≥0∞))+a+t ≤ B) :
    ENNReal.ofReal C*E (run oa c) (fun out => ENNReal.ofReal (pairEnvelope out.2))+
      ENNReal.ofReal (kappa/2)*a+ENNReal.ofReal postRate*t+
      ENNReal.ofReal (kappa*(B:ℝ)/1000) ≤
        ENNReal.ofReal ((243337:ℝ)/245000*kappa*(B:ℝ)) := by
  let run := OptimalOTS.run oa c
  let Q := realEval run (fun out => (queryCount out.2:ℝ))
  let P := realEval run (fun out => pairEnvelope out.2)
  have hQ0 : 0 ≤ Q := realEval_nonneg run _ (fun out => Nat.cast_nonneg _)
  have hP0 : 0 ≤ P := realEval_nonneg run _ (fun out => pairEnvelope_nonneg _)
  have hQ : E run (fun out => (queryCount out.2:ℝ≥0∞))=ENNReal.ofReal Q := by
    simpa only [ENNReal.ofReal_natCast] using
      (ofReal_realEval run (fun out => (queryCount out.2:ℝ)) (fun out => Nat.cast_nonneg _)).symm
  have hP : E run (fun out => ENNReal.ofReal (pairEnvelope out.2))=ENNReal.ofReal P :=
    (ofReal_realEval run (fun out => pairEnvelope out.2) (fun out => pairEnvelope_nonneg _)).symm
  change E run _+a+t ≤ B at hclock
  rw [hQ] at hclock
  have haB : a ≤ (B:ℝ≥0∞) := (le_add_self.trans le_self_add).trans hclock
  have htB : t ≤ (B:ℝ≥0∞) := le_add_self.trans hclock
  have ha : a≠⊤ := ne_top_of_le_ne_top (by simp) haB
  have ht : t≠⊤ := ne_top_of_le_ne_top (by simp) htB
  have hsum : ENNReal.ofReal Q+a≠⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,ha⟩
  have hc := ENNReal.toReal_mono (show (B:ℝ≥0∞)≠⊤ by simp) hclock
  rw [ENNReal.toReal_add hsum ht,ENNReal.toReal_add ENNReal.ofReal_ne_top ha,
    ENNReal.toReal_ofReal hQ0,ENNReal.toReal_natCast] at hc
  have hr := actual_small_shared_real oa B hB hBN c hf a.toReal t.toReal
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hc
  have hC0 : 0 ≤ C := by norm_num [C]
  have hk0 : 0 ≤ kappa/2 := by norm_num [kappa]
  have hp0 : 0 ≤ postRate := by norm_num [postRate,C,kappa]
  have htail : 0 ≤ kappa*(B:ℝ)/1000 :=
    div_nonneg (mul_nonneg (by norm_num [kappa]) (Nat.cast_nonneg B)) (by norm_num)
  have hCP : 0 ≤ C*P := mul_nonneg hC0 hP0
  have hka : 0 ≤ (kappa/2)*a.toReal := mul_nonneg hk0 ENNReal.toReal_nonneg
  have hpt : 0 ≤ postRate*t.toReal := mul_nonneg hp0 ENNReal.toReal_nonneg
  have he := ENNReal.ofReal_le_ofReal hr
  change ENNReal.ofReal (C*P+(kappa/2)*a.toReal+postRate*t.toReal+kappa*(B:ℝ)/1000) ≤ _ at he
  rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hCP hka) hpt) htail,
    ENNReal.ofReal_add (add_nonneg hCP hka) hpt,ENNReal.ofReal_add hCP hka,
    ENNReal.ofReal_mul hC0,ENNReal.ofReal_mul hk0,ENNReal.ofReal_mul hp0,
    ENNReal.ofReal_toReal ha,ENNReal.ofReal_toReal ht] at he
  change ENNReal.ofReal C*E run (fun out => ENNReal.ofReal (pairEnvelope out.2))+_+_+_ ≤ _
  rw [hP]
  exact he

#print axioms actual_small_shared_ennreal
#print axioms hazard_le_pairEnvelope
#print axioms actual_small_shared_real
end OptimalOTS.WeightedConstruction.WideStoppedPayoff
end
end

