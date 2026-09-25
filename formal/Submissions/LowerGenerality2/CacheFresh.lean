import Submissions.LowerGenerality2.Cache
import VCVio.EvalDist.Expectation

/-!
# Fresh message prefixes in a finite bare-oracle cache

A cache containing at most `K` strings can intersect the nonce domain of at most
`K` messages. This fact uses only the strings in the cache, without labels or a
condition on the computation graph.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section
open scoped Classical

namespace OptimalOTS.BareLower

open OptimalOTS.Dag


attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

abbrev CacheP := (hashSpec).QueryCache

/-- `D` contains every query for which the cache already has an answer. -/
def HasSupport (c : CacheP) (D : Finset Query) : Prop :=
  ∀ q, (c q).isSome → q ∈ D

/-- Every nonce query for this message is absent from the cache. -/
def FreshMessage (c : CacheP) (m : BitVec msgBits) : Prop :=
  ∀ η : BitVec nonceBits, c ⟨msgBits + nonceBits, m ++ η⟩ = none

/-- Extract the message prefix of an index-length string. Its value on other
lengths is harmless because those strings cannot witness a nonce-domain hit. -/
def messagePrefix (q : Query) : BitVec msgBits :=
  q.2.extractLsb' nonceBits msgBits

@[simp] theorem messagePrefix_append (m : BitVec msgBits)
    (η : BitVec nonceBits) :
    messagePrefix ⟨msgBits + nonceBits, m ++ η⟩ = m :=
  BitVec.extractLsb'_append_eq_left

@[simp] theorem hasSupport_empty : HasSupport (∅ : CacheP) ∅ := by
  intro q hq
  simp at hq

theorem HasSupport.cacheQuery {c : CacheP} {D : Finset Query}
    (hc : HasSupport c D) (q : Query) (u : BitVec hashBits) :
    HasSupport (c.cacheQuery q u) (insert q D) := by
  intro q' hq'
  by_cases h : q' = q
  · simp [h]
  · rw [QueryCache.cacheQuery_of_ne _ _ h] at hq'
    exact Finset.mem_insert_of_mem (hc q' hq')

theorem nonfresh_subset_prefixes {c : CacheP} {D : Finset Query}
    (hc : HasSupport c D) :
    (Finset.univ.filter fun m : BitVec msgBits => ¬ FreshMessage c m) ⊆
      D.image (messagePrefix) := by
  intro m hm
  have hm' : ¬ FreshMessage c m := (Finset.mem_filter.mp hm).2
  simp only [FreshMessage, not_forall] at hm'
  obtain ⟨η, hη⟩ := hm'
  exact Finset.mem_image.mpr ⟨⟨_, m ++ η⟩,
    hc _ (Option.ne_none_iff_isSome.mp hη), messagePrefix_append m η⟩

/-- At most one message prefix is excluded per cached string. -/
theorem card_nonfresh_le {c : CacheP} {D : Finset Query}
    (hc : HasSupport c D) :
    (Finset.univ.filter fun m : BitVec msgBits => ¬ FreshMessage c m).card ≤ D.card :=
  (Finset.card_le_card (nonfresh_subset_prefixes hc)).trans (Finset.card_image_le)

/-- Uniform sampling turns a finite event's cardinality into its exact probability. -/
theorem uniform_indicator (n : ℕ) (A : Finset (BitVec n)) :
    expectedValue ($ᵗ BitVec n) (fun m => if m ∈ A then (1 : ℝ≥0∞) else 0) =
      (A.card : ℝ≥0∞) / 2 ^ n := by
  rw [expectedValue_def, tsum_fintype]
  simp only [probOutput_uniformSample]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul, div_eq_mul_inv, Fintype.card_bitVec]
  norm_cast

/-- A uniform message has a previously queried nonce-domain point with
probability at most `card D / 2^msgBits`. -/
theorem uniform_nonfresh_le {c : CacheP} {D : Finset Query}
    (hc : HasSupport c D) :
    expectedValue ($ᵗ BitVec msgBits)
      (fun m => if ¬ FreshMessage c m then (1 : ℝ≥0∞) else 0) ≤
      (D.card : ℝ≥0∞) / 2 ^ msgBits := by
  have heq : (fun m : BitVec msgBits => if ¬ FreshMessage c m then (1 : ℝ≥0∞) else 0) =
      (fun m => if m ∈ Finset.univ.filter (fun m => ¬ FreshMessage c m)
        then (1 : ℝ≥0∞) else 0) := by
    funext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq, uniform_indicator]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_nonfresh_le hc) _

/-- Excluding a previous message costs at most one additional prefix. -/
theorem card_nonfresh_or_eq_le {c : CacheP} {D : Finset Query}
    (hc : HasSupport c D) (m₀ : BitVec msgBits) :
    (Finset.univ.filter fun m : BitVec msgBits => ¬ FreshMessage c m ∨ m = m₀).card ≤
      D.card + 1 := by
  have hsub : (Finset.univ.filter fun m : BitVec msgBits => ¬ FreshMessage c m ∨ m = m₀) ⊆
      insert m₀ (D.image (messagePrefix)) := by
    intro m hm
    rcases (Finset.mem_filter.mp hm).2 with hm | rfl
    · exact Finset.mem_insert_of_mem
        (nonfresh_subset_prefixes hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩))
    · exact Finset.mem_insert_self _ _
  calc _ ≤ (insert m₀ (D.image (messagePrefix))).card := Finset.card_le_card hsub
    _ ≤ (D.image (messagePrefix)).card + 1 := Finset.card_insert_le _ _
    _ ≤ D.card + 1 := Nat.add_le_add_right Finset.card_image_le 1

/-- A uniform fresh message can also be required to differ from a previous one. -/
theorem uniform_nonfresh_or_eq_le {c : CacheP} {D : Finset Query}
    (hc : HasSupport c D) (m₀ : BitVec msgBits) :
    expectedValue ($ᵗ BitVec msgBits)
      (fun m => if ¬ FreshMessage c m ∨ m = m₀ then (1 : ℝ≥0∞) else 0) ≤
      ((D.card + 1 : ℕ) : ℝ≥0∞) / 2 ^ msgBits := by
  have heq : (fun m : BitVec msgBits =>
        if ¬ FreshMessage c m ∨ m = m₀ then (1 : ℝ≥0∞) else 0) =
      (fun m => if m ∈ Finset.univ.filter (fun m => ¬ FreshMessage c m ∨ m = m₀)
        then (1 : ℝ≥0∞) else 0) := by
    funext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq, uniform_indicator]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_nonfresh_or_eq_le hc m₀) _

/-- A complement form useful when freshness gates an attack. -/
theorem uniform_complement_ge (n : ℕ) (bad : BitVec n → Prop) [DecidablePred bad] (δ : ℝ≥0∞)
    (hbad : expectedValue ($ᵗ BitVec n) (fun m => if bad m then (1 : ℝ≥0∞) else 0) ≤ δ) :
    1 - δ ≤ expectedValue ($ᵗ BitVec n) (fun m => if ¬ bad m then (1 : ℝ≥0∞) else 0) := by
  apply tsub_le_iff_right.mpr
  have hadd : expectedValue ($ᵗ BitVec n) (fun m => if ¬ bad m then (1 : ℝ≥0∞) else 0) +
      expectedValue ($ᵗ BitVec n) (fun m => if bad m then (1 : ℝ≥0∞) else 0) = 1 := by
    rw [← expectedValue_add]
    have heq : (fun m : BitVec n => (if ¬ bad m then (1 : ℝ≥0∞) else 0) +
        (if bad m then (1 : ℝ≥0∞) else 0)) = fun _ => (1 : ℝ≥0∞) := by
      funext m
      by_cases hm : bad m <;> simp only [hm, not_true_eq_false, not_false_eq_true,
        if_true, if_false, zero_add, add_zero]
    rw [heq, expectedValue_const (by simp)]
  calc 1 = _ := hadd.symm
    _ ≤ _ := add_le_add_right hbad _

/-- A fresh message different from `m₀` retains all but `(card D+1)/2^msgBits`
of the probability mass. -/
theorem uniform_fresh_ne_ge {c : CacheP} {D : Finset Query}
    (hc : HasSupport c D) (m₀ : BitVec msgBits) :
    1 - ((D.card + 1 : ℕ) : ℝ≥0∞) / 2 ^ msgBits ≤
      expectedValue ($ᵗ BitVec msgBits)
        (fun m => if FreshMessage c m ∧ m ≠ m₀ then (1 : ℝ≥0∞) else 0) := by
  simpa only [not_or, not_not] using uniform_complement_ge msgBits
    (fun m => ¬ FreshMessage c m ∨ m = m₀) _ (by simpa only using uniform_nonfresh_or_eq_le hc m₀)

/-- A computation of cost at most `b` adds at most `b` cache entries. -/
theorem exists_support_run {α : Type} (oa : OracleComp Spec α) :
    ∀ {b : ℕ}, CostAtMost oa b → ∀ {c : CacheP} {D : Finset Query},
      HasSupport c D → ∀ p ∈ support (run oa c),
        ∃ D' : Finset Query, HasSupport p.2 D' ∧ D'.card ≤ D.card + b := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro b hb c D hc p hp
    rw [run_pure, support_pure] at hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨D, hc, Nat.le_add_right _ _⟩
  | query_bind t k ih =>
    intro b hb c D hc p hp
    rw [CostAtMost, isQueryBound_query_bind_iff] at hb
    obtain ⟨ht, hk⟩ := hb
    rw [run_query_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
    rcases t with t | q
    · rw [oracleImpl_run_inl, support_bind] at hu
      simp only [Set.mem_iUnion] at hu
      obtain ⟨w, _, hw⟩ := hu
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      simpa only [queryCost, Nat.sub_zero] using ih u (hk u) hc p hp
    · have hqcost : 1 ≤ queryCost (.inr q) := Nat.le_max_left _ _
      rcases hcache : c q with _ | v
      · rw [oracleImpl_run_inr_none hcache, support_bind] at hu
        simp only [Set.mem_iUnion] at hu
        obtain ⟨w, _, hw⟩ := hu
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨D', hD', hcard⟩ := ih u (hk u) (hc.cacheQuery q u) p hp
        refine ⟨D', hD', ?_⟩
        have hins : (insert q D).card ≤ D.card + 1 := Finset.card_insert_le _ _
        omega
      · rw [oracleImpl_run_inr_some hcache, support_pure] at hu
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        obtain ⟨D', hD', hcard⟩ := ih u (hk u) hc p hp
        exact ⟨D', hD', hcard.trans (Nat.add_le_add_left (Nat.sub_le _ _) _)⟩

/-- In particular a run from the empty cache has at most its cost in entries. -/
theorem exists_support_run_empty {α : Type} {oa : OracleComp Spec α}
    {b : ℕ} (hb : CostAtMost oa b) (p : α × CacheP)
    (hp : p ∈ support (run oa ∅)) :
    ∃ D : Finset Query, HasSupport p.2 D ∧ D.card ≤ b := by
  simpa only [Finset.card_empty, Nat.zero_add] using
    exists_support_run oa hb (hasSupport_empty) p hp

end OptimalOTS.BareLower
