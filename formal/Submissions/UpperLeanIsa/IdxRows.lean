import Submissions.UpperLeanIsa.IdxRho

/-!
# Rows of the index cache

Ported from UpperRiscv `Rows.lean`. The index entries `m ++ η` of a cache, grouped by extended
message `m` (a *row*): the cached nonces `rowCached`, the accepted ones `rowAcc`, the accepted
ones sharing their index `rowBad`, and the non-shared accepted ones with a given index `rowHit`;
how they change when one fresh index answer is cached (`*_cacheQuery`), and the two global counts
used by the potential (`sum_rowFree_le`, `sum_rowCached_le`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option linter.constructorNameAsVariable false

attribute [local irreducible] hashBits msgBits pkBits trials Params.validSet Params.encQuery

namespace Params

variable (P : Params)






/-- Cached nonces of row `m`. -/
def rowCached (d : Cache) (m : EMessage) : Finset Nonce :=
  Finset.univ.filter fun η => (d (P.encQuery (m ++ η))).isSome

/-- Accepted nonces of row `m` with index `i` that no other entry shares. -/
def rowHit (d : Cache) (m : EMessage) (i : ℕ) : Finset Nonce :=
  Finset.univ.filter fun η => ∃ w, d (P.encQuery (m ++ η)) = some w ∧ idxOf w ∈ P.validSet ∧
    ¬ P.IdxPre d (m ++ η) (idxOf w) ∧ idxOf w = i

theorem mem_V_iff {d : Cache} {i : ℕ} :
    i ∈ P.V d ↔ ∃ u w, d (P.encQuery u) = some w ∧ idxOf w ∈ P.validSet ∧ idxOf w = i := by
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨w, hw, hi⟩ := P.mem_validInputs.1 hu
    exact ⟨u, w, hw, hi, by rw [hw, idxOfOpt_some]⟩
  · rintro ⟨u, w, hw, hi, rfl⟩
    exact P.mem_V hw hi

theorem V_sub_valid (d : Cache) : ∀ i ∈ P.V d, i ∈ P.validSet := by
  intro i hi
  obtain ⟨u, w, -, hw, rfl⟩ := (P.mem_V_iff).1 hi
  exact hw

theorem card_V_le_numValid (d : Cache) : (P.V d).card ≤ P.numValid := by
  rw [← P.card_validSet]
  exact Finset.card_le_card (P.V_sub_valid d)

theorem rowHit_subset (d : Cache) (m : EMessage) (i : ℕ) :
    P.rowHit d m i ⊆ P.rowAcc d m \ P.rowBad d m := by
  intro η hη
  simp only [Params.rowHit, Finset.mem_filter, Finset.mem_univ, true_and] at hη
  obtain ⟨w, hw, hi, hn, -⟩ := hη
  simp only [Finset.mem_sdiff, Params.rowAcc, Params.rowBad, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨w, hw, hi⟩, ?_⟩
  rintro ⟨w', hw', -, hpre⟩
  rw [hw] at hw'
  cases hw'
  exact hn hpre

theorem rowHit_eq_empty (d : Cache) (m : EMessage) {i : ℕ} (hi : i ∉ P.V d) :
    P.rowHit d m i = ∅ := by
  ext η
  simp only [Params.rowHit, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  rintro ⟨w, hw, hv, -, rfl⟩
  exact hi (P.mem_V hw hv)

/-- Every non-shared accepted entry of row `m` has its index in `P.V`. -/
theorem sum_rowHit (d : Cache) (m : EMessage) :
    ∑ i ∈ P.V d, (P.rowHit d m i).card = (P.rowAcc d m \ P.rowBad d m).card := by
  have hdisj : ∀ i ∈ P.V d, ∀ j ∈ P.V d, i ≠ j → Disjoint (P.rowHit d m i) (P.rowHit d m j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro η h1 h2
    simp only [Params.rowHit, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨w, hw, -, -, rfl⟩ := h1
    obtain ⟨w', hw', -, -, rfl⟩ := h2
    rw [hw] at hw'
    cases hw'
    exact hij rfl
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext η
  simp only [Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, -, hη⟩
    exact Finset.mem_sdiff.1 (P.rowHit_subset d m i hη)
  · rintro ⟨hacc, hbad⟩
    simp only [Params.rowAcc, Finset.mem_filter, Finset.mem_univ, true_and] at hacc
    obtain ⟨w, hw, hi⟩ := hacc
    refine ⟨idxOf w, P.mem_V hw hi, ?_⟩
    simp only [Params.rowHit, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨w, hw, hi, fun hpre => hbad ?_, rfl⟩
    simp only [Params.rowBad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hw, hi, hpre⟩

/-- Non-shared accepted entries of all rows hold distinct indices. -/
theorem sum_rowFree_le (d : Cache) :
    ∑ m, (P.rowAcc d m \ P.rowBad d m).card ≤ (P.V d).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn
    (fun p => idxOfOpt (d (P.encQuery (p.1 ++ p.2)))) ?_ ?_
  · intro p hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_univ,
      true_and, Finset.mem_sdiff, Params.rowAcc, Finset.mem_filter] at hp
    obtain ⟨⟨w, hw, hi⟩, -⟩ := hp
    show idxOfOpt (d (P.encQuery (p.1 ++ p.2))) ∈ P.V d
    rw [hw, idxOfOpt_some]
    exact P.mem_V hw hi
  · intro p hp p' hp' heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_univ,
      true_and, Finset.mem_sdiff, Params.rowAcc, Params.rowBad, Finset.mem_filter] at hp hp'
    obtain ⟨⟨w, hw, hi⟩, hn⟩ := hp
    obtain ⟨⟨w', hw', hi'⟩, -⟩ := hp'
    dsimp only at heq
    rw [hw, hw', idxOfOpt_some, idxOfOpt_some] at heq
    by_contra hne
    apply hn
    refine ⟨w, hw, hi, p'.1 ++ p'.2, ?_, w', hw', heq.symm⟩
    intro he
    apply hne
    obtain ⟨h1, h2⟩ := append_pair_inj he
    exact Sigma.ext h1.symm (heq_of_eq h2.symm)

/-- Rows partition the encoding entries. -/
theorem sum_rowCached_le (d : Cache) :
    ∑ m, (P.rowCached d m).card ≤ P.encCount d := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn (fun p => p.1 ++ p.2) ?_ ?_
  · intro p hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_univ,
      true_and, Params.rowCached, Finset.mem_filter] at hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact hp
  · intro p _ p' _ heq
    obtain ⟨h1, h2⟩ := append_pair_inj heq
    exact Sigma.ext h1 (heq_of_eq h2)

/-! ## One fresh encoding answer -/

section Step

variable {d : Cache} {m₀ : EMessage} {η₀ : Nonce} (w : BitVec hashBits)

theorem cacheQuery_enc_apply (m : EMessage) (η : Nonce) :
    (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w) (P.encQuery (m ++ η)) =
      if m = m₀ ∧ η = η₀ then some w else d (P.encQuery (m ++ η)) := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact QueryCache.cacheQuery_self _ _ _
  · refine QueryCache.cacheQuery_of_ne _ _ fun he => h ?_
    exact append_pair_inj (P.encQuery_inj he)

variable (hfresh : d (P.encQuery (m₀ ++ η₀)) = none)
include hfresh

theorem rowCached_cacheQuery (m : EMessage) :
    (P.rowCached (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w) m).card =
      (P.rowCached d m).card + if m = m₀ then 1 else 0 := by
  by_cases hm : m = m₀
  · subst hm
    rw [if_pos rfl]
    have hnot : η₀ ∉ P.rowCached d m := by
      simp [Params.rowCached, hfresh]
    have : P.rowCached (d.cacheQuery (P.encQuery (m ++ η₀)) w) m = insert η₀ (P.rowCached d m) := by
      ext η
      simp only [Params.rowCached, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        P.cacheQuery_enc_apply]
      by_cases h : η = η₀ <;> simp [h]
    rw [this, Finset.card_insert_of_notMem hnot]
  · rw [if_neg hm, add_zero]
    refine congrArg Finset.card ?_
    ext η
    simp only [Params.rowCached, Finset.mem_filter, Finset.mem_univ, true_and, P.cacheQuery_enc_apply,
      hm, false_and, if_false]

theorem rowAcc_cacheQuery (m : EMessage) :
    (P.rowAcc (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w) m).card =
      (P.rowAcc d m).card + if m = m₀ ∧ idxOf w ∈ P.validSet then 1 else 0 := by
  by_cases hm : m = m₀ ∧ idxOf w ∈ P.validSet
  · obtain ⟨rfl, hi⟩ := hm
    rw [if_pos ⟨rfl, hi⟩]
    have hnot : η₀ ∉ P.rowAcc d m := by
      simp [Params.rowAcc, hfresh]
    have : P.rowAcc (d.cacheQuery (P.encQuery (m ++ η₀)) w) m = insert η₀ (P.rowAcc d m) := by
      ext η
      simp only [Params.rowAcc, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        P.cacheQuery_enc_apply]
      by_cases h : η = η₀
      · simp [h, hi]
      · simp [h]
    rw [this, Finset.card_insert_of_notMem hnot]
  · rw [if_neg hm, add_zero]
    refine congrArg Finset.card ?_
    ext η
    simp only [Params.rowAcc, Finset.mem_filter, Finset.mem_univ, true_and, P.cacheQuery_enc_apply]
    by_cases h : m = m₀ ∧ η = η₀
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, if_true, Option.some.injEq, exists_eq_left', hfresh, reduceCtorEq,
        false_and, exists_false, iff_false]
      exact fun hi => hm ⟨rfl, hi⟩
    · simp only [h, if_false]

theorem V_cacheQuery :
    (P.V (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w)).card =
      (P.V d).card + if idxOf w ∈ P.validSet ∧ idxOf w ∉ P.V d then 1 else 0 := by
  have hmem : ∀ i, i ∈ P.V (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w) ↔
      i ∈ P.V d ∨ (idxOf w ∈ P.validSet ∧ idxOf w = i) := by
    intro i
    rw [P.mem_V_iff, P.mem_V_iff]
    constructor
    · rintro ⟨u, w', hu, hi, rfl⟩
      by_cases he : u = m₀ ++ η₀
      · subst he
        rw [QueryCache.cacheQuery_self] at hu
        cases hu
        exact Or.inr ⟨hi, rfl⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ (fun h => he (P.encQuery_inj h))] at hu
        exact Or.inl ⟨u, w', hu, hi, rfl⟩
    · rintro (⟨u, w', hu, hi, rfl⟩ | ⟨hi, rfl⟩)
      · have hne : u ≠ m₀ ++ η₀ := by
          rintro rfl
          rw [hfresh] at hu
          cases hu
        refine ⟨u, w', ?_, hi, rfl⟩
        rw [QueryCache.cacheQuery_of_ne _ _ (fun h => hne (P.encQuery_inj h))]
        exact hu
      · exact ⟨m₀ ++ η₀, w, QueryCache.cacheQuery_self _ _ _, hi, rfl⟩
  split_ifs with h
  · have : P.V (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w) = insert (idxOf w) (P.V d) := by
      ext i
      rw [hmem, Finset.mem_insert]
      constructor
      · rintro (h' | ⟨-, rfl⟩)
        · exact Or.inr h'
        · exact Or.inl rfl
      · rintro (rfl | h')
        · exact Or.inr ⟨h.1, rfl⟩
        · exact Or.inl h'
    rw [this, Finset.card_insert_of_notMem h.2]
  · rw [add_zero]
    congr 1
    ext i
    rw [hmem]
    constructor
    · rintro (h' | ⟨hi, rfl⟩)
      · exact h'
      · by_contra hn
        exact h ⟨hi, hn⟩
    · exact Or.inl

/-- A cached entry is shared after the answer only if it was shared before, or it is the new
entry (then its index was already held), or it holds the new index alone. -/
theorem rowBad_cacheQuery (m : EMessage) :
    (P.rowBad (d.cacheQuery (P.encQuery (m₀ ++ η₀)) w) m).card ≤
      (P.rowBad d m).card + (P.rowHit d m (idxOf w)).card +
        if m = m₀ ∧ idxOf w ∈ P.V d then 1 else 0 := by
  set d' := d.cacheQuery (P.encQuery (m₀ ++ η₀)) w with hd'
  have hsub : P.rowBad d' m ⊆ P.rowBad d m ∪ P.rowHit d m (idxOf w) ∪
      (if m = m₀ ∧ idxOf w ∈ P.V d then {η₀} else ∅) := by
    intro η hη
    simp only [Params.rowBad, Finset.mem_filter, Finset.mem_univ, true_and, hd',
      P.cacheQuery_enc_apply] at hη
    obtain ⟨w₁, hw₁, hi₁, u, hu, w₂, hw₂, hidx⟩ := hη
    by_cases hnew : m = m₀ ∧ η = η₀
    · obtain ⟨rfl, rfl⟩ := hnew
      simp only [and_self, if_true, Option.some.injEq] at hw₁
      subst hw₁
      apply Finset.mem_union_right
      have hu' : d (P.encQuery u) = some w₂ := by
        rwa [QueryCache.cacheQuery_of_ne _ _ (fun h => hu (P.encQuery_inj h))] at hw₂
      have hV : idxOf w ∈ P.V d := by
        rw [← hidx]; exact P.mem_V hu' (hidx ▸ hi₁)
      rw [if_pos ⟨rfl, hV⟩]
      exact Finset.mem_singleton_self _
    · rw [if_neg hnew] at hw₁
      by_cases hu0 : u = m₀ ++ η₀
      · subst hu0
        rw [QueryCache.cacheQuery_self] at hw₂
        cases hw₂
        by_cases hpre : P.IdxPre d (m ++ η) (idxOf w₁)
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          simp only [Params.rowBad, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w₁, hw₁, hi₁, hpre⟩
        · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          simp only [Params.rowHit, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w₁, hw₁, hi₁, hpre, hidx.symm⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        simp only [Params.rowBad, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨w₁, hw₁, hi₁, u, hu, w₂, ?_, hidx⟩
        rwa [QueryCache.cacheQuery_of_ne _ _ (fun h => hu0 (P.encQuery_inj h))] at hw₂
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  refine add_le_add ((Finset.card_union_le _ _)) ?_
  split_ifs <;> simp

end Step

/-! ## Queries of other lengths leave the rows unchanged -/

section Other

variable {d : Cache} {q : Query} (hq : ∀ u : EncInput, q ≠ P.encQuery u)
  (w : BitVec hashBits)
include hq

theorem enc_apply_of_ne (u : EncInput) : (d.cacheQuery q w) (P.encQuery u) = d (P.encQuery u) :=
  QueryCache.cacheQuery_of_ne _ _ (hq u).symm

theorem rowCached_of_ne (m : EMessage) : P.rowCached (d.cacheQuery q w) m = P.rowCached d m := by
  simp only [Params.rowCached, P.enc_apply_of_ne hq]

theorem rowAcc_of_ne (m : EMessage) : P.rowAcc (d.cacheQuery q w) m = P.rowAcc d m := by
  simp only [Params.rowAcc, P.enc_apply_of_ne hq]

theorem idxPre_of_ne (u : EncInput) (i : ℕ) : P.IdxPre (d.cacheQuery q w) u i ↔ P.IdxPre d u i := by
  simp only [Params.IdxPre, P.enc_apply_of_ne hq]

theorem rowBad_of_ne (m : EMessage) : P.rowBad (d.cacheQuery q w) m = P.rowBad d m := by
  simp only [Params.rowBad, P.enc_apply_of_ne hq, P.idxPre_of_ne hq]

theorem V_of_ne : P.V (d.cacheQuery q w) = P.V d := by
  ext i
  simp only [P.mem_V_iff, P.enc_apply_of_ne hq]

end Other


end Params

end OptimalOTS.LeanIsaBaseline.Layer
