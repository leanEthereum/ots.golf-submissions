import Submissions.UpperCompressions.IndexedSampling

/-! Raw `CostAtMost` padding: every signing outcome can be reached after the
maximum number of trials. Oracle-answer consistency is deliberately irrelevant
because the protected resource predicate quantifies over all answer paths. -/

open OracleSpec OracleComp
open scoped Classical

noncomputable section

namespace OptimalOTS
namespace IndexedAnalysis
namespace SigningReserve

open OptimalOTS.Dag
local notation "M" => OptimalOTS.IndexedAnalysis.numCuts

attribute [local irreducible] CostAtMost hashBits msgBits nonceBits idxBits trials

private theorem fresh_card_insert (tried : Finset Nonce) (η : Nonce)
    (hη : η ∈ Finset.univ \ tried) :
    (Finset.univ \ insert η tried).card + 1 = (Finset.univ \ tried).card := by
  have heq : Finset.univ \ insert η tried = (Finset.univ \ tried).erase η := by
    ext x
    simp
  rw [heq, Finset.card_erase_of_mem hη]
  have := Finset.card_pos.mpr ⟨η, hη⟩
  omega

private theorem nonceOf_surjective (tried : Finset Nonce)
    (hc : 0 < (Finset.univ \ tried).card) (η : Nonce)
    (hη : η ∈ Finset.univ \ tried) :
    ∃ j, nonceOf tried hc j = η := by
  have hcast : (Finset.univ \ tried).card - 1 + 1 = (Finset.univ \ tried).card := by omega
  let j := Fin.cast hcast.symm ((Finset.univ \ tried).equivFin ⟨η, hη⟩)
  refine ⟨j, ?_⟩
  simp [nonceOf, j]

private theorem cost_at_nonce {β : Type} (m : Message) (k : ℕ)
    (tried : Finset Nonce) (η : Nonce) (hη : η ∈ Finset.univ \ tried)
    (kont : Option (Nonce × Fin M) → OracleComp Spec β) {b : ℕ}
    (hB : CostAtMost (signIdxLoop m (k + 1) tried >>= kont) b) :
    1 ≤ b ∧ ∀ w, CostAtMost (afterHash m k tried η w >>= kont) (b - 1) := by
  have hc : 0 < (Finset.univ \ tried).card := Finset.card_pos.mpr ⟨η, hη⟩
  rw [signIdxLoop_succ m k tried hc] at hB
  obtain ⟨j, hj⟩ := nonceOf_surjective tried hc η hη
  have hbody := costAtMost_inl_bind _ _ kont hB j
  rw [hj] at hbody
  have hstep := costAtMost_inr_bind _ _ kont hbody
  have hcost : queryCost (.inr (encQuery (m ++ η))) = 1 := by
    norm_num [queryCost, encQuery, blockCost, msgBits, nonceBits, blockBits]
  simpa only [hcost] using hstep

/-- Force all remaining trials to reject, reserving their full cost even when
the original execution would have returned early. -/
theorem none_reserve {β : Type} (reject : BitVec hashBits)
    (hreject : ¬ idxOf reject < M) (m : Message)
    (kont : Option (Nonce × Fin M) → OracleComp Spec β) :
    ∀ (k : ℕ) (tried : Finset Nonce) (b : ℕ),
      k ≤ (Finset.univ \ tried).card →
      CostAtMost (signIdxLoop m k tried >>= kont) b →
      k ≤ b ∧ CostAtMost (kont none) (b - k) := by
  intro k
  induction k with
  | zero =>
      intro tried b _ hB
      simpa only [signIdxLoop, pure_bind, Nat.sub_zero] using And.intro (Nat.zero_le b) hB
  | succ k ih =>
      intro tried b hcard hB
      have hc : 0 < (Finset.univ \ tried).card := by omega
      obtain ⟨η, hη⟩ := Finset.card_pos.mp hc
      obtain ⟨hb, hw⟩ := cost_at_nonce m k tried η hη kont hB
      have hrej := hw reject
      simp only [afterHash, dif_neg hreject] at hrej
      have hcard' : k ≤ (Finset.univ \ insert η tried).card := by
        have := fresh_card_insert tried η hη
        omega
      obtain ⟨hk, hkont⟩ := ih (insert η tried) (b - 1) hcard' hrej
      refine ⟨by omega, ?_⟩
      have hsub : b - 1 - k = b - (k + 1) := by omega
      simpa only [hsub] using hkont

/-- Force rejections until the final trial, then return the prescribed fresh
nonce and prescribed accepted index. -/
theorem some_reserve {β : Type} (reject : BitVec hashBits)
    (hreject : ¬ idxOf reject < M) (m : Message)
    (kont : Option (Nonce × Fin M) → OracleComp Spec β)
    (η : Nonce) (i : Fin M) (accept : BitVec hashBits)
    (haccept : idxOf accept = i.val) :
    ∀ (k : ℕ) (tried : Finset Nonce) (b : ℕ),
      k + 1 ≤ (Finset.univ \ tried).card → η ∉ tried →
      CostAtMost (signIdxLoop m (k + 1) tried >>= kont) b →
      CostAtMost (kont (some (η, i))) (b - (k + 1)) := by
  intro k
  induction k with
  | zero =>
      intro tried b _ hη hB
      have hη' : η ∈ Finset.univ \ tried := by simp [hη]
      have hw := (cost_at_nonce m 0 tried η hη' kont hB).2 accept
      have ha : idxOf accept < M := haccept ▸ i.isLt
      simp only [afterHash, dif_pos ha, pure_bind] at hw
      have hi : (⟨idxOf accept, ha⟩ : Fin M) = i := Fin.ext haccept
      simpa only [hi, Nat.zero_add] using hw
  | succ k ih =>
      intro tried b hcard hη hB
      have hη' : η ∈ Finset.univ \ tried := by simp [hη]
      have hc : 0 < ((Finset.univ \ tried).erase η).card := by
        rw [Finset.card_erase_of_mem hη']
        omega
      obtain ⟨ζ, hζ⟩ := Finset.card_pos.mp hc
      obtain ⟨hne, hζ'⟩ := Finset.mem_erase.mp hζ
      obtain ⟨hb, hw⟩ := cost_at_nonce m (k + 1) tried ζ hζ' kont hB
      have hrej := hw reject
      simp only [afterHash, dif_neg hreject] at hrej
      have hcard' : k + 1 ≤ (Finset.univ \ insert ζ tried).card := by
        have := fresh_card_insert tried ζ hζ'
        omega
      have hηnew : η ∉ insert ζ tried := by simp [hη, Ne.symm hne]
      have hkont := ih (insert ζ tried) (b - 1) hcard' hηnew hrej
      have hsub : b - 1 - (k + 1) = b - (k + 1 + 1) := by omega
      simpa only [hsub] using hkont

/-- A portable interface: only existence of accepted/rejected oracle answers
and enough nonce choices is needed; no random-oracle cache hypotheses occur. -/
theorem signIdx_reserve_of_answers {β : Type}
    (reject : BitVec hashBits) (hreject : ¬ idxOf reject < M)
    (accept : Fin M → BitVec hashBits) (haccept : ∀ i, idxOf (accept i) = i.val)
    (htrials : 0 < trials) (hspace : trials ≤ Fintype.card Nonce)
    (m : Message) (kont : Option (Nonce × Fin M) → OracleComp Spec β) {b : ℕ}
    (hB : CostAtMost (signIdx m >>= kont) b) :
    trials ≤ b ∧ ∀ r, CostAtMost (kont r) (b - trials) := by
  have hcard : trials ≤ (Finset.univ \ (∅ : Finset Nonce)).card := by
    simpa using hspace
  have hloop : CostAtMost (signIdxLoop m trials ∅ >>= kont) b := hB
  obtain ⟨hle, hnone⟩ := none_reserve reject hreject m kont trials ∅ b hcard hloop
  refine ⟨hle, ?_⟩
  intro r
  rcases r with _ | ⟨η, i⟩
  · exact hnone
  · have ht : trials - 1 + 1 = trials := by omega
    have hs := some_reserve reject hreject m kont η i (accept i) (haccept i)
      (trials - 1) ∅ b (by simpa only [ht] using hcard) (by simp)
      (by simpa only [ht] using hloop)
    simpa only [ht] using hs


private theorem idxOf_ofNat (i : ℕ) (hi : i < 2 ^ idxBits) :
    idxOf (BitVec.ofNat hashBits i) = i := by
  have hp : 2 ^ idxBits ≤ 2 ^ hashBits := by norm_num [idxBits, hashBits]
  have hh : i < 2 ^ hashBits := hi.trans_le hp
  simp only [idxOf, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt hi]

/-- The concrete existing signer reserves all `trials` compressions for every
continuation outcome, including `none`. -/
theorem signIdx_reserve {β : Type}
    (m : Message) (kont : Option (Nonce × Fin M) → OracleComp Spec β) {b : ℕ}
    (hB : CostAtMost (signIdx m >>= kont) b) :
    trials ≤ b ∧ ∀ r, CostAtMost (kont r) (b - trials) := by
  have hM : M < 2 ^ idxBits := by norm_num [numCuts, idxBits]
  apply signIdx_reserve_of_answers (BitVec.ofNat hashBits M) ?_
    (fun i => BitVec.ofNat hashBits i.val) ?_ ?_ ?_ m kont hB
  · rw [idxOf_ofNat M hM]
    exact Nat.lt_irrefl _
  · intro i
    exact idxOf_ofNat i.val (i.isLt.trans hM)
  · norm_num [trials, idxCost, signBudget, blockCost, msgBits, nonceBits, blockBits]
  · norm_num [Nonce, Fintype.card_bitVec, nonceBits, trials, idxCost, signBudget, blockCost, msgBits, blockBits]

#print axioms signIdx_reserve

#print axioms none_reserve
#print axioms some_reserve
#print axioms signIdx_reserve_of_answers

end SigningReserve
end IndexedAnalysis
end OptimalOTS
