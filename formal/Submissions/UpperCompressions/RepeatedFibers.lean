import Submissions.UpperCompressions.IndexedRows

/-! A finite function has at most twice its number of repeated image values
many elements in nonsingleton fibers. No cryptographic assumptions are used. -/

open scoped BigOperators

namespace TightIndex

noncomputable section
open scoped Classical

/-- Elements of `s` whose image is shared by another element of `s`. -/
def repeated {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) : Finset α :=
  s.filter fun x => ∃ y ∈ s, y ≠ x ∧ f y = f x

theorem mem_repeated {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (x : α) :
    x ∈ repeated s f ↔ x ∈ s ∧ ∃ y ∈ s, y ≠ x ∧ f y = f x := by
  exact Finset.mem_filter

/-- Fiber counting: each nonsingleton fiber contributes at most twice its
cardinality minus one. Singleton fibers contribute zero bad elements. -/
theorem repeated_card_le_twice_excess {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (repeated s f).card ≤ 2 * (s.card - (s.image f).card) := by
  classical
  let B := repeated s f
  let V := s.image f
  have hBs : B ⊆ s := Finset.filter_subset _ _
  have hs : s.card = ∑ y ∈ V, (s.filter fun x => f x = y).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hb : B.card = ∑ y ∈ V, (B.filter fun x => f x = y).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hBs hx, rfl⟩
  have hfiber : ∀ y ∈ V,
      (B.filter fun x => f x = y).card + 2 ≤
        2 * (s.filter fun x => f x = y).card := by
    intro y hy
    let F := s.filter fun x => f x = y
    let G := B.filter fun x => f x = y
    have hGF : G ⊆ F := by
      intro x hx
      obtain ⟨hxB, hxy⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hBs hxB, hxy⟩
    have hFpos : 1 ≤ F.card := by
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      exact Finset.one_le_card.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxy⟩⟩
    by_cases hFtwo : 2 ≤ F.card
    · have hcard : G.card ≤ F.card := Finset.card_le_card hGF
      change G.card + 2 ≤ 2 * F.card
      omega
    · have hGempty : G = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨hxB, hxy⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxs, z, hzs, hzx, hzxval⟩ := Finset.mem_filter.mp hxB
        have hxF : x ∈ F := Finset.mem_filter.mpr ⟨hxs, hxy⟩
        have hzF : z ∈ F := Finset.mem_filter.mpr ⟨hzs, hzxval.trans hxy⟩
        have hpair : ({x, z} : Finset α) ⊆ F := by
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact hxF
          · exact hzF
        have hcard := Finset.card_le_card hpair
        have hpaircard : ({x, z} : Finset α).card = 2 := by simp [Ne.symm hzx]
        rw [hpaircard] at hcard
        exact hFtwo hcard
      change G.card + 2 ≤ 2 * F.card
      rw [hGempty, Finset.card_empty]
      omega
  have hsum := Finset.sum_le_sum hfiber
  have hsumB : (∑ y ∈ V, ((B.filter fun x => f x = y).card + 2)) = B.card + V.card * 2 := by
    rw [Finset.sum_add_distrib, ← hb]
    simp
  have hsumS : (∑ y ∈ V, 2 * (s.filter fun x => f x = y).card) = 2 * s.card := by
    rw [← Finset.mul_sum, ← hs]
  rw [hsumB, hsumS] at hsum
  change B.card ≤ 2 * (s.card - V.card)
  omega

#print axioms repeated_card_le_twice_excess

end
end TightIndex

namespace TightIndex

open OptimalOTS OptimalOTS.Dag OptimalOTS.IndexedAnalysis

noncomputable section
open scoped Classical

attribute [local irreducible] hashBits msgBits nonceBits OptimalOTS.IndexedAnalysis.idxBits
  OptimalOTS.IndexedAnalysis.numCuts

/-- The accepted-class label associated with a cached encoding input. -/
def cacheLabel (d : Cache) (u : EncInput) : ℕ :=
  ((d (encQuery u)).map idxOf).getD 0

/-- Every bad entry in a selected message row belongs to a nonsingleton fiber
of the complete accepted encoding cache. -/
theorem rowBad_card_le_twice_excess (d : Cache) (m : Message) :
    (rowBad d m).card ≤ 2 * ((validSet d).card - (V d).card) := by
  classical
  have hmaps : Set.MapsTo (fun η : Nonce => m ++ η) ↑(rowBad d m)
      ↑(repeated (validSet d) (cacheLabel d)) := by
    intro η hη
    obtain ⟨w, hw, hi, hpre⟩ := (Finset.mem_filter.mp hη).2
    obtain ⟨u', hne, w', hw', heq⟩ := hpre
    apply (mem_repeated (validSet d) (cacheLabel d) (m ++ η)).mpr
    refine ⟨?_, u', ?_, hne, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w', hw', heq ▸ hi⟩
    · simp [cacheLabel, hw, hw', heq]
  have hinj : Set.InjOn (fun η : Nonce => m ++ η) ↑(rowBad d m) := by
    intro η _ η' _ he
    exact (append_pair_inj he).2
  calc
    (rowBad d m).card ≤ (repeated (validSet d) (cacheLabel d)).card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ 2 * ((validSet d).card - (V d).card) := by
      change (repeated (validSet d) (cacheLabel d)).card ≤
        2 * ((validSet d).card - ((validSet d).image (cacheLabel d)).card)
      exact repeated_card_le_twice_excess (validSet d) (cacheLabel d)

#print axioms rowBad_card_le_twice_excess

end
end TightIndex
