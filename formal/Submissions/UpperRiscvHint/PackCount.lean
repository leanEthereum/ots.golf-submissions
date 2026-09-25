import Submissions.UpperRiscvHint.PackFiber

/-! # The fiber count of `pack` -/

namespace OptimalOTS

attribute [local irreducible] hashBits

/-- Every set of packed indices below `2 ^ 128` is hit by exactly `2 ^ 128` answers each. -/
theorem card_pack_mem (A : Finset ℕ) (hA : ∀ n ∈ A, n < 2 ^ 128) :
    (Finset.univ.filter fun y : BitVec hashBits => pack y ∈ A).card = A.card * 2 ^ 128 := by
  have hj : ∀ y, junk y < 2 ^ 128 := junk_lt
  have hpu : ∀ i j, i < 2 ^ 128 → j < 2 ^ 128 → pack (unpack i j) = i :=
    fun i j hi _ => pack_unpack j hi
  have hju : ∀ i j, i < 2 ^ 128 → j < 2 ^ 128 → junk (unpack i j) = j :=
    fun i j _ hj => junk_unpack i hj
  generalize hM : (2 : ℕ) ^ 128 = M at hA hj hpu hju ⊢
  rw [← Finset.card_range M, ← Finset.card_product]
  refine Finset.card_nbij' (fun y => (pack y, junk y)) (fun x => unpack x.1 x.2) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨hy.2, Finset.mem_range.mpr (hj y)⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hx
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hpu _ _ (hA _ hx.1) hx.2]
    exact hx.1
  · intro y _
    exact unpack_pack_junk y
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hx
    exact Prod.ext (hpu _ _ (hA _ hx.1) hx.2) (hju _ _ (hA _ hx.1) hx.2)

end OptimalOTS
