import Submissions.UpperLeanIsa.LayerBits

/-! The effective index discards bit zero of the raw 128-bit hash slice. -/

namespace OptimalOTS.LeanIsaBaseline.Layer

set_option linter.constructorNameAsVariable false

abbrev RawIndex := BitVec 128
abbrev Index := BitVec 127

def effective (w : RawIndex) : Index := w.extractLsb' 1 127

def indexSlice {n : ℕ} (w : BitVec n) : Index := w.extractLsb' 1 127

def indexRest (w : BitVec 256) : BitVec 129 :=
  w.extractLsb' 128 128 ++ w.extractLsb' 0 1

def joinIndex (i : Index) (r : BitVec 129) : BitVec 256 :=
  (r.extractLsb' 1 128 ++ i) ++ r.extractLsb' 0 1

theorem indexSlice_effective (w : BitVec 256) :
    indexSlice w = effective (w.extractLsb' 0 128) := by
  unfold indexSlice effective
  exact (BitVec.extractLsb'_extractLsb'_of_le (by decide)).symm

theorem joinIndex_split (w : BitVec 256) : joinIndex (indexSlice w) (indexRest w) = w := by
  unfold joinIndex indexSlice indexRest
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 128 = 1 + 127)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 1 = 0 + 1)]
  exact BitVec.extractLsb'_eq_self

theorem indexSlice_join (i : Index) (r : BitVec 129) : indexSlice (joinIndex i r) = i := by
  unfold indexSlice joinIndex
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 1 ≤ 1)]
  exact BitVec.extractLsb'_append_eq_right

theorem indexRest_join (i : Index) (r : BitVec 129) : indexRest (joinIndex i r) = r := by
  unfold indexRest joinIndex
  simp only [BitVec.extractLsb'_append_eq_ite]
  norm_num

theorem card_indexSlice (p : Index → Prop) [DecidablePred p] :
    (Finset.univ.filter fun w : BitVec 256 => p (indexSlice w)).card =
      (Finset.univ.filter p).card * 2 ^ 129 := by
  have hu : (Finset.univ : Finset (BitVec 129)).card = 2 ^ 129 := by
    rw [Finset.card_univ, Fintype.card_bitVec]
  rw [← hu, ← Finset.card_product]
  refine Finset.card_nbij' (fun w => (indexSlice w, indexRest w))
    (fun x => joinIndex x.1 x.2) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
    simp [hw]
  · intro x hx
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_ofPred_eq, Finset.coe_univ, Set.mem_univ, and_true] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      indexSlice_join]
    exact hx
  · intro w _
    exact joinIndex_split w
  · intro x _
    exact Prod.ext (indexSlice_join _ _) (indexRest_join _ _)

end OptimalOTS.LeanIsaBaseline.Layer
