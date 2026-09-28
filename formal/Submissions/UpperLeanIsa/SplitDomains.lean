import Submissions.UpperLeanIsa.FourInputs

/-! Concrete finite domain labels for the split four/five-child graph. -/
namespace OptimalOTS.LeanIsaBaseline.Layer.FourFusion
open OptimalOTS
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def mdIndex (k : Fin 42) : Fin 47 := ![13,3,5,17,17,17,17,6,1,2,13,13,13,13,13,13,13,13,13,17,17,17,13,13,17,17,17,13,13,17,17,17,13,13,7,8,13,13,13,9,10,13] k
def tagIndex (k : Fin 42) : Fin 47 := ![1,1,1,1,2,3,4,1,1,1,1,1,1,1,1,1,1,1,1,5,6,7,1,1,8,9,10,1,1,11,12,13,1,1,1,1,1,1,1,1,1,1] k
def rootIndex (_r : Fin 1) : Fin 47 := 4

theorem mdIndex_reserved : ∀ k, mdIndex k ≠ 0 ∧ mdIndex k ≠ 16 ∧
    ∀ r, mdIndex k ≠ rootIndex r := by decide
theorem rootIndex_reserved : ∀ r, rootIndex r ≠ 0 ∧ rootIndex r ≠ 16 := by decide
theorem mdIndex_bounds : ∀ k, (mdIndex k).val ≤ 14 ∨ (mdIndex k).val = 17 := by decide
theorem tagIndex_bounds : ∀ k, (tagIndex k).val ≤ 13 := by decide

/-- Boolean form of the metadata-kind check: only the 42 × 42 parent pairs are scanned,
since `owner` already determines the child indices. -/
def kindCheck : Bool :=
  (List.finRange 42).all fun k => (List.finRange 42).all fun k' =>
    match owner k, owner k' with
    | some u, some v => !(Nat.beq (mdIndex k).val (mdIndex k').val) || five u == five v
    | _, _ => true

/-- Boolean form of the metadata/tag location check. -/
def locationCheck : Bool :=
  (List.finRange 42).all fun k => (List.finRange 42).all fun k' =>
    match owner k, owner k' with
    | some u, some _ => !(Nat.beq (mdIndex k).val (mdIndex k').val) ||
        !(five u || Nat.beq (tagIndex k).val (tagIndex k').val) || Nat.beq k.val k'.val
    | _, _ => true

theorem kindCheck_eq : kindCheck = true := by decide +kernel
theorem locationCheck_eq : locationCheck = true := by decide +kernel

theorem indices_kind : ∀ (k k' : Fin 42) (u v : Fin 8),
    owner k = some u → owner k' = some v → mdIndex k = mdIndex k' →
    five u = five v := by
  intro k k' u v hu hv hm
  have h := List.all_eq_true.1 (List.all_eq_true.1 kindCheck_eq k (List.mem_finRange k)) k'
    (List.mem_finRange k')
  rw [hu, hv] at h
  simpa [hm] using h

theorem indices_location : ∀ (k k' : Fin 42) (u v : Fin 8),
    owner k = some u → owner k' = some v → mdIndex k = mdIndex k' →
    (five u = true ∨ tagIndex k = tagIndex k') → k = k' := by
  intro k k' u v hu hv hm hf
  have h := List.all_eq_true.1 (List.all_eq_true.1 locationCheck_eq k (List.mem_finRange k)) k'
    (List.mem_finRange k')
  rw [hu, hv] at h
  have ht : (tagIndex k).val = (tagIndex k').val → k = k' := by
    intro ht; simpa [hm, ht, Fin.ext_iff] using h
  rcases hf with hf | hf
  · simpa [hm, hf, Fin.ext_iff] using h
  · exact ht (congrArg Fin.val hf)

/-- Five-child packets identify their parent by metadata alone. Four-child packets
also use word five as a tag; the metadata separates these two packet formats. -/
theorem packet_location (P : Params)
    (hmd : ∀ a b, P.fusedMd a = P.fusedMd b → mdIndex a = mdIndex b)
    (htag : ∀ a b, P.fusedTag a = P.fusedTag b → tagIndex a = tagIndex b)
    (k k' : Fin 42) (u v : Fin 8) (t t' : Tops) (x y : Word)
    (ho : owner k = some u) (ho' : owner k' = some v)
    (h : P.groupInput t u k 0 x = P.groupInput t' v k' 0 y) : k = k' := by
  have he := packet_injective h
  have hm : P.fusedMd k = P.fusedMd k' := congrFun he 6
  have hmi := hmd k k' hm
  have hf := indices_kind k k' u v ho ho' hmi
  apply indices_location k k' u v ho ho' hmi
  by_cases hfu : five u = true
  · exact Or.inl hfu
  · right
    have hfv : ¬ five v = true := by rwa [← hf]
    have h5 := congrFun he 5
    have ht : P.fusedTag k = P.fusedTag k' := by
      simpa [Params.groupInput, fusionWords, hfu, hfv] using h5
    exact htag k k' ht

end OptimalOTS.LeanIsaBaseline.Layer.FourFusion
