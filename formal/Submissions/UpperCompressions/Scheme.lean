import Submissions.UpperCompressions.Cuts

/-!
# The concrete scheme as a `Scheme`

`forestScheme` is the 54-chain forest (the paper's forest with six subtrees): the graph of
`Forest.Names`, with the `2 ^ 115` disclosure sets chosen injectively from the family of
`Forest.Cuts`.  Every signature
verifies in `104` compressions (`forestScheme_verifyCost`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name

/-- The disclosure sets, indexed injectively by `Fin (2 ^ 115)`. -/
def setsName (i : Fin (2 ^ 115)) : Finset Name :=
  (family.equivFin.symm (Fin.castLE card_family i)).1

theorem setsName_mem (i : Fin (2 ^ 115)) : setsName i ∈ family :=
  (family.equivFin.symm (Fin.castLE card_family i)).2

theorem setsName_injective : Function.Injective setsName := by
  intro i j h
  unfold setsName at h
  exact Fin.castLE_injective _ (family.equivFin.symm.injective (Subtype.ext h))

/-- The concrete scheme. -/
def forestScheme : Scheme where
  graph := graph
  sets := fun i => fins (setsName i)
  root_not_mem := by
    intro i
    show rh.fin ∉ fins (setsName i)
    rw [mem_fins]
    exact (isCut_of_mem_family (setsName_mem i)).rh_not_mem
  no_hidden_source := by
    intro i
    exact (no_hidden_source_iff (setsName i)).mpr (isCut_of_mem_family (setsName_mem i)).covers
  reveal_le := by
    intro i
    show graph.revealBits (fins (setsName i)) + 128 ≤ 5504
    rw [revealBits_eq, Finset.sum_const_nat fun n hn => (isCut_of_mem_family (setsName_mem i)).values n hn]
    have := card_le_of_mem_family (setsName_mem i)
    omega
  keygen_le := by
    show graph.keygenCost ≤ 1024
    rw [graph_keygenCost]
    norm_num

theorem isCut_setsName (i : Fin (2 ^ 115)) : IsCut (setsName i) :=
  isCut_of_mem_family (setsName_mem i)

theorem cost_setsName (i : Fin (2 ^ 115)) : ∑ n ∈ evaluatedSet (setsName i), n.cost = 103 :=
  cost_of_mem_family (setsName_mem i)

/-- Every signature verifies in `104` compressions. -/
theorem forestScheme_verifyCost (i : Fin numCuts) : forestScheme.verifyCost i = 104 := by
  show idxCost + graph.reconstructCost (fins (setsName i)) = 104
  have hidx : idxCost = 1 := by decide
  rw [reconstructCost_eq, hidx]
  have h := cost_setsName i
  omega

end Forest

end OptimalOTS
