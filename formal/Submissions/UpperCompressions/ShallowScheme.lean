import Submissions.UpperCompressions.ShallowCuts
import Submissions.UpperCompressions.IndexedSampling

/-!
# The shallow forest with the submitted index threshold

An injective family of `45 * 2^109` cuts instantiates the indexed DAG interface.
Every cut discloses 42 words and reconstructs the root in 101 compressions;
the message-and-nonce query brings verification to 102 compressions.
Security and the generic raw-bit interface are separate obligations.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.ShallowForest

open OptimalOTS.Dag
open Name

/-- Select distinct cuts from the certified shallow family. -/
def setsName (i : Fin IndexedAnalysis.numCuts) : Finset Name :=
  (family.equivFin.symm (Fin.castLE card_family i)).1

theorem setsName_mem (i : Fin IndexedAnalysis.numCuts) : setsName i ∈ family :=
  (family.equivFin.symm (Fin.castLE card_family i)).2

theorem setsName_injective : Function.Injective setsName := by
  intro i j h
  unfold setsName at h
  exact Fin.castLE_injective _ (family.equivFin.symm.injective (Subtype.ext h))

def forestScheme : IndexedDag.Scheme IndexedAnalysis.numCuts where
  graph := graph
  sets := fun i => fins (setsName i)
  root_not_mem := by
    intro i
    show rh.fin ∉ fins (setsName i)
    rw [mem_fins]
    exact (isCut_of_mem_family (setsName_mem i)).rh_not_mem
  no_hidden_source := by
    intro i
    exact (no_hidden_source_iff (setsName i)).mpr
      (isCut_of_mem_family (setsName_mem i)).covers
  reveal_le := by
    intro i
    show graph.revealBits (fins (setsName i)) + 128 ≤ 5504
    rw [revealBits_eq, Finset.sum_const_nat
      fun n hn => (isCut_of_mem_family (setsName_mem i)).values n hn]
    have := card_of_mem_family (setsName_mem i)
    omega
  keygen_le := by
    show graph.keygenCost ≤ 1024
    rw [graph_keygenCost]
    norm_num

theorem isCut_setsName (i : Fin IndexedAnalysis.numCuts) : IsCut (setsName i) :=
  isCut_of_mem_family (setsName_mem i)

theorem card_setsName (i : Fin IndexedAnalysis.numCuts) : (setsName i).card = 42 :=
  card_of_mem_family (setsName_mem i)

theorem cost_setsName (i : Fin IndexedAnalysis.numCuts) :
    ∑ n ∈ evaluatedSet (setsName i), n.cost = 101 :=
  cost_of_mem_family (setsName_mem i)

theorem forestScheme_reconstructCost (i : Fin IndexedAnalysis.numCuts) :
    forestScheme.graph.reconstructCost (forestScheme.sets i) = 101 := by
  change graph.reconstructCost (fins (setsName i)) = 101
  rw [reconstructCost_eq, cost_setsName]

theorem forestScheme_revealBits (i : Fin IndexedAnalysis.numCuts) :
    forestScheme.graph.revealBits (forestScheme.sets i) = 42 * 128 := by
  change graph.revealBits (fins (setsName i)) = 42 * 128
  rw [revealBits_eq, Finset.sum_const_nat fun n hn => (isCut_setsName i).values n hn,
    card_setsName]

theorem forestScheme_keygenCost : forestScheme.graph.keygenCost = 995 :=
  graph_keygenCost

theorem forestScheme_verifyCost (i : Fin IndexedAnalysis.numCuts) :
    forestScheme.verifyCost i = 102 := by
  unfold IndexedDag.Scheme.verifyCost
  rw [forestScheme_reconstructCost]
  have hidx : Dag.idxCost = 1 := by decide
  rw [hidx]

end OptimalOTS.ShallowForest
