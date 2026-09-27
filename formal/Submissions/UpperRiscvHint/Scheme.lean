import Submissions.UpperRiscvHint.FixedChoice
import Submissions.UpperRiscvHint.GScheme

/-!
# The bare-chain forest

A family of cuts indexed by the accepted indices, with thirteen 192-bit and twenty 144-bit
values. Verification costs 180 compressions.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

open OptimalOTS.Dag


namespace Forest

open Name

/-- A fixed disclosure layout, with chain positions decoded from the index. -/
def setsName (i : Idx) : Finset Name := cutOf (fixedChoice i)

theorem setsName_injective : Function.Injective setsName := fixedCut_injective

/-- The concrete scheme. -/
def forestScheme : GScheme where
  graph := graph
  sets := fun i => fins (setsName i)
  no_hidden_source := by
    intro i
    exact (no_hidden_source_iff (setsName i)).mpr (fixedCut_isCut i).covers
  reveal_le := by
    intro i
    show graph.revealBits (fins (setsName i)) ≤ 5376
    rw [revealBits_eq]
    change ∑ n ∈ cutOf (fixedChoice i), n.len ≤ 5376
    rw [reveal_cutOf]
  keygen_le := by
    show graph.keygenCost ≤ 2 ^ 20
    rw [graph_keygenCost]
    norm_num

theorem isCut_setsName (i : Idx) : IsCut (setsName i) :=
  fixedCut_isCut i

theorem cost_setsName (i : Idx) : ∑ n ∈ evaluatedSet (setsName i), n.cost = 179 :=
  fixedCut_cost i

/-- Every signature verifies in `180` compressions. -/
theorem forestScheme_verifyCost (i : Idx) : forestScheme.verifyCost i = 180 := by
  show idxCost + graph.reconstructCost (fins (setsName i)) = 180
  have hidx : idxCost = 1 := by decide
  rw [reconstructCost_eq, hidx]
  have h := cost_setsName i
  omega

end Forest

end OptimalOTS
