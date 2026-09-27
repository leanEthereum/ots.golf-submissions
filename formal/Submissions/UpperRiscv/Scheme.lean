import Submissions.UpperRiscv.FixedChoice
import Submissions.UpperRiscv.GScheme

/-!
# The bare-chain forest

A family of cuts indexed by the accepted indices, with twenty-one 144-bit and twelve 192-bit
values, followed by the free digit as an 8-bit tag. Verification costs 191 compressions.
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

/-- The free digit of an index as eight bits, least significant first. -/
def freeTag (i : Idx) : List Bool := toBits (BitVec.ofNat 8 (freeDigit i.val))

theorem length_freeTag (i : Idx) : (freeTag i).length = 8 := by
  simp [freeTag, toBits]

/-- The concrete scheme. -/
def forestScheme : GScheme where
  graph := graph
  sets := fun i => fins (setsName i)
  root_not_mem := by
    intro i
    show rh.fin ∉ fins (setsName i)
    rw [mem_fins]
    exact (fixedCut_isCut i).rh_not_mem
  no_hidden_source := by
    intro i
    exact (no_hidden_source_iff (setsName i)).mpr (fixedCut_isCut i).covers
  tag := freeTag
  reveal_le := by
    intro i
    show graph.revealBits (fins (setsName i)) + (freeTag i).length ≤ 5376
    rw [revealBits_eq, length_freeTag]
    change ∑ n ∈ cutOf (fixedChoice i), n.len + 8 ≤ 5376
    rw [reveal_cutOf _ (fixedChoice_capChoice i)]
    norm_num
  keygen_le := by
    show graph.keygenCost ≤ 2 ^ 20
    rw [graph_keygenCost]
    norm_num

theorem isCut_setsName (i : Idx) : IsCut (setsName i) :=
  fixedCut_isCut i

theorem cost_setsName (i : Idx) : ∑ n ∈ evaluatedSet (setsName i), n.cost = 190 :=
  fixedCut_cost i

/-- Every signature verifies in `191` compressions. -/
theorem forestScheme_verifyCost (i : Idx) : forestScheme.verifyCost i = 191 := by
  show idxCost + graph.reconstructCost (fins (setsName i)) = 191
  have hidx : idxCost = 1 := by decide
  rw [reconstructCost_eq, hidx]
  have h := cost_setsName i
  omega

end Forest

end OptimalOTS
