import Submissions.UpperRiscv.Wire
import Submissions.UpperRiscv.Program

/-! Exact signature layout used by the assembly refinement. -/

noncomputable section
open scoped Classical

namespace OptimalOTS.Forest

open OptimalOTS.Dag


theorem fixed_revealBits (i : Idx) :
    forestScheme.graph.revealBits (forestScheme.sets i) = 5328 := by
  change graph.revealBits (fins (cutOf (fixedChoice i))) = 5328
  rw [revealBits_eq, reveal_cutOf _ (fixedChoice_capChoice i)]

end OptimalOTS.Forest

namespace OptimalOTS.RiscvUpperForest.Wire

open OptimalOTS.Dag


/-- A well-formed payload is a 5456-bit signature. -/
theorem payload_wellFormed_iff (bits : List Bool) (i : Idx) :
    Forest.forestScheme.WellFormed i (Forest.decodeSignature bits).2 ↔ bits.length = 5456 := by
  unfold GScheme.WellFormed
  rw [Forest.fixed_revealBits]
  change (Payload.permute (bits.drop 128)).length = 5328 + ([] : List Bool).length ∧
      (Payload.permute (bits.drop 128)).drop 5328 = [] ↔ _
  rw [Payload.length_permute, List.length_drop, List.drop_eq_nil_iff, Payload.length_permute,
    List.length_drop]
  constructor
  · rintro ⟨h1, -⟩; simp at h1; omega
  · intro h; simp; omega
end OptimalOTS.RiscvUpperForest.Wire
