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


/-- A well-formed payload is a 5464-bit signature whose last byte is the free digit. -/
theorem payload_wellFormed_iff (bits : List Bool) (i : Idx) :
    Forest.forestScheme.WellFormed i (Forest.decodeSignature bits).2 ↔
      bits.length = 5464 ∧ bits.drop 5456 = Forest.freeTag i := by
  unfold GScheme.WellFormed
  rw [Forest.fixed_revealBits]
  change (Payload.permute (bits.drop 128)).length = 5328 + (Forest.freeTag i).length ∧
      (Payload.permute (bits.drop 128)).drop 5328 = Forest.freeTag i ↔ _
  rw [Payload.length_permute, Forest.length_freeTag, List.length_drop,
    show (5328 : ℕ) = Payload.valueBits from rfl, Payload.drop_permute, List.drop_drop]
  unfold Payload.valueBits
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by rwa [show 128 + 5328 = 5456 from rfl] at h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by rwa [show 128 + 5328 = 5456 from rfl]⟩

end OptimalOTS.RiscvUpperForest.Wire
