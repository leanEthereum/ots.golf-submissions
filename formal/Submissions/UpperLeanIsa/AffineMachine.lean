import Submissions.UpperLeanIsa.AffineFaithful
import Submissions.UpperLeanIsa.AffineConcrete

/-! The complete affine-frame submission: 103 ordinary instructions,
87 BLAKE2S instructions, and the fixed 120-cycle boundary charge. -/

namespace OptimalOTS.AffineVM

open OptimalOTS.HLFour OptimalOTS.LeanIsaBaseline.Layer
noncomputable section

abbrev affineMachine : LeanIsa.Submission :=
  machineSubmission (AffineCodec.params (layout fusionTab)) fusionTab

theorem affine_certificate : affineMachine.Certificate 1093 where
  admissible := AffineCodec.admissible (layout fusionTab)
  secure := AffineCodec.secure (layout fusionTab)
  valid := machine_valid
  faithful := faithful fusionTab_hyp concrete_compat
  sound := machine_sound fusionTab_hyp concrete_compat
  cycles := machine_cycles fusionTab_hyp

theorem affine_seededRows : affineMachine.seededRows < LeanIsa.maxSeededRows :=
  machine_seededRows

end
end OptimalOTS.AffineVM
