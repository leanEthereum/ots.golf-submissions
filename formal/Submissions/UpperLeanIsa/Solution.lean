import Submissions.UpperLeanIsa.Group3Security
import Submissions.UpperLeanIsa.MachineGroup3

/-! The leanISA submission: the HL-GROUP-3 layer scheme (`SchemeGroup3.lean`: a free chain and 13
groups of 3 or 4 chains whose digits are read from (cost, lex) tables with aliased entries of the
index's group fields, on the layer `88`, rarest-cut signing), its uniform-cost hinted-landing bytecode
(`MachineProgram.lean`) and the six certificate clauses. -/

namespace OptimalOTS.Challenge.UpperLeanIsa

open OptimalOTS OptimalOTS.LeanIsaBaseline.Layer

/-- The OTS, the bytecode, the announced memory size, the prover's memory-filling strategy and
the step count. -/
noncomputable def submission : LeanIsa.Submission := HLG3.g3machine

/-- Admissibility and strong security of the OTS, well-formed bytecode, agreement of the honest
prover's run with the verifier, soundness against every prover-chosen memory, and at most
`1209` cycles on every completing execution. -/
theorem certificate : submission.Certificate 1209 where
  admissible := Group3.admissible
  secure := Group3.secure
  valid := HLG3.g3_valid
  faithful := HLG3.g3_faithful
  sound := HLG3.g3_sound
  cycles := HLG3.g3_cycles

/-- The bytecode slots and memory cells the prover must seed and finalize, together fewer than
`LeanIsa.maxSeededRows`. -/
theorem seeded_rows : submission.seededRows < LeanIsa.maxSeededRows := HLG3.g3_seededRows

end OptimalOTS.Challenge.UpperLeanIsa
