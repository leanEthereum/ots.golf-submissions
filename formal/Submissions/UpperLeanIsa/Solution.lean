import Submissions.UpperLeanIsa.FlatSecurity
import Submissions.UpperLeanIsa.MachineFaithful

/-! The leanISA submission: the FLAT-42 layer scheme (`SchemeFlat.lean`, 42 Winternitz chains
on one hypercube layer, nonce-ground index), its grouped hinted-landing bytecode HL-TRI
(`MachineProgram.lean`) and the six certificate clauses. -/

namespace OptimalOTS.Challenge.UpperLeanIsa

open OptimalOTS OptimalOTS.LeanIsaBaseline.Layer

/-- The OTS, the bytecode, the announced memory size, the prover's memory-filling strategy and
the step count. -/
noncomputable def submission : LeanIsa.Submission := HLFlat.machineSubmission

/-- Admissibility and strong security of the OTS, well-formed bytecode, agreement of the honest
prover's run with the verifier, soundness against every prover-chosen memory, and at most
`1439` cycles on every completing execution. -/
theorem certificate : submission.Certificate 1439 where
  admissible := Flat.admissible
  secure := Flat.secure
  valid := HLFlat.machine_valid
  faithful := HLFlat.faithful
  sound := HLFlat.machine_sound
  cycles := HLFlat.claim_eq ▸ HLFlat.machine_cycles

/-- The bytecode slots and memory cells the prover must seed and finalize, together fewer than
`LeanIsa.maxSeededRows`. -/
theorem seeded_rows : submission.seededRows < LeanIsa.maxSeededRows :=
  HLFlat.machine_seededRows

end OptimalOTS.Challenge.UpperLeanIsa
