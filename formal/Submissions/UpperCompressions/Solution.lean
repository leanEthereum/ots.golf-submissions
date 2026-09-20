import Submissions.UpperCompressions.ShallowWire

/-! A fully admissible oracle algorithm with verification cost at most 102. -/

namespace OptimalOTS.Challenge.UpperCompressions

/-- The forest's key-generation, signing, and verification programs on bit strings. -/
noncomputable def scheme : OracleAlgorithm.Scheme := ShallowUpperForest.Wire.scheme

/-- Perfect correctness, bounded signing failure, and the competition's resource limits. -/
theorem admissible : scheme.Admissible := ShallowUpperForest.Wire.admissible

/-- 127-bit strong unforgeability in the shared random-oracle experiment. -/
theorem secure : scheme.Secure := ShallowUpperForest.Wire.secure

/-- A bound for every input and every oracle-answer path, including rejecting inputs. -/
theorem cost : scheme.VerifyCostAtMost 102 := ShallowUpperForest.Wire.cost

end OptimalOTS.Challenge.UpperCompressions

/--
info: 'OptimalOTS.Challenge.UpperCompressions.cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.UpperCompressions.cost
