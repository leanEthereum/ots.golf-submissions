import Submissions.UpperCompressions.ProofBundle04
import Submissions.UpperCompressions.ProofBundle13

/- Original module: Submissions.UpperCompressions.Solution; SHA256 abf8100627d21595652936160df4ef44cbc58b906f3f5d47c5eec3e352d40e91. -/

namespace OptimalOTS.Challenge.UpperCompressions

noncomputable def scheme : OracleAlgorithm.Scheme :=
  WeightedConstruction.WideWire.scheme

theorem admissible : scheme.Admissible :=
  WeightedConstruction.WideHonest.admissible

theorem secure : scheme.Secure :=
  WeightedConstruction.WideSecure.raw_secure

theorem cost : scheme.VerifyCostAtMost 92 :=
  WeightedConstruction.WideWire.cost

end OptimalOTS.Challenge.UpperCompressions

