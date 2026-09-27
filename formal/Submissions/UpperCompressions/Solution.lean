import Submissions.UpperCompressions.LongChain91Secure

namespace OptimalOTS.Challenge.UpperCompressions

noncomputable def scheme : OracleAlgorithm.Scheme :=
  WeightedConstruction.LongChain91.wireScheme

theorem admissible : scheme.Admissible :=
  WeightedConstruction.LongChain91.wire_admissible

theorem secure : scheme.Secure :=
  WeightedConstruction.LongChain91Secure.raw_secure

theorem cost : scheme.VerifyCostAtMost 89 :=
  WeightedConstruction.LongChain91.wire_cost

end OptimalOTS.Challenge.UpperCompressions
