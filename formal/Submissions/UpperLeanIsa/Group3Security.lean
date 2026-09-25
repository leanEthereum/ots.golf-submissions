import Submissions.UpperLeanIsa.Group3Hyp
import Submissions.UpperLeanIsa.Security

/-!
# Concrete admissibility and strict 127-bit security

Group3.admissible supplies all scheme requirements. Group3.secure bounds every attack below
B/2^127. For B ≤ 2^127 the adaptive proof gives 2^-500 + (B-keygenCost)/2^127: the signer keeps
the rarest accepted class of 2^19 trials, every non-index query is charged 2^-128 per compression,
the index queries and signing are paid by the budget term of the tier schedule
`Tier.g1281Sched`, and the unavoidable key-generation cost of 1268 compressions supplies the
strict inequality.
-/

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Group3

/-- **Strong unforgeability of HL-GROUP-3.** -/
theorem secure : scheme.Secure := params.secure hyp

end Group3

end OptimalOTS.LeanIsaBaseline.Layer

/--
info: 'OptimalOTS.LeanIsaBaseline.Layer.Group3.secure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.LeanIsaBaseline.Layer.Group3.secure

/--
info: 'OptimalOTS.LeanIsaBaseline.Layer.Group3.admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.LeanIsaBaseline.Layer.Group3.admissible
