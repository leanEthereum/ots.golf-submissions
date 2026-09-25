import Submissions.UpperLeanIsa.Group3Hyp
import Submissions.UpperLeanIsa.Security

/-!
# Concrete admissibility and strict 127-bit security

Group3.admissible supplies all scheme requirements. Group3.secure bounds every attack below
B/2^127. For B ≤ 2^127 the adaptive proof first gives badW + (B-keygenCost)/2^127 with
badW ≤ 672/2^128 (the records that are not good); the unavoidable key-generation cost of
1326 compressions (2652/2^128 at the Tier B rate) supplies the strict inequality.
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
