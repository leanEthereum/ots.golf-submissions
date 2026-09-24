import Submissions.UpperLeanIsa.FlatHyp
import Submissions.UpperLeanIsa.Security

/-!
# Admissibility and strong unforgeability of HL-FLAT-A

`Flat.admissible : Flat.scheme.Admissible` (all eight fields, with the concrete budgets
`keygen 622`, `sign 2 ^ 20`, `verify 226`) and `Flat.secure : Flat.scheme.Secure`: every attacker
whose experiment costs at most `B` compressions on every path wins with probability at most
`(19/20) · B / 2 ^ 127 < B / 2 ^ 127`.
-/

namespace OptimalOTS.LeanIsaBaseline.Layer

namespace Flat

/-- **Strong unforgeability of HL-FLAT-A.** -/
theorem secure : scheme.Secure := params.secure hyp

end Flat

end OptimalOTS.LeanIsaBaseline.Layer

/--
info: 'OptimalOTS.LeanIsaBaseline.Layer.Flat.secure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.LeanIsaBaseline.Layer.Flat.secure

/--
info: 'OptimalOTS.LeanIsaBaseline.Layer.Flat.admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.LeanIsaBaseline.Layer.Flat.admissible
