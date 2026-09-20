import Submissions.LowerGenerality3.Assemble

namespace OptimalOTS.Challenge.LowerGenerality3

/-- Every admissible, secure algorithm needs at least two compressions. -/
theorem candidate : LowerBoundGenerality3 2 := OptimalOTS.LowerGenerality3.paper_lowerBound_two

end OptimalOTS.Challenge.LowerGenerality3

/--
info: 'OptimalOTS.Challenge.LowerGenerality3.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.LowerGenerality3.candidate
