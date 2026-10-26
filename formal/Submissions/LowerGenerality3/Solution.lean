import Submissions.LowerGenerality3.Proof

namespace OptimalOTS.Challenge.LowerGenerality3

/-- Every admissible, secure algorithm needs at least one compression. -/
theorem candidate : LowerBoundGenerality3 1 := OptimalOTS.LowerGenerality3.paper_lowerBound_one

end OptimalOTS.Challenge.LowerGenerality3

/--
info: 'OptimalOTS.Challenge.LowerGenerality3.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.LowerGenerality3.candidate
