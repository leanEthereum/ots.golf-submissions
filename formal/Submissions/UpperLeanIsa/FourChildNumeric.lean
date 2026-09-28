import Submissions.UpperLeanIsa.SplitNumeric

namespace OptimalOTS.LeanIsaBaseline.Layer.FourChildNumeric

/-- The exact 440-tier schedule for the split1096 codec. -/
abbrev schedule := SplitNumeric.schedule

theorem schedule_valid : schedule.LinearValid :=
  SplitNumeric.schedule_linear_conditions

end OptimalOTS.LeanIsaBaseline.Layer.FourChildNumeric
