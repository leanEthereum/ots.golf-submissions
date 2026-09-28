import Submissions.UpperLeanIsa.SplitDPStage3

/-! Serial checkpoint 4 of the sparse multiplicative convolution.
Each arithmetic certificate checks at most 32 weight rows. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitDP

attribute [local irreducible] keys3 rows3

def keys4 : List ℕ := [1]

def rows4 : List (List ℕ) :=
  [[0, 3, 33, 199, 870, 3081, 9373, 25389, 62712, 143650, 308958, 629850, 1226108, 2292607, 4136655, 7227979, 12262332, 20238327, 32545165, 51056355, 78221262, 117142298, 171620722, 246148266, 345815080, 476096712, 642480696, 849924592, 1102187688, 1401082734, 1745688734, 2131589422, 2550217584, 2988402709, 3428238663, 3847409289, 4220133154, 4518914205, 4717312977, 4793658473, 4734492544, 4536138198, 4204812106, 3756659190, 3217444092, 2621353171, 2008938867, 1424035527, 909457012, 501266353, 221386347, 68297229, 10741194]]

theorem step4 : stepM (profile 3) 85 keys3 keys4 rows3 = rows4 := by
  decide +kernel

theorem rows_length4 : rows4.length = keys4.length := by decide +kernel

theorem closed3 : ∀ x ∈ profile 3, ∀ w ∈ keys3, w * x.2.1 ∈ keys4 := by
  decide +kernel

end OptimalOTS.LeanIsaBaseline.Layer.SplitDP
