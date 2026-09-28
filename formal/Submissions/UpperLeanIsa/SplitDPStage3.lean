import Submissions.UpperLeanIsa.SplitDPStage2

/-! Serial checkpoint 3 of the sparse multiplicative convolution.
Each arithmetic certificate checks at most 32 weight rows. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitDP

attribute [local irreducible] keys2 rows2

def keys3 : List ℕ := [1]

def rows3 : List (List ℕ) :=
  [[0, 3, 24, 109, 369, 1035, 2541, 5643, 11583, 22308, 40755, 71214, 119782, 194875, 307452, 470807, 700169, 1011960, 1422673, 1947330, 2597478, 3378679, 4287448, 5307591, 6405893, 7527104, 8592681, 9514894, 10216750, 10633209, 10709232, 10407477, 9713307, 8640393, 7236947, 5592621, 3846109, 2193490, 897351, 188442]]

theorem step3 : stepM (profile 2) 85 keys2 keys3 rows2 = rows3 := by
  decide +kernel

theorem rows_length3 : rows3.length = keys3.length := by decide +kernel

theorem closed2 : ∀ x ∈ profile 2, ∀ w ∈ keys2, w * x.2.1 ∈ keys3 := by
  decide +kernel

end OptimalOTS.LeanIsaBaseline.Layer.SplitDP
