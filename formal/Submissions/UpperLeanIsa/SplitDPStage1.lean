import Submissions.UpperLeanIsa.SplitDPStage0

/-! Serial checkpoint 1 of the sparse multiplicative convolution.
Each arithmetic certificate checks at most 32 weight rows. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitDP

attribute [local irreducible] keys0 rows0

def keys1 : List ℕ := [1]

def rows1 : List (List ℕ) :=
  [[0, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 58]]

theorem step1 : stepM (profile 0) 85 keys0 keys1 rows0 = rows1 := by
  decide +kernel

theorem rows_length1 : rows1.length = keys1.length := by decide +kernel

theorem closed0 : ∀ x ∈ profile 0, ∀ w ∈ keys0, w * x.2.1 ∈ keys1 := by
  decide +kernel

end OptimalOTS.LeanIsaBaseline.Layer.SplitDP
