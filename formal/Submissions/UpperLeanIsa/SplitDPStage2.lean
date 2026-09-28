import Submissions.UpperLeanIsa.SplitDPStage1

/-! Serial checkpoint 2 of the sparse multiplicative convolution.
Each arithmetic certificate checks at most 32 weight rows. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitDP

attribute [local irreducible] keys1 rows1

def keys2 : List ℕ := [1]

def rows2 : List (List ℕ) :=
  [[0, 3, 15, 46, 111, 231, 434, 756, 1242, 1947, 2937, 4290, 6097, 8416, 11103, 13942, 16837, 19617, 22092, 24052, 25266, 25481, 24421, 21786, 17251, 10465, 3306]]

theorem step2 : stepM (profile 1) 85 keys1 keys2 rows1 = rows2 := by
  decide +kernel

theorem rows_length2 : rows2.length = keys2.length := by decide +kernel

theorem closed1 : ∀ x ∈ profile 1, ∀ w ∈ keys1, w * x.2.1 ∈ keys2 := by
  decide +kernel

end OptimalOTS.LeanIsaBaseline.Layer.SplitDP
