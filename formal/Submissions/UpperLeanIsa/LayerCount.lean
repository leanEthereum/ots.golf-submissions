import Mathlib

/-!
# List sums over a range

`sum_map_range` turns the list sums that kernel-evaluated tables use into `Finset` sums.
-/

namespace OptimalOTS.LeanIsaBaseline.Layer

theorem sum_map_range (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ v ∈ Finset.range m, f v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

end OptimalOTS.LeanIsaBaseline.Layer
