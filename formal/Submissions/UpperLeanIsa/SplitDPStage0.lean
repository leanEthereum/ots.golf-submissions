import Submissions.UpperLeanIsa.SplitProfiles
import Submissions.UpperLeanIsa.SplitNumeric

/-! Serial checkpoint 0 of the sparse multiplicative convolution.
Each arithmetic certificate checks at most 32 weight rows. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalOTS.LeanIsaBaseline.Layer.SplitDP

theorem stepM_append_eq (p : List MProfile) (S : ℕ) (prevKeys a b : List ℕ)
    (prev ra rb : List (List ℕ))
    (ha : stepM p S prevKeys a prev = ra)
    (hb : stepM p S prevKeys b prev = rb) :
    stepM p S prevKeys (a ++ b) prev = ra ++ rb :=
  (stepM_append p S prevKeys a b prev).trans (congrArg₂ List.append ha hb)

theorem map_getD_eq (f : List ℕ → ℕ) (hf : f [] = 0)
    (rows : List (List ℕ)) (i : ℕ) :
    (rows.map f).getD i 0 = f (rows.getD i []) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases rows[i]? <;> simp [hf]

theorem map_append_eq (f : List ℕ → ℕ) (a b : List (List ℕ)) (ra rb : List ℕ)
    (ha : a.map f = ra) (hb : b.map f = rb) : (a ++ b).map f = ra ++ rb := by
  rw [List.map_append]
  exact congrArg₂ List.append ha hb

theorem take_sum_getD : ∀ (n : ℕ) (xs : List ℕ),
    (xs.take n).sum = ∑ i ∈ Finset.range n, xs.getD i 0
  | 0, xs => by simp
  | n + 1, [] => by simp
  | n + 1, a :: xs => by
    rw [List.take_succ_cons, List.sum_cons, take_sum_getD n xs,
      Finset.sum_range_succ']
    simp [Nat.add_comm]

theorem winSum_fast (row : List ℕ) :
    ((List.range 64).map fun i => row.getD (22 + i) 0).sum =
      ((row.drop 22).take 64).sum := by
  rw [sum_map_range, take_sum_getD]
  apply Finset.sum_congr rfl
  intro i _
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

def winSum (row : List ℕ) : ℕ := ((row.drop 22).take 64).sum

theorem winSum_eq (row : List ℕ) :
    winSum row = ((List.range 64).map fun i => row.getD (22 + i) 0).sum :=
  (winSum_fast row).symm

def keys0 : List ℕ := [1]

def rows0 : List (List ℕ) :=
  [[1]]

theorem rows_length0 : rows0.length = keys0.length := by decide +kernel

end OptimalOTS.LeanIsaBaseline.Layer.SplitDP
