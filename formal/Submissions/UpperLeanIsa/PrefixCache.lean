import Submissions.UpperLeanIsa.ConstraintMath

/-! Prefix tables checked by their initial value and every recurrence step.
The correctness lemma is uniform in the summands and the table implementation. -/
namespace OptimalOTS.CheckedPrefix
open scoped BigOperators

def read (data width index : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul width index)) (Nat.sub (Nat.pow 2 width) 1)

def check (F table : Nat → Nat) (n : Nat) : Bool :=
  Nat.beq (table 0) 0 && (List.range n).all fun i =>
    Nat.beq (table (i+1)) (Nat.add (table i) (F i))

theorem correct (F table : Nat → Nat) {n : Nat} (h : check F table n = true)
    {j : Nat} (hj : j ≤ n) : table j = ∑ i ∈ Finset.range j, F i := by
  simp only [check, Bool.and_eq_true, Nat.beq_eq] at h
  have hs (i : Nat) (hi : i < n) : table (i+1) = table i + F i :=
    Nat.beq_eq.mp (List.all_eq_true.mp h.2 i (List.mem_range.mpr hi))
  induction j with
  | zero => simpa using h.1
  | succ j ih => rw [hs j (by omega), ih (by omega), Finset.sum_range_succ]

end OptimalOTS.CheckedPrefix
