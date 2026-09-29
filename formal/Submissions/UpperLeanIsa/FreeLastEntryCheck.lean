import Submissions.UpperLeanIsa.FreeLastLayoutData

namespace OptimalOTS.FreeLastEntryCheck
open OptimalOTS.FreeLastLayout
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def Entry (e : Nat) (b : Body) : Prop :=
  27 ≤ e ∧ e < 262143 ∧ (candidateTree.lookup e).entry = e ∧
    (candidateTree.lookup e).body = b
instance (e : Nat) (b : Body) : Decidable (Entry e b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def check (f : Nat → Body) (start : Nat) : List Nat → Bool
  | [] => true
  | e::es => decide (Entry e (f start)) && check f (start+1) es

theorem check_append (f : Nat → Body) (start : Nat) (xs ys : List Nat) :
    check f start (xs++ys) = (check f start xs && check f (start+xs.length) ys) := by
  induction xs generalizing start with
  | nil => simp [check]
  | cons e es ih =>
    simp only [List.cons_append,check,ih,List.length_cons]
    rw [Bool.and_assoc,show start+1+es.length = start+(es.length+1) by omega]

theorem check_sound (f : Nat → Body) (es : List Nat) (start : Nat)
    (h : check f start es = true) {i : Nat} (hi : i < es.length) :
    Entry (es.getD i 0) (f (start+i)) := by
  induction es generalizing start i with
  | nil => simp at hi
  | cons e es ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
    cases i with
    | zero => simpa only [List.getD_cons_zero,Nat.add_zero] using h.1
    | succ i =>
      simpa only [List.getD_cons_succ,Nat.add_assoc,Nat.add_comm 1 i] using
        ih (start+1) h.2 (by simpa using hi : i < es.length)

theorem check_append_true (f : Nat → Body) (xs ys : List Nat) (start : Nat)
    (hx : check f start xs = true) (hy : check f (start+xs.length) ys = true) :
    check f start (xs++ys) = true := by
  rw [check_append,hx,hy]
  rfl

end OptimalOTS.FreeLastEntryCheck
