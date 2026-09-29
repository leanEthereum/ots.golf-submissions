import Submissions.UpperLeanIsa.FreeLastBlocks

/-! A balanced interval decoder and its kernel-checkable geometry invariant.
The concrete rows are generated in FreeLastLayoutData. -/
namespace OptimalOTS.FreeLastLayout
open OptimalOTS.HLFour OptimalOTS.FreeLastBlocks
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

inductive Body
  | group (unit raw : Nat) (zero : Bool)
  | free (steps : Nat)
  | trap
  deriving DecidableEq

structure Row where
  entry : Nat
  length : Nat
  body : Body
  deriving DecidableEq

def hintAt (u v e : Nat) : Bool :=
  if u = 8 then PartialHints.hints8.any (fun r => r.1 == e &&
    (PartialHints.label8 (BitVec.ofNat 10 r.2.1)).toNat == v)
  else if u = 9 then PartialHints.hints9.any (fun r => r.1 == e &&
    (PartialHints.label9 (BitVec.ofNat 10 r.2.1)).toNat == v)
  else true

def Good (r : Row) : Prop :=
  0 < r.length ∧ match r.body with
  | .trap => True
  | .free s => 1 ≤ s ∧ s ≤ 63 ∧ r.length = s+1
  | .group u v z => u < 13 ∧ v < VF u ∧ (z = true → u = 1) ∧
      budget u + band u v + hm u + (if z then 1 else 0) ≤ r.length ∧
      (u = 11 ∨ u = 12 → r.entry = entryOf u v ∧ r.length = SL u v) ∧
      (hinted u v = true → hintAt u v r.entry = true)

instance (r : Row) : Decidable (Good r) := by unfold Good; cases r.body <;> infer_instance

inductive Tree
  | leaf (row : Row)
  | branch (pivot : Nat) (left right : Tree)

def Tree.lookup : Tree → Nat → Row
  | .leaf r, _ => r
  | .branch p l r, s => if s < p then l.lookup s else r.lookup s

def Tree.check : Tree → Nat → Nat → Bool
  | .leaf r, lo, hi => decide (r.entry = lo ∧ r.entry+r.length = hi ∧ Good r)
  | .branch p l r, lo, hi => decide (lo < p ∧ p < hi) && l.check lo p && r.check p hi

theorem Tree.lookup_good (t : Tree) {lo hi : Nat} (h : t.check lo hi = true)
    {s : Nat} (hlo : lo ≤ s) (hhi : s < hi) :
    Good (t.lookup s) ∧ (t.lookup s).entry ≤ s ∧
      s < (t.lookup s).entry + (t.lookup s).length := by
  induction t generalizing lo hi with
  | leaf r =>
    simp only [Tree.check, decide_eq_true_eq] at h
    change Good r ∧ r.entry ≤ s ∧ s < r.entry+r.length
    exact ⟨h.2.2, by omega, by omega⟩
  | branch p l r ihl ihr =>
    simp only [Tree.check, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hs : s < p
    · simpa only [Tree.lookup, if_pos hs] using ihl h.1.2 hlo hs
    · simpa only [Tree.lookup, if_neg hs] using ihr h.2 (by omega) hhi

end OptimalOTS.FreeLastLayout
