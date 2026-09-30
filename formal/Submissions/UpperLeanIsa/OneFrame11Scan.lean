import Submissions.UpperLeanIsa.LengthFrameScan

/-! Exhaustive constant-frame guards for the unchanged stage-11 intervals.
Each finite-field relation is checked by the Lean kernel. -/
namespace OptimalOTS.OneFrame11
open LeanerVM.Parameters OptimalOTS.HLFour OptimalOTS.ByteWindow
open OptimalOTS.LengthFrameChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000
set_option Elab.async false

def blocksCheck : Nat → List (List (Nat × Nat)) → Bool
  | _, [] => true
  | x, r :: rs => Nat.beq r.length (SL 11 x) &&
      scan (entryOf 11 x) 1 (entryOf 11 x) r && blocksCheck (x+1) rs

theorem blocksCheck_cons {x : Nat} {r : List (Nat × Nat)} {rs : List (List (Nat × Nat))}
    (hr : r.length = SL 11 x ∧ scan (entryOf 11 x) 1 (entryOf 11 x) r = true)
    (ht : blocksCheck (x+1) rs = true) : blocksCheck x (r::rs) = true := by
  simp only [blocksCheck,Bool.and_eq_true,Nat.beq_eq]
  exact ⟨hr,ht⟩

theorem blocksCheck_sound : ∀ rs x, blocksCheck x rs = true →
    ∀ j < rs.length, ∃ r, r.length = SL 11 (x+j) ∧
      scan (entryOf 11 (x+j)) 1 (entryOf 11 (x+j)) r = true := by
  intro rs
  induction rs with
  | nil => intros; simp_all
  | cons r rs ih =>
    intro x h j hj
    simp only [blocksCheck, Bool.and_eq_true, Nat.beq_eq] at h
    cases j with
    | zero => exact ⟨r, h.1.1, h.1.2⟩
    | succ j =>
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
        ih (x+1) h.2 j (by simpa using hj)
def exitCheck : Nat → List Nat → Bool
  | _, [] => true
  | x, delta :: ds => frameCheck bytePow 0 (entryOf 11 x) 0 1 delta && exitCheck (x+1) ds

theorem exitCheck_cons {x delta : Nat} {ds : List Nat}
    (hd : frameCheck bytePow 0 (entryOf 11 x) 0 1 delta = true)
    (hs : exitCheck (x+1) ds = true) : exitCheck x (delta::ds) = true := by
  simp only [exitCheck,Bool.and_eq_true]
  exact ⟨hd,hs⟩

theorem exitCheck_sound : ∀ ds x, exitCheck x ds = true → ∀ i < ds.length,
    ∃ delta, frameCheck bytePow 0 (entryOf 11 (x+i)) 0 1 delta = true := by
  intro ds
  induction ds with
  | nil => intros; simp_all
  | cons d ds ih =>
    intro x h i hi
    simp only [exitCheck, Bool.and_eq_true] at h
    cases i with
    | zero => exact ⟨d, h.1⟩
    | succ i =>
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using ih (x+1) h.2 i (by simpa using hi)

end OptimalOTS.OneFrame11
