import Submissions.UpperLeanIsa.FreeLastSelect
import Submissions.UpperLeanIsa.FreeLastProgram
import Submissions.UpperLeanIsa.LengthFrameChecks

/-! Instantiation of the weighted base selection with the concrete candidate
decoder. This fixes the bytecode's base and proves that all declared body
frames are nonzero. Complete landing/read and whole-run proofs are separate. -/
namespace OptimalOTS.FreeLastBase
open LeanerVM.Parameters LeanerVM.Semantics OptimalOTS.HLFour
open OptimalOTS.FreeLastLayout OptimalOTS.FreeLastBlocks
noncomputable section
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def cell0 : CInstr → Nat
  | .init => lenCell
  | .xor a _ _ => a
  | .mul a _ _ => a
  | .setc a _ => a
  | .blake a _ _ _ _ _ _ => a
  | _ => oneCell

def bodyCell (r : Row) (s : Nat) : Nat :=
  let i := s-r.entry
  let b := FreeLastProgram.body r
  if i < b.length then cell0 (b.getD i .pad) else oneCell

def defaultTarget : FreeLastSelect.Target := ⟨0,0,oneCell⟩

def groupTarget (s : FreeLastSelect.GroupSlot) : FreeLastSelect.Target :=
  if s.val < 27 then
    let b := FreeLastBlocks.prologue 1
    ⟨0,0,if s.val < b.length then cell0 (b.getD s.val .pad) else oneCell⟩
  else
    let r := candidateTree.lookup s.val
    match r.body with
    | .group u _ _ =>
        if u < 12 then ⟨(u+1 : Nat),gpow r.entry,bodyCell r s.val⟩
        else ⟨0,gpow r.entry+AffineFrames.lengthK-1,bodyCell r s.val⟩
    | _ => defaultTarget

def freeTarget (s : FreeLastSelect.FreeSlot) : FreeLastSelect.Target :=
  let r := candidateTree.lookup (260064+s.val)
  match r.body with
  | .free n => if n ≤ 63 then ⟨-(n : Int),gpow r.entry,bodyCell r (260064+s.val)⟩
      else defaultTarget
  | _ => defaultTarget

def layout : FreeLastSelect.Layout where
  group := groupTarget
  free := freeTarget
  group_bounds s := by
    by_cases hs : s.val < 27
    · simp only [groupTarget, if_pos hs]; decide
    · simp only [groupTarget, if_neg hs]
      cases hb : (candidateTree.lookup s.val).body with
      | group u v z =>
        simp only [hb]
        split_ifs <;> simp only <;> constructor <;> omega
      | free n => simp [hb, defaultTarget]
      | trap => simp [hb, defaultTarget]
  free_bounds s := by
    simp only [freeTarget]
    cases hb : (candidateTree.lookup (260064+s.val)).body with
    | free n => simp only [hb]; split_ifs <;> simp only [defaultTarget] <;> constructor <;> omega
    | group u v z => simp [hb, defaultTarget]
    | trap => simp [hb, defaultTarget]

def base : K := FreeLastSelect.base layout
def program : Program := FreeLastProgram.program base

theorem base_ne_zero : base ≠ 0 := FreeLastSelect.base_ne_zero layout
theorem valid : LeanIsa.BytecodeValid program := FreeLastProgram.valid base
theorem seeded_rows : 2^program.logSize + 2^16 < LeanIsa.maxSeededRows :=
  FreeLastProgram.seeded_rows base

theorem powers_injective {i j : Nat} (hi : i ≤ 300) (hj : j ≤ 300)
    (h : base^i = base^j) : i = j := FreeLastSelect.powers_injective layout hi hj h

theorem group_frame_nonzero {s u v : Nat} {z : Bool}
    (hs : 27 ≤ s) (hs' : s < 262143)
    (hb : (candidateTree.lookup s).body = .group u v z) :
    FreeLastProgram.frame base (candidateTree.lookup s) ≠ 0 := by
  obtain ⟨hg, he, hl⟩ := candidate_lookup_good hs hs'
  have hgood := hg.2
  simp only [hb] at hgood
  have hu : u < 13 := hgood.1
  have hentry : (candidateTree.lookup s).entry < 2^18 := by omega
  by_cases hu12 : u < 12
  · let t : FreeLastSelect.TargetSlot := .inl ⟨s,by omega⟩
    have ht : layout.target t =
        ⟨(u+1 : Nat),gpow (candidateTree.lookup s).entry,bodyCell (candidateTree.lookup s) s⟩ := by
      simp only [t, FreeLastSelect.Layout.target, layout, groupTarget,
        show ¬s < 27 by omega, if_false, hb, if_pos hu12]
    have hn : (layout.target t).exponent ≠ 0 := by rw [ht]; simp only; omega
    have h := FreeLastSelect.nonconstant_frame_nonzero layout t hn
    rw [ht] at h
    simpa only [base, FreeLastProgram.frame, hb, show u ≠ 12 by omega, if_false,
      zpow_natCast, add_comm] using h
  · have hu12' : u = 12 := by omega
    simpa only [base, FreeLastProgram.frame, hb, hu12', if_true,
      LengthFrameChecks.lengthBias] using LengthFrameChecks.length_frame_ne_zero hentry

theorem free_frame_nonzero_at (s : FreeLastSelect.FreeSlot) {n : Nat}
    (hb : (candidateTree.lookup (260064+s.val)).body = .free n) :
    FreeLastProgram.frame base (candidateTree.lookup (260064+s.val)) ≠ 0 := by
  have hs : 27 ≤ 260064+s.val := by omega
  have hs' : 260064+s.val < 262143 := by have := s.isLt; omega
  obtain ⟨hg, _, _⟩ := candidate_lookup_good hs hs'
  have hgood := hg.2
  simp only [hb] at hgood
  obtain ⟨hn,h63,_,_,_⟩ := hgood
  have ht : layout.target (.inr s) =
      ⟨-(n : Int),gpow (candidateTree.lookup (260064+s.val)).entry,
        bodyCell (candidateTree.lookup (260064+s.val)) (260064+s.val)⟩ := by
    simp only [FreeLastSelect.Layout.target, layout, freeTarget, hb, if_pos h63]
  have hn' : (layout.target (.inr s)).exponent ≠ 0 := by rw [ht]; simp only; omega
  have h := FreeLastSelect.nonconstant_frame_nonzero layout (.inr s) hn'
  rw [ht] at h
  have he : (FreeLastSelect.base layout)^(-(n : Int)) = (base^n)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
    rfl
  change (FreeLastSelect.base layout)^(-(n : Int)) +
    gpow (candidateTree.lookup (260064+s.val)).entry ≠ 0 at h
  rw [he] at h
  rw [FreeLastProgram.frame, hb, add_comm]
  exact h

theorem free_frame_nonzero {s n : Nat} (hs : 27 ≤ s) (hs' : s < 262143)
    (hb : (candidateTree.lookup s).body = .free n) :
    FreeLastProgram.frame base (candidateTree.lookup s) ≠ 0 := by
  obtain ⟨hg, he, _⟩ := candidate_lookup_good hs hs'
  have hgood := hg.2
  simp only [hb] at hgood
  have hslo : 260064 ≤ s := by have := hgood.2.2.2.1; omega
  have heq : 260064+(s-260064) = s := by omega
  have hb' : (candidateTree.lookup (260064+(s-260064))).body = .free n := by
    rw [heq]; exact hb
  simpa only [heq] using free_frame_nonzero_at ⟨s-260064,by omega⟩ hb'

end
end OptimalOTS.FreeLastBase
