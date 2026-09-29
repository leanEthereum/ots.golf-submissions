import Submissions.UpperLeanIsa.FreeLastBlocks
import Submissions.UpperLeanIsa.CenteredChecksum

/-! The special last group is group 1, whose complete raw code is pinned by
an ordinary tie. Duplicating a hinted group would change its hint word. These
lemmas isolate the N-to-Z re-entry contradiction used by the future path proof. -/
namespace OptimalOTS.FreeLastBlocks
open LeanerVM.Parameters OptimalOTS.HLFour
open OptimalOTS.LeanIsaBaseline.Layer
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pattern1_zero : pattern 1 0 = 0 := by decide +kernel

theorem pattern1_injective {v w : Nat} (hv : v < 512) (hw : w < 512)
    (h : pattern 1 v = pattern 1 w) : v = w := by
  unfold pattern at h
  have he := congrArg LeanIsa.cellBits h
  simp only [LeanIsa.cellBits_cellOfBits] at he
  have hi := PartialHints.wordPermutation.injective he
  have hp : POS 1 = 10 := rfl
  have hlv : label 1 v = v := rfl
  have hlw : label 1 w = w := rfl
  rw [hp, hlv, hlw] at hi
  have hn := congrArg BitVec.toNat hi
  simp only [BitVec.toNat_ofNat] at hn
  norm_num at hn
  omega

theorem tie1_equation (B : BlakeRel) (mem : Nat → E) {v : Nat}
    (hone : mem oneCell = 1)
    (h : ∀ ci ∈ tie 1 v, ci.RelB B mem) :
    mem (accCell 1) = mem (accCell 0) + pattern 1 v := by
  have hnv : hinted 1 v = false := rfl
  by_cases hz : v = 0
  · subst v
    have hc := h (copy (accCell 0) (accCell 1)) (by
      simp only [tie, show ¬(1 : Nat) = 0 by decide, if_false, hnv, Bool.false_eq_true,
        if_true, List.mem_singleton])
    change mem (accCell 1) = mem (accCell 0) * mem oneCell at hc
    simpa only [hone, mul_one, pattern1_zero, add_zero] using hc
  · have hs := h (.setc (tCell 1) (pattern 1 v)) (by
      simp only [tie, show ¬(1 : Nat) = 0 by decide, if_false, hnv, Bool.false_eq_true,
        if_neg hz, List.mem_cons, true_or])
    have hx := h (.xor (accCell 0) (tCell 1) (accCell 1)) (by
      simp only [tie, show ¬(1 : Nat) = 0 by decide, if_false, hnv, Bool.false_eq_true,
        if_neg hz, List.mem_cons, List.not_mem_nil, or_false, or_true])
    change mem (tCell 1) = pattern 1 v at hs
    change mem (accCell 1) = mem (accCell 0) + mem (tCell 1) at hx
    rwa [hs] at hx

theorem tie1_unique (B : BlakeRel) (mem : Nat → E) {v w : Nat}
    (hv : v < 512) (hw : w < 512) (hone : mem oneCell = 1)
    (h : ∀ ci ∈ tie 1 v, ci.RelB B mem)
    (h' : ∀ ci ∈ tie 1 w, ci.RelB B mem) : v = w := by
  apply pattern1_injective hv hw
  exact add_left_cancel ((tie1_equation B mem hone h).symm.trans (tie1_equation B mem hone h'))

theorem checksum_unique {F : Type*} [Field F] {a x y z : F} (ha : a ≠ 0) (c : Nat)
    (h : CenteredChecksum.Step a c x y) (h' : CenteredChecksum.Step a c x z) : y = z :=
  ((CenteredChecksum.step_ratio ha c).mp h).trans ((CenteredChecksum.step_ratio ha c).mp h').symm

theorem zero_switch_impossible {F : Type*} [Field F] {a x y : F} (ha : a ≠ 0)
    (hsep : a^2 ≠ 1) (c : Nat) (hincoming : y = a^2)
    (hn : CenteredChecksum.Step a c x y) (hz : CenteredChecksum.Step a c x 1) : False := by
  have he := checksum_unique ha c hn hz
  exact hsep (hincoming.symm.trans he)

end
end OptimalOTS.FreeLastBlocks
