import Submissions.UpperLeanIsa.AffineSelect
import Submissions.UpperLeanIsa.FixedFrameGuard

/-! The selected affine frames guard actual reads in the pinned machine.
The constants depend only on the fixed program layout. -/

namespace OptimalOTS.AffineFrames

open Polynomial LeanerVM.Parameters LeanerVM.Semantics
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def bias (L : Layout) (u : Stage) : K := safeBase L ^ stageExponent u.val

theorem bias_fixed (L : Layout) (u : Stage) (hu : u.val = 13) : bias L u = 1 := by
  simp [bias, stageExponent, hu]

theorem bias_positive (L : Layout) (u : Stage) (hu : u.val ≠ 13) :
    bias L u = safeBase L ^ (u.val + 1) := by
  simp [bias, stageExponent, hu]

def frame (L : Layout) (u : Stage) (s : Slot) : K :=
  bias L u + gpow s.val

def operand (L : Layout) (d : BodyDescriptor) (c : ℕ) : K :=
  gpow c / frame L d.stage d.entry

theorem frame_ne_zero (L : Layout) (u : Stage) (s : Slot)
    (hpos : u.val = 13 → 0 < s.val) : frame L u s ≠ 0 := by
  by_cases hu : u.val = 13
  · simpa only [frame, bias_fixed L u hu, add_comm] using
      FixedFrameChecks.fixed_frame_ne_zero (hpos hu) s.isLt
  · simpa only [frame, bias_positive L u hu] using safeBase_frame_ne_zero L u s

/-- The fixed free-stage frame at target zero is zero; its read fails instead
of being covered by a false nonzero-frame assertion. -/
theorem frame_fixed_zero (L : Layout) :
    frame L ⟨13, by decide⟩ ⟨0, by decide⟩ = 0 := by
  unfold frame
  rw [bias_fixed L _ rfl]
  simpa only [add_comm] using
    FixedFrameChecks.fixed_frame_zero

theorem read_fixed_zero {κ : ℕ} (M : MemImage κ) (L : Layout) (c : K) :
    M.read (frame L ⟨13, by decide⟩ ⟨0, by decide⟩ * c) = none := by
  rw [frame_fixed_zero, zero_mul]
  apply (MemImage.read_eq_none_iff M).mpr
  intro j
  exact (pow_ne_zero _ g_ne_zero).symm

theorem operand_correct (L : Layout) (d : BodyDescriptor) (c : ℕ)
    (hpos : d.stage.val = 13 → 0 < d.entry.val) :
    frame L d.stage d.entry * operand L d c = gpow c := by
  unfold operand
  exact mul_div_cancel₀ _ (frame_ne_zero L d.stage d.entry hpos)

theorem frame_halt_ne_one (L : Layout) (u : Stage) :
    frame L u ⟨2 ^ 18 - 1, by norm_num⟩ ≠ 1 := by
  by_cases hu : u.val = 13
  · simpa only [frame, bias_fixed L u hu, show (2 ^ 18 - 1 : ℕ) = 262143 by decide,
      add_comm] using
      FixedFrameChecks.fixed_halt_ne_one
  · have h := safeBase_avoids L (.inr (.inr (.inl u)))
    simpa only [constraints, initialPoly, framePoly, Polynomial.eval_sub,
      Polynomial.eval_C_mul, Polynomial.eval_add, Polynomial.eval_X_pow,
      Polynomial.eval_C, gpow, pow_zero, one_mul, sub_ne_zero, frame,
      bias_positive L u hu] using h

theorem initial_address_ne (L : Layout) (hL : FixedHyp L)
    (u : Stage) (s : Slot) (c : Cell) (hshape : L s = .initial c) (j : MaxCell) :
    frame L u s * gpow c.val ≠ gpow j.val := by
  by_cases hu : u.val = 13
  · simpa only [frame, bias_fixed L u hu, add_comm] using
      FixedFrameChecks.fixed_initial_address_ne (hL.initial_range s c hshape) c.isLt j.isLt
  · have h := safeBase_avoids L (.inl (u,s,j))
    simp only [constraints, landingPoly, hshape, if_neg hu, initialPoly, framePoly,
      Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_add,
      Polynomial.eval_X_pow, Polynomial.eval_C, sub_ne_zero] at h
    simpa only [frame, bias_positive L u hu, mul_comm] using h

theorem declared_entry_positive (L : Layout) (hL : FixedHyp L)
    (s : Slot) (d : BodyDescriptor) (hshape : L s = .body d)
    (hd : d.stage.val = 13) : 0 < d.entry.val := by
  have hh := hL.fixed_body s d hshape hd
  omega

theorem body_address_ne (L : Layout) (hL : FixedHyp L)
    (u : Stage) (s : Slot) (d : BodyDescriptor)
    (hshape : L s = .body d) (hwrong : ¬(u = d.stage ∧ s = d.entry)) (j : MaxCell) :
    frame L u s * operand L d d.firstCell.val ≠ gpow j.val := by
  have hdpos := declared_entry_positive L hL s d hshape
  by_cases hfixed : u.val = 13 ∧ d.stage.val = 13
  · obtain ⟨hlo, hhi, he⟩ := hL.fixed_body s d hshape hfixed.2
    have hne : s.val ≠ 255615 + 68 * ((s.val - 255615) / 68) := by
      intro hs
      exact hwrong ⟨Fin.ext (hfixed.1.trans hfixed.2.symm), Fin.ext (hs.trans he.symm)⟩
    obtain ⟨delta, hcheck⟩ := FixedFrameData.all_free_wrong hlo hhi hne
    rw [← he] at hcheck
    have hn := FixedFrameChecks.fixed_frame_ne_zero (hdpos hfixed.2) d.entry.isLt
    simpa only [frame, operand, bias_fixed L u hfixed.1,
      bias_fixed L d.stage hfixed.2, add_comm] using
      FixedFrameChecks.fixed_body_address_ne hcheck d.firstCell.isLt j.isLt hn
  · have h := safeBase_avoids L (.inl (u,s,j))
    simp only [constraints, landingPoly, hshape, if_neg (not_or.mpr ⟨hwrong, hfixed⟩),
      collision_eval, sub_ne_zero] at h
    intro he
    apply h
    change gpow d.firstCell.val * frame L u s =
      gpow j.val * frame L d.stage d.entry
    have he' := (div_eq_iff (frame_ne_zero L d.stage d.entry hdpos)).mp
      (show (frame L u s * gpow d.firstCell.val) / frame L d.stage d.entry =
        gpow j.val by simpa only [operand, mul_div_assoc] using he)
    simpa only [mul_comm] using he'

/-- The guard covers every prover-selected image size, not only the honest image. -/
theorem read_initial_none {κ : ℕ} (hκ : κ ≤ 32) (M : MemImage κ)
    (L : Layout) (hL : FixedHyp L) (u : Stage) (s : Slot) (c : Cell)
    (hshape : L s = .initial c) :
    M.read (frame L u s * gpow c.val) = none := by
  apply (MemImage.read_eq_none_iff M).mpr
  intro j
  have hj : j.val < 2 ^ 32 := lt_of_lt_of_le j.isLt
    (Nat.pow_le_pow_right (by norm_num) hκ)
  exact initial_address_ne L hL u s c hshape ⟨j.val,hj⟩

theorem read_body_none {κ : ℕ} (hκ : κ ≤ 32) (M : MemImage κ)
    (L : Layout) (hL : FixedHyp L) (u : Stage) (s : Slot) (d : BodyDescriptor)
    (hshape : L s = .body d) (hwrong : ¬(u = d.stage ∧ s = d.entry)) :
    M.read (frame L u s * operand L d d.firstCell.val) = none := by
  apply (MemImage.read_eq_none_iff M).mpr
  intro j
  have hj : j.val < 2 ^ 32 := lt_of_lt_of_le j.isLt
    (Nat.pow_le_pow_right (by norm_num) hκ)
  exact body_address_ne L hL u s d hshape hwrong ⟨j.val,hj⟩

/-- Correctly framed operands still address the original absolute cells. -/
theorem read_body_correct {κ : ℕ} (hκ : κ < 64) (M : MemImage κ)
    (L : Layout) (d : BodyDescriptor) (c : Fin (2 ^ κ))
    (hpos : d.stage.val = 13 → 0 < d.entry.val) :
    M.read (frame L d.stage d.entry * operand L d c.val) = some (M c) := by
  rw [operand_correct L d c.val hpos]
  exact MemImage.read_gpow hκ M c

/-- A primitive's first read happens before any assertion or oracle call. -/
def firstOperand : Instr → K
  | .xor a _ _ => a
  | .mulNative a _ _ => a
  | .setConstant a _ => a
  | .deref a _ _ _ => a
  | .jump a _ _ => a
  | .blake2s m _ _ _ => m 0

theorem execute_none_of_first {κ : ℕ} (M : MemImage κ) (r : Regs K) (i : Instr)
    (h : M.read (r.fp * firstOperand i) = none) :
    LeanIsa.execute M r i = pure none := by
  cases i <;> simp only [firstOperand] at h <;>
    simp [LeanIsa.execute, LeanerVM.Semantics.execute, h]

theorem execute_wrong_body {κ : ℕ} (hκ : κ ≤ 32) (M : MemImage κ)
    (L : Layout) (hL : FixedHyp L) (u : Stage) (s : Slot) (d : BodyDescriptor) (i : Instr)
    (hshape : L s = .body d) (hwrong : ¬(u = d.stage ∧ s = d.entry))
    (hfirst : firstOperand i = operand L d d.firstCell.val) :
    LeanIsa.execute M ⟨gpow s.val, frame L u s⟩ i = pure none := by
  apply execute_none_of_first
  rw [hfirst]
  exact read_body_none hκ M L hL u s d hshape hwrong

theorem execute_wrong_initial {κ : ℕ} (hκ : κ ≤ 32) (M : MemImage κ)
    (L : Layout) (hL : FixedHyp L) (u : Stage) (s : Slot) (c : Cell) (i : Instr)
    (hshape : L s = .initial c) (hfirst : firstOperand i = gpow c.val) :
    LeanIsa.execute M ⟨gpow s.val, frame L u s⟩ i = pure none := by
  apply execute_none_of_first
  rw [hfirst]
  exact read_initial_none hκ M L hL u s c hshape

/-- The same selected base also pins the exact total number of charged hashes. -/
def initialProduct (L : Layout) (layer s : ℕ) : K :=
  gpow (2 ^ 18 - 1) / safeBase L ^ layer * safeBase L ^ s

theorem checksum_exact (L : Layout) {layer s c : ℕ}
    (hLayer : layer ≤ 300) (hSum : s + c ≤ 300) :
    initialProduct L layer s * safeBase L ^ c = gpow (2 ^ 18 - 1) ↔ s + c = layer := by
  have hn : gpow (2 ^ 18 - 1) ≠ 0 := pow_ne_zero _ g_ne_zero
  have hl : safeBase L ^ layer ≠ 0 := pow_ne_zero _ (safeBase_ne_zero L)
  rw [initialProduct, mul_assoc, ← pow_add]
  constructor
  · intro h
    have he : safeBase L ^ (s+c) = safeBase L ^ layer := by
      field_simp at h
      exact h
    exact safeBase_powers_injective L hSum hLayer he
  · intro h
    rw [h]
    exact div_mul_cancel₀ _ hl

end
end OptimalOTS.AffineFrames
