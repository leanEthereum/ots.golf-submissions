import Submissions.UpperRiscvHint.MixedContext
import Submissions.UpperRiscvHint.Reader

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W W_toNat)
open Forest

/-- Base cursor in graph payload order. The zero-step bottom top adds three bits to the final
cursor, as recorded by `cursorAt`. -/
def cursor (k : ℕ) : ℕ := if k ≤ 14 then 192*k else 2688+141*(k-14)
/-- Maximum disclosure width in the view; the bottom top has three extra bits. -/
def wireBits (k : Chain) : ℕ := if k.val = 32 then 144 else chainBits k

theorem chainBits_le_wireBits (k : Chain) : chainBits k ≤ wireBits k := by
  revert k; decide

theorem wireBits_le (k : Chain) : wireBits k ≤ 192 := by
  revert k; decide

/-- Offset of chain `k`'s value in the view, in bits. -/
def wireOffset (k : ℕ) : ℕ := 128 + 8 * wireByte k

theorem cursor_step (k : Chain) : cursor (k.val+1) = cursor k + chainBits k := by
  unfold cursor chainBits
  split_ifs <;> omega

/-- The sequential cursor differs only after the final, zero-step bottom chain. -/
def cursorAt (index : ChainIndex) (k : ℕ) : ℕ :=
  cursor k + if k = 33 ∧ 32 ≤ RiscvUpperForest.ForestVerifier.firstAt index 32 then 3 else 0

theorem cursorAt_chain (index : ChainIndex) (k : Chain) : cursorAt index k = cursor k := by
  unfold cursorAt
  rw [if_neg (by have := k.isLt; omega), Nat.add_zero]

theorem cursorAt_next_eval (index : ChainIndex) (k : Chain)
    (h : RiscvUpperForest.ForestVerifier.firstAt index k < 32) :
    cursorAt index (k.val+1) = cursor k + chainBits k := by
  unfold cursorAt
  rw [if_neg, Nat.add_zero, cursor_step]
  rintro ⟨hk, hb⟩
  have he : k = 32 := Fin.ext (by omega)
  subst k
  omega

theorem topBits_hidden (index : ChainIndex) (k : Chain)
    (h : 32 ≤ RiscvUpperForest.ForestVerifier.firstAt index k) : topBits k = wireBits k := by
  have cap : k.val < 14 ∨ 31 ≤ k.val := by
    unfold RiscvUpperForest.ForestVerifier.firstAt firstEval at h
    split_ifs at h with hc
    · exact hc
    · have := (fixedPositions index k).isLt; omega
  rw [topBits_of_cap cap]
  rfl

theorem cursorAt_next_hidden (index : ChainIndex) (k : Chain)
    (h : 32 ≤ RiscvUpperForest.ForestVerifier.firstAt index k) :
    cursorAt index (k.val+1) = cursor k + topBits k := by
  rw [topBits_hidden index k h]
  unfold cursorAt wireBits
  rw [cursor_step]
  by_cases hk : k.val = 32
  · have he : k = 32 := Fin.ext hk
    subst k
    simp [h, chainBits]
  · rw [if_neg hk, if_neg (by omega), Nat.add_zero]

theorem wireOffset_aligned (k : Chain) : wireOffset k % 8 = 0 := by
  unfold wireOffset; omega

theorem wireOffset_contained (k : Chain) : wireOffset k + wireBits k ≤ honestViewBits := by
  revert k; decide

/-- Every chain value sits at its view offset from the view base 0x400030. -/
theorem work_eq_view (k : ℕ) : work k = 0x400030 + wireOffset k / 8 := by
  unfold work wireOffset; omega

/-- Every answer buffer lies above the message, below the lane words. -/
theorem output_bounds (k : Chain) :
    0x400038 ≤ outAddr k ∧ outAddr k + 32 ≤ 0x4003D0 ∧ outAddr k % 8 = 0 := by
  revert k; decide

/-- Where chain `k`'s committed top lies: its answer buffer, shifted by the top's offset. -/
def topAddr (k : Chain) : ℕ := outAddr k + topOff k / 8

/-- The state of every chain begins `truncOff k / 8` bytes into its answer buffer: byte 0 for the
wide chains and chain 31, byte 14 otherwise. -/
theorem work_eq' : ∀ k : Chain, work k = outAddr k + truncOff k / 8 := by
  decide +kernel

/-- A chain hash never overwrites a later, unread view value. -/
theorem unread_disjoint (k j : Chain) (hkj : k.val < j.val) :
    work j + (wireBits j + 7) / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ work j := by
  have hj := j.isLt
  unfold work wireByte outAddr wireBits chainBits
  split_ifs <;> omega

/-- A chain hash never overwrites the committed top of an earlier chain. -/
theorem completed_disjoint (j k : Chain) (hjk : j.val < k.val) :
    topAddr j + (topBits j + 7) / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ topAddr j := by
  have hk := k.isLt
  unfold topAddr outAddr topBits topOff
  split_ifs <;> omega

/-- Distinct chains have distinct answer buffers. -/
theorem outAddr_inj {i j : ℕ} (hi : i < 33) (hj : j < 33) (h : W (outAddr i) = W (outAddr j)) :
    i = j := by
  have e := congrArg BitVec.toNat h
  rw [W_toNat _ (by unfold outAddr; split_ifs <;> omega),
    W_toNat _ (by unfold outAddr; split_ifs <;> omega)] at e
  unfold outAddr at e
  split_ifs at e <;> omega

end OptimalOTS.RiscvMixedProgram
