import Submissions.UpperRiscvHint.MixedContext
import Submissions.UpperRiscvHint.Reader

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W W_toNat)
open Forest

/-- Cursor in the graph's payload order (the free chain and the 12 caps, then the 20 normal
chains), including the final cursor at chain 33. -/
def cursor (k : ℕ) : ℕ := if k ≤ 13 then 192*k else 2496+144*(k-13)
/-- Offset of chain `k`'s value in the view, in bits. -/
def wireOffset (k : ℕ) : ℕ := 128 + 8 * wireByte k

theorem cursor_step (k : Chain) : cursor (k.val+1) = cursor k + chainBits k := by
  unfold cursor chainBits
  split_ifs <;> omega

theorem cursor_zero : cursor 0 = 0 := rfl
theorem cursor_end : cursor 33 = 5376 := by decide

theorem wireOffset_aligned (k : Chain) : wireOffset k % 8 = 0 := by
  unfold wireOffset; omega

theorem wireOffset_contained (k : Chain) : wireOffset k + chainBits k ≤ honestViewBits := by
  revert k; decide

/-- Every chain value sits at its view offset from the view base 0x400030. -/
theorem work_eq_view (k : ℕ) : work k = 0x400030 + wireOffset k / 8 := by
  unfold work wireOffset; omega

/-- Every answer buffer lies in the root region, below the lane words. -/
theorem output_bounds (k : Chain) :
    0x400040 ≤ outAddr k ∧ outAddr k + 32 ≤ 0x4003C0 ∧ outAddr k % 8 = 0 := by
  revert k; decide

/-- The state of every chain begins `truncOff k / 8` bytes into its answer buffer: byte 0 for the
free chain and a cap, byte 8 for a normal chain. -/
theorem work_eq' : ∀ k : Chain, work k = outAddr k + truncOff k / 8 := by
  decide +kernel

/-- A chain hash never overwrites a later, unread view value. -/
theorem unread_disjoint (k j : Chain) (hkj : k.val < j.val) :
    work j + chainBits j / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ work j := by
  have hj := j.isLt
  unfold work wireByte outAddr chainBits
  split_ifs <;> omega

/-- A chain hash never overwrites the committed top of an earlier chain. -/
theorem completed_disjoint (j k : Chain) (hjk : j.val < k.val) :
    outAddr j + topBits j / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ outAddr j := by
  have hk := k.isLt
  unfold outAddr topBits
  split_ifs <;> omega

/-- Distinct chains have distinct answer buffers. -/
theorem outAddr_inj {i j : ℕ} (hi : i < 33) (hj : j < 33) (h : W (outAddr i) = W (outAddr j)) :
    i = j := by
  have e := congrArg BitVec.toNat h
  rw [W_toNat _ (by unfold outAddr; split_ifs <;> omega),
    W_toNat _ (by unfold outAddr; split_ifs <;> omega)] at e
  unfold outAddr at e
  split_ifs at e <;> omega

theorem work_inj {i j : ℕ} (hi : i < 33) (hj : j < 33) (h : W (work i) = W (work j)) : i = j := by
  have e := congrArg BitVec.toNat h
  rw [W_toNat _ (by unfold work wireByte; split_ifs <;> omega),
    W_toNat _ (by unfold work wireByte; split_ifs <;> omega)] at e
  unfold work wireByte at e
  split_ifs at e <;> omega

end OptimalOTS.RiscvMixedProgram
