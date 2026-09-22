import Submissions.UpperRiscv.MixedContext
import Submissions.UpperRiscv.Payload

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W W_toNat)
open Forest

/-- Cursor in the graph's payload order, including the final cursor at chain 32. -/
def cursor (k : ℕ) : ℕ := if k < 8 then 192*k else 1536+160*(k-8)
/-- Offset in the wire payload, whose narrow blocks occur in reverse execution order. -/
def wireOffset (k : ℕ) : ℕ := if k < 8 then 192*k else 1536+160*(31-k)

theorem cursor_step (k : Fin 32) : cursor (k.val+1) = cursor k + chainBits k := by
  unfold cursor chainBits
  split_ifs <;> omega

theorem cursor_zero : cursor 0 = 0 := rfl
theorem cursor_end : cursor 32 = 5376 := by decide

theorem wireOffset_aligned (k : Fin 32) : wireOffset k % 8 = 0 := by
  unfold wireOffset; split_ifs <;> omega

theorem wireOffset_contained (k : Fin 32) : wireOffset k + chainBits k ≤ 5376 := by
  have := k.isLt
  unfold wireOffset chainBits; split_ifs <;> omega

theorem wireSlot_eq (k : Fin 32) : wireSlot k = 0x400040 + wireOffset k / 8 := by
  have := k.isLt
  unfold wireSlot slot physical narrow wireOffset
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

theorem slot_bounds (k : Fin 32) :
    0x400040 ≤ slot k ∧ slot k + 24 ≤ 0x400348 ∧ slot k % 8 = 0 := by
  have := k.isLt
  unfold slot physical narrow
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

theorem output_bounds (k : Fin 32) :
    0x400038 ≤ outAddr k ∧ outAddr k + 32 ≤ 0x400348 ∧ outAddr k % 8 = 0 := by
  have h := slot_bounds k
  unfold outAddr; omega

/-- Expanding a narrow chain never overwrites a later, unread wire block. -/
theorem unread_disjoint (k j : Fin 32) (hkj : k.val < j.val) :
    wireSlot j + chainBits j / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ wireSlot j := by
  have := k.isLt; have := j.isLt
  unfold outAddr wireSlot slot physical narrow chainBits
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

/-- Position of the bytes committed by the root for a completed chain. -/
def rootSliceAddr (k : ℕ) : ℕ := if k < 8 ∨ k = 31 then outAddr k else slot k
def rootSliceBits (k : ℕ) : ℕ := if k = 7 ∨ k = 31 then 256 else 192

/-- Every later hash preserves the committed slice of an earlier chain. -/
theorem completed_disjoint (j k : Fin 32) (hjk : j.val < k.val) :
    rootSliceAddr j + rootSliceBits j / 8 ≤ outAddr k ∨
      outAddr k + 32 ≤ rootSliceAddr j := by
  have := k.isLt; have := j.isLt
  unfold rootSliceAddr rootSliceBits outAddr slot physical narrow
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

theorem payload_index (k : Fin 32) (i : ℕ) (hi : i < chainBits k) :
    Payload.index 5376 (cursor k + i) = wireOffset k + i := by
  have := k.isLt
  unfold Payload.index cursor wireOffset chainBits at *
  split_ifs at * <;> omega

end OptimalOTS.RiscvMixedProgram
