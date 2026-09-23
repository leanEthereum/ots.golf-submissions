import Submissions.UpperRiscv.MixedContext
import Submissions.UpperRiscv.Payload

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W W_toNat)
open Forest

/-- Cursor in the graph's payload order, including the final cursor at chain 32. -/
def cursor (k : ℕ) : ℕ := if k < 4 then 160*k else if k < 20 then 640+152*(k-4) else 3072+192*(k-20)
/-- Offset in the wire payload, in bits. -/
def wireOffset (k : ℕ) : ℕ := 8 * wireByte k

theorem cursor_step (k : Fin 32) : cursor (k.val+1) = cursor k + chainBits k := by
  unfold cursor chainBits
  split_ifs <;> omega

theorem cursor_zero : cursor 0 = 0 := rfl
theorem cursor_end : cursor 32 = 5376 := by decide

theorem wireOffset_aligned (k : Fin 32) : wireOffset k % 8 = 0 := by
  unfold wireOffset; omega

theorem wireOffset_contained (k : Fin 32) : wireOffset k + chainBits k ≤ 5376 := by
  revert k; decide

theorem wireSlot_eq (k : Fin 32) : wireSlot k = 0x400040 + wireOffset k / 8 := by
  revert k; decide

theorem slot_bounds (k : Fin 32) :
    0x3FFFE0 ≤ slot k ∧ slot k + 24 ≤ 0x4002E0 ∧ slot k % 8 = 0 := by
  revert k; decide

theorem output_bounds (k : Fin 32) :
    0x3FFFD8 ≤ outAddr k ∧ outAddr k + 32 ≤ 0x4002E0 ∧ outAddr k % 8 = 0 := by
  have h := slot_bounds k
  unfold outAddr; omega

/-- The state of every chain begins `truncOff k / 8` bytes into its answer buffer: byte 8 for a
chain in its cell, byte 13 for the four chains hashed in place five bytes above their cells. -/
theorem work_eq' : ∀ k : Fin 32, work k = outAddr k + truncOff k / 8 := by
  decide +kernel

theorem work_of_expands {k : ℕ} (h : expands k = true) : work k = slot k := by
  unfold work
  exact if_pos h

theorem work_of_not_expands {k : ℕ} (h : ¬ expands k = true) : work k = wireSlot k := by
  unfold work
  exact if_neg h

/-- Every wire value lies at or above its own cell's state address, so the ascending
hash writes never reach an unread wire block. -/
theorem wireSlot_ge_slot (k : Fin 32) : slot k ≤ wireSlot k := by
  revert k; decide

/-- Expanding a chain never overwrites a later, unread wire block. -/
theorem unread_disjoint (k j : Fin 32) (hkj : k.val < j.val) :
    wireSlot j + chainBits j / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ wireSlot j := by
  right
  have h := wireSlot_ge_slot j
  unfold outAddr slot at *
  omega

/-- Position of the bytes committed by the root for a completed chain: the low 192 bits
of every cell. -/
def rootSliceAddr (k : ℕ) : ℕ := outAddr k
def rootSliceBits (_k : ℕ) : ℕ := 192

/-- Every later hash preserves the committed slice of an earlier chain. -/
theorem completed_disjoint (j k : Fin 32) (hjk : j.val < k.val) :
    rootSliceAddr j + rootSliceBits j / 8 ≤ outAddr k ∨
      outAddr k + 32 ≤ rootSliceAddr j := by
  left
  unfold rootSliceAddr rootSliceBits outAddr slot
  omega

theorem payload_index (k : Fin 32) (i : ℕ) (hi : i < chainBits k) :
    Payload.index 5376 (cursor k + i) = wireOffset k + i := by
  revert i k; decide +kernel

end OptimalOTS.RiscvMixedProgram
