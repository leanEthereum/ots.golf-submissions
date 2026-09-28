import Submissions.UpperRiscv.MixedContext
import Submissions.UpperRiscv.Names

/-! Byte geometry of the chains: values, answer buffers, root slots, the seven bytes past the
region, and the order constraints that make every hash leave unread values and committed slots
intact. Chains are numbered by execution position. -/

set_option maxRecDepth 100000

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program (W W_toNat laneBase)
open Forest

/-- Offset of chain `k`'s value in the payload, in bits. -/
def wireOffset (k : ℕ) : ℕ := 8 * valueOffs.getD k 0

/-- Address of chain `k`'s root slot. -/
def slotAddr (k : Fin 33) : ℕ := regionAddr + slotPos k / 8

/-- The seven bytes past the region, read by the root query of an oversized signature. -/
def tailAddr : ℕ := regionAddr + 800

theorem valueAddr_eq' : ∀ k : Fin 33, valueAddr k = payloadAddr + wireOffset k / 8 := by
  decide +kernel

theorem wireOffset_aligned' : ∀ k : Fin 33, wireOffset k % 8 = 0 := by decide +kernel

theorem wireOffset_contained' : ∀ k : Fin 33, wireOffset k + chainBits k ≤ 5328 := by
  decide +kernel

theorem chainBits_bytes' : ∀ k : Fin 33, chainBits k = 8 * chainBytes k := by decide +kernel

theorem truncOff_bytes' : ∀ k : Fin 33, truncOff k = 8 * truncBytes k := by decide +kernel

theorem output_bounds' : ∀ k : Fin 33,
    regionAddr - 8 ≤ outAddr k ∧ outAddr k + 32 ≤ laneBase ∧ outAddr k % 8 = 0 := by
  decide +kernel

theorem value_bounds' : ∀ k : Fin 33,
    payloadAddr ≤ valueAddr k ∧ valueAddr k + chainBytes k ≤ tailAddr := by
  decide +kernel

theorem slot_eq' : ∀ k : Fin 33, slotAddr k = outAddr k + topOff k / 8 := by decide +kernel

theorem slotPos_aligned' : ∀ k : Fin 33, slotPos k % 8 = 0 := by decide +kernel

theorem topBits_aligned' : ∀ k : Fin 33, topBits k % 8 = 0 := by decide +kernel

/-- A cap's value lies on its root slot. -/
theorem cap_value_slot' : ∀ k : Fin 33, capChain k = true →
    valueAddr k = slotAddr k ∧ work k = valueAddr k := by
  decide +kernel

/-- Only expanding chains read their value away from their working address. -/
theorem work_value' : ∀ k : Fin 33, expands k = false → work k = valueAddr k := by
  decide +kernel

theorem capChain_iff' : ∀ k : Fin 33, capChain k = true ↔ isCap k := by decide +kernel

theorem cap_not_expands' : ∀ k : Fin 33, capChain k = true → expands k = false := by
  decide +kernel

/-- A hash never overwrites the value of a chain that runs later. -/
theorem unread_disjoint' : ∀ k j : Fin 33, k.val < j.val →
    valueAddr j + chainBytes j ≤ outAddr k ∨ outAddr k + 32 ≤ valueAddr j := by
  decide +kernel

/-- A hash never overwrites the root slot of a chain that ran earlier. -/
theorem completed_disjoint' : ∀ j k : Fin 33, j.val < k.val →
    slotAddr j + topBits j / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ slotAddr j := by
  decide +kernel

/-- Every chain answer buffer is disjoint from the seven bytes past the region. -/
theorem tail_disjoint' : ∀ k : Fin 33,
    tailAddr + 7 ≤ outAddr k ∨ outAddr k + 32 ≤ tailAddr := by
  decide +kernel


theorem valueAddr_eq (k : Fin 33) : valueAddr k = payloadAddr + wireOffset k / 8 := valueAddr_eq' k
theorem wireOffset_aligned (k : Fin 33) : wireOffset k % 8 = 0 := wireOffset_aligned' k
theorem wireOffset_contained (k : Fin 33) : wireOffset k + chainBits k ≤ 5328 :=
  wireOffset_contained' k
theorem chainBits_bytes (k : Fin 33) : chainBits k = 8 * chainBytes k := chainBits_bytes' k
theorem truncOff_bytes (k : Fin 33) : truncOff k = 8 * truncBytes k := truncOff_bytes' k
theorem output_bounds (k : Fin 33) :
    regionAddr - 8 ≤ outAddr k ∧ outAddr k + 32 ≤ laneBase ∧ outAddr k % 8 = 0 := output_bounds' k
theorem value_bounds (k : Fin 33) :
    payloadAddr ≤ valueAddr k ∧ valueAddr k + chainBytes k ≤ tailAddr := value_bounds' k
theorem slot_eq (k : Fin 33) : slotAddr k = outAddr k + topOff k / 8 := slot_eq' k
theorem work_eq (k : Fin 33) : work k = outAddr k + truncOff k / 8 := by
  unfold work; rw [truncOff_bytes]; omega
theorem unread_disjoint (k j : Fin 33) (h : k.val < j.val) :
    valueAddr j + chainBytes j ≤ outAddr k ∨ outAddr k + 32 ≤ valueAddr j := unread_disjoint' k j h
theorem completed_disjoint (j k : Fin 33) (h : j.val < k.val) :
    slotAddr j + topBits j / 8 ≤ outAddr k ∨ outAddr k + 32 ≤ slotAddr j :=
  completed_disjoint' j k h
theorem tail_disjoint (k : Fin 33) :
    tailAddr + 7 ≤ outAddr k ∨ outAddr k + 32 ≤ tailAddr := tail_disjoint' k

end OptimalOTS.RiscvMixedProgram
