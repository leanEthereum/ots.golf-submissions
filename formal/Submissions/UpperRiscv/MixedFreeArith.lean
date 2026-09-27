import Submissions.UpperRiscv.MixedJump
import Submissions.UpperRiscv.MixedCode

/-! The count-byte dispatch of the free chain: `x28 = 5465 - 4 v`, and the jump lands `v`
entries before prologue 0. Entries for `v < 16` are hash steps; the others branch to the index
phase's rejection. -/

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program

theorem free_target (v : ℕ) (hv : v < 256) :
    ((W 5465 - W (4*v)) + signExtend12 (imm12 freeImm)) &&& ~~~(1#64) =
      W (4096 + 4*(prologue0At - v)) := by
  have e : W 5465 - W (4*v) = W (5465 - 4*v) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, W_toNat _ (by omega), W_toNat _ (by omega)]; omega),
      W_toNat _ (by omega), W_toNat _ (by omega), W_toNat _ (by omega)]
  rw [e, W_add_imm _ _ (by decide) (by decide) (by unfold freeImm prologue0At boundWord; omega)
    (by omega)]
  have e2 : (((5465 - 4*v : ℕ) : ℤ) + freeImm).toNat = 4096 + 4*(prologue0At - v) := by
    unfold freeImm prologue0At boundWord; omega
  rw [e2]
  apply and_not_one_of_even
  rw [W_toNat _ (by unfold prologue0At; omega)]
  omega

theorem freeTable_low (v : ℕ) (hv : v < 16) :
    (freeTable ++ prologue 0).drop (255 - v) = List.replicate v .ECALL ++ prologue 0 := by
  interval_cases v <;> decide +kernel

theorem freeTable_length : freeTable.length = 255 := by simp [freeTable]

theorem freeTable_high (v : ℕ) (hv : 16 ≤ v) (hv' : v < 256) :
    (freeTable ++ prologue 0)[255 - v]? =
      some (.BEQ .x0 .x0 (BitVec.ofInt 13 (4*((indexStub : ℤ) - (freeTableAt + ((255 - v : ℕ) : ℤ)))))) := by
  rw [List.getElem?_append_left (by rw [freeTable_length]; omega)]
  unfold freeTable
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, freeEntry]
  rw [if_neg (by omega)]

set_option maxRecDepth 100000 in
theorem freeBranch_target' : ∀ v : Fin 256, 16 ≤ v.val →
    W (4096 + 4*(prologue0At - v.val)) +
      signExtend13 (BitVec.ofInt 13 (4*((indexStub : ℤ) - (freeTableAt + ((255 - v.val : ℕ) : ℤ))))) =
      W (4096 + 4*indexStub) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem freeBranch_admitted' : ∀ v : Fin 256, 16 ≤ v.val →
    Riscv.admittedInstruction
      (.BEQ .x0 .x0 (BitVec.ofInt 13 (4*((indexStub : ℤ) - (freeTableAt + ((255 - v.val : ℕ) : ℤ)))))) =
      true := by
  decide +kernel

/-- The branch of a high entry reaches the index phase's rejection. -/
theorem freeBranch_target (v : ℕ) (hv : 16 ≤ v) (hv' : v < 256) :
    W (4096 + 4*(prologue0At - v)) +
      signExtend13 (BitVec.ofInt 13 (4*((indexStub : ℤ) - (freeTableAt + ((255 - v : ℕ) : ℤ))))) =
      W (4096 + 4*indexStub) :=
  freeBranch_target' ⟨v, hv'⟩ hv

end OptimalOTS.RiscvMixedProgram
