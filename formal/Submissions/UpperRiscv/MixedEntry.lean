import Submissions.UpperRiscv.MixedMemory
import Submissions.UpperRiscv.MixedJump

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

def prevInput (k : ℕ) : ℕ := if k = 0 then hashBase else work (k-1)
def enterPointers (k : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((wireSlot k : ℤ)-prevInput k)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ)-wireSlot k))]

theorem enter_parts (k : ℕ) : enter k (prevInput k) = enterPointers k ++
    (if expands k then [.ECALL, .ADDI .x10 .x12 8] else []) := rfl

theorem input_delta_range' : ∀ k : Fin 32,
    -2048 ≤ (wireSlot k : ℤ)-prevInput k ∧ (wireSlot k : ℤ)-prevInput k < 2048 := by
  decide +kernel

theorem output_delta_range' : ∀ k : Fin 32,
    -2048 ≤ (outAddr k : ℤ)-wireSlot k ∧ (outAddr k : ℤ)-wireSlot k < 2048 := by
  decide +kernel

theorem wireSlot_bounds (k : Fin 32) : 32 ≤ wireSlot k ∧ wireSlot k + 24 < 2^62 := by
  have := wireOffset_contained k
  rw [wireSlot_eq]; omega

theorem prevInput_bounds' : ∀ k : Fin 32, prevInput k < 2^62 := by
  decide +kernel

theorem prevInput_bounds (k : Fin 32) : prevInput k < 2^62 := prevInput_bounds' k

theorem input_step (s : MachineState) (k : Fin 32) (hp : s.getReg .x10 = W (prevInput k)) :
    s.getReg .x10 + signExtend12 (imm12 ((wireSlot k : ℤ)-prevInput k)) = W (wireSlot k) := by
  have h := input_delta_range' k
  rw [hp, W_add_imm _ _ h.1 h.2 (by omega) (prevInput_bounds k)]
  congr 1; omega

theorem output_step (k : Fin 32) :
    W (wireSlot k) + signExtend12 (imm12 ((outAddr k : ℤ)-wireSlot k)) = W (outAddr k) := by
  have h := output_delta_range' k
  have b := wireSlot_bounds k
  rw [W_add_imm _ _ h.1 h.2 (by omega) (by omega)]
  congr 1; omega

structure EntryEffect (a b : MachineState) (k : Fin 32) : Prop where
  input : b.getReg .x10 = W (wireSlot k)
  out : b.getReg .x12 = W (outAddr k)
  regs : ∀ r, r ≠ .x10 → r ≠ .x12 → b.getReg r = a.getReg r
  mem : b.mem = a.mem
  pc : b.pc = a.pc+8
  code : b.code = a.code

theorem enterPointers_effect (s : MachineState) (k : Fin 32)
    (hp : s.getReg .x10 = W (prevInput k)) :
    EntryEffect s ((enterPointers k).foldl execInstrBr s) k := by
  have h1 := input_step s k hp
  have h2 := output_step k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [enterPointers, execInstrBr, getReg_setReg_ite, h1]
  · simp [enterPointers, execInstrBr, getReg_setReg_ite, h1, h2]
  · intro r h10 h12
    simp [enterPointers, execInstrBr, getReg_setReg_ite, h10, h12]
  · rfl
  · change s.pc+4+4 = s.pc+8
    rw [BitVec.add_assoc]; rfl
  · rfl

theorem enterPointers_ready (s : MachineState) (k : ℕ) : Riscv.LinearReady s (enterPointers k) := by
  simp [enterPointers, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

/-- After the first hash of an expanding chain its state begins eight bytes into the output. -/
theorem redirect_input (s : MachineState) (k : Fin 32) (ho : s.getReg .x12 = W (outAddr k)) :
    (execInstrBr s (.ADDI .x10 .x12 8)).getReg .x10 = W (slot k) := by
  have hs := slot_bounds k
  simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true, ho]
  rw [show (8:BitVec 12)=BitVec.ofNat 12 8 from rfl, signExtend12_nat _ (by norm_num), W_add]
  congr 1; unfold outAddr; omega

end OptimalOTS.RiscvMixedProgram
