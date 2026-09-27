import Submissions.UpperRiscv.MixedMemory
import Submissions.UpperRiscv.MixedJump

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

/-- The input pointer before chain `k`: the public key for the free chain, else the previous
chain's working address. -/
def prevInput (k : ℕ) : ℕ := if k = 0 then hashBase else work (k-1)
def enterPointers (k : ℕ) : Code :=
  [.ADDI .x10 .x10 (imm12 ((valueAddr k : ℤ)-prevInput k)),
   .ADDI .x12 .x10 (imm12 ((outAddr k : ℤ)-valueAddr k))]
def redirectCode (k : ℕ) : Code := [.ADDI .x10 .x12 (imm12 (truncBytes k))]

theorem enter_parts (k : ℕ) : enter k (prevInput k) = enterPointers k ++
    (if expands k then [.ECALL] ++ redirectCode k else []) := rfl

theorem input_delta_range' : ∀ k : Fin 33,
    -2048 ≤ (valueAddr k : ℤ)-prevInput k ∧ (valueAddr k : ℤ)-prevInput k < 2048 := by
  decide +kernel

theorem output_delta_range' : ∀ k : Fin 33,
    -2048 ≤ (outAddr k : ℤ)-valueAddr k ∧ (outAddr k : ℤ)-valueAddr k < 2048 := by
  decide +kernel

theorem valueAddr_bounds (k : Fin 33) : 32 ≤ valueAddr k ∧ valueAddr k + 24 < 2^62 := by
  have := value_bounds k
  unfold payloadAddr tailAddr regionAddr at *
  omega

theorem prevInput_bounds' : ∀ k : Fin 33, prevInput k < 2^62 := by
  decide +kernel

theorem prevInput_bounds (k : Fin 33) : prevInput k < 2^62 := prevInput_bounds' k

theorem input_step (s : MachineState) (k : Fin 33) (hp : s.getReg .x10 = W (prevInput k)) :
    s.getReg .x10 + signExtend12 (imm12 ((valueAddr k : ℤ)-prevInput k)) = W (valueAddr k) := by
  have h := input_delta_range' k
  rw [hp, W_add_imm _ _ h.1 h.2 (by omega) (prevInput_bounds k)]
  congr 1; omega

theorem output_step (k : Fin 33) :
    W (valueAddr k) + signExtend12 (imm12 ((outAddr k : ℤ)-valueAddr k)) = W (outAddr k) := by
  have h := output_delta_range' k
  have b := valueAddr_bounds k
  rw [W_add_imm _ _ h.1 h.2 (by omega) (by omega)]
  congr 1; omega

structure EntryEffect (a b : MachineState) (k : Fin 33) : Prop where
  input : b.getReg .x10 = W (valueAddr k)
  out : b.getReg .x12 = W (outAddr k)
  regs : ∀ r, r ≠ .x10 → r ≠ .x12 → b.getReg r = a.getReg r
  mem : b.mem = a.mem
  pc : b.pc = a.pc+8
  code : b.code = a.code

theorem enterPointers_effect (s : MachineState) (k : Fin 33)
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

theorem truncBytes_lt' : ∀ k : Fin 33, truncBytes k < 32 := by decide +kernel

/-- After the first hash of an expanding chain its state begins `truncBytes k` bytes into the
output. -/
theorem redirect_input (s : MachineState) (k : Fin 33) (ho : s.getReg .x12 = W (outAddr k)) :
    (execInstrBr s (.ADDI .x10 .x12 (imm12 (truncBytes k)))).getReg .x10 = W (work k) := by
  have hs := output_bounds k
  have ht := truncBytes_lt' k
  simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, and_true, ho]
  rw [W_add_imm _ _ (by omega) (by omega) (by omega) (by unfold laneBase at hs; omega)]
  have e : ((outAddr k : ℤ) + (truncBytes k : ℤ)).toNat = work k := by unfold work; omega
  rw [e]

end OptimalOTS.RiscvMixedProgram
