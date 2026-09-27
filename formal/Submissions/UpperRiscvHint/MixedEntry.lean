import Submissions.UpperRiscvHint.MixedMemory
import Submissions.UpperRiscvHint.MixedJump

namespace OptimalOTS.RiscvMixedProgram
open RiscvZkvm.Rv64
open Riscv2Program
open Forest

/-- `x10` before chain `k`'s pointer moves: the previous chain's working address. -/
def prevInput (k : ℕ) : ℕ := if k = 0 then hashBase else work (k-1)

theorem input_delta_range' : ∀ k : Chain,
    -2048 ≤ (work k : ℤ)-prevInput k ∧ (work k : ℤ)-prevInput k < 2048 := by
  decide +kernel

theorem output_delta_range' : ∀ k : Chain,
    -2048 ≤ (outAddr k : ℤ)-work k ∧ (outAddr k : ℤ)-work k < 2048 := by
  decide +kernel

theorem work_bounds (k : Chain) : 32 ≤ work k ∧ work k + 24 < 2^62 := by
  have := wireOffset_contained k
  unfold honestViewBits at this
  rw [work_eq_view]; omega

theorem prevInput_bounds' : ∀ k : Chain, prevInput k < 2^62 := by
  decide +kernel

theorem prevInput_bounds (k : Chain) : prevInput k < 2^62 := prevInput_bounds' k

theorem input_step (s : MachineState) (k : Chain) (hp : s.getReg .x10 = W (prevInput k)) :
    s.getReg .x10 + signExtend12 (imm12 ((work k : ℤ)-prevInput k)) = W (work k) := by
  have h := input_delta_range' k
  rw [hp, W_add_imm _ _ h.1 h.2 (by omega) (prevInput_bounds k)]
  congr 1; omega

theorem output_step (k : Chain) :
    W (work k) + signExtend12 (imm12 ((outAddr k : ℤ)-work k)) = W (outAddr k) := by
  have h := output_delta_range' k
  have b := work_bounds k
  rw [W_add_imm _ _ h.1 h.2 (by omega) (by omega)]
  congr 1; omega

structure EntryEffect (a b : MachineState) (k : Chain) : Prop where
  input : b.getReg .x10 = W (work k)
  out : b.getReg .x12 = W (outAddr k)
  regs : ∀ r, r ≠ .x10 → r ≠ .x12 → b.getReg r = a.getReg r
  mem : b.mem = a.mem
  pc : b.pc = a.pc+8
  code : b.code = a.code

theorem enter_effect (s : MachineState) (k : Chain)
    (hp : s.getReg .x10 = W (prevInput k)) :
    EntryEffect s ((enter k (prevInput k)).foldl execInstrBr s) k := by
  have h1 := input_step s k hp
  have h2 := output_step k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [enter, execInstrBr, getReg_setReg_ite, h1]
  · simp [enter, execInstrBr, getReg_setReg_ite, h1, h2]
  · intro r h10 h12
    simp [enter, execInstrBr, getReg_setReg_ite, h10, h12]
  · rfl
  · change s.pc+4+4 = s.pc+8
    rw [BitVec.add_assoc]; rfl
  · rfl

theorem enter_ready (s : MachineState) (k previous : ℕ) :
    Riscv.LinearReady s (enter k previous) := by
  simp [enter, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

end OptimalOTS.RiscvMixedProgram
