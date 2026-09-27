import Submissions.UpperRiscv.MixedChainSemantics
import Submissions.UpperRiscv.MixedEntry

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64
open Riscv2Program
open Forest Forest.Name OracleComp

def CtxReg (r : Reg) : Prop := r = .x30 ∨ r = .x31 ∨ r = .x5 ∨ r = .x13 ∨ r = .x1 ∨ r = .x29

theorem Ctx.frame {s t : MachineState} {index : RawIdx} {v : ℕ} {pk : PublicKey} {a : ℕ} (ctx : Ctx s index v pk a)
    (regs : ∀ r, CtxReg r → t.getReg r = s.getReg r) (mem : t.mem = s.mem)
    (code : t.code = s.code) : Ctx t index v pk a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ctx.short, ?_, ?_, ctx.code.code_eq code⟩
  · rw [regs .x30 (by simp [CtxReg])]; exact ctx.pk0
  · rw [regs .x31 (by simp [CtxReg])]; exact ctx.pk1
  · rw [regs .x5 (by simp [CtxReg])]; exact ctx.call
  · intro q
    simpa only [MachineState.getHalfword, MachineState.getMem, mem] using ctx.lanes q
  · rw [regs .x13 (by simp [CtxReg])]; exact ctx.sigLen
  · rw [regs .x1 (by simp [CtxReg])]; exact ctx.bound
  · rw [regs .x29 (by simp [CtxReg])]; exact ctx.count

/-- A chain hash preserves the dispatch table and all fixed registers. -/
theorem Ctx.writeHash {s : MachineState} {index : RawIdx} {v : ℕ} {pk : PublicKey} {a : ℕ}
    (ctx : Ctx s index v pk a) (k : Fin 33) (y : BitVec hashBits)
    (ho : s.getReg .x12 = W (outAddr k)) : Ctx (Riscv.writeHash s y) index v pk a := by
  have b := output_bounds k
  refine ⟨?_, ?_, ?_, ?_, ?_, ctx.short, ?_, ?_, ctx.code.code_eq (writeHash_code s y)⟩
  · rw [writeHash_regs]; exact ctx.pk0
  · rw [writeHash_regs]; exact ctx.pk1
  · rw [writeHash_regs]; exact ctx.call
  · intro q
    have he : (Riscv.writeHash s y).getHalfword (W (laneAddr q)) = s.getHalfword (W (laneAddr q)) := by
      simp only [MachineState.getHalfword]
      rw [writeHash_frame]
      intro j hj he
      have e := congrArg BitVec.toNat he
      have hq := q.isLt
      unfold laneBase at b
      rw [alignToDword_toNat, ho, W_add,
        W_toNat _ (by unfold laneAddr laneBase; omega), W_toNat _ (by omega)] at e
      unfold laneAddr laneBase at e
      omega
    rw [he]; exact ctx.lanes q
  · rw [writeHash_regs]; exact ctx.sigLen
  · rw [writeHash_regs]; exact ctx.bound
  · rw [writeHash_regs]; exact ctx.count

/-- Each chain input costs one oracle compression, at either state width. -/
theorem chain_blockCost (k : Fin 33) : blockCost (chainBits k) = 1 := by
  rcases chainBits_cases k with h | h <;> rw [h] <;> decide

/-- A chain hash is valid at any input address in memory. -/
theorem chain_hashValid (s : MachineState) (k : Fin 33) (base : ℕ)
    (hp : s.getReg .x10 = W base) (ho : s.getReg .x12 = W (outAddr k))
    (hn : s.getReg .x11 = W (chainBits k)) (hb : 32 ≤ base ∧ base+24 ≤ 0x78000000) :
    Riscv.hashArgumentsValid s = true := by
  have bo := output_bounds k
  have hlen := chainBits_le k
  have hmin := chainBits_ge k
  unfold laneBase regionAddr at bo
  have r1 : isValidOutputRange (W base) ((chainBits k+7)/8) = true :=
    range_ok _ _ hb.1 (by omega) (by omega) (by omega)
  have r2 := hashOutput_ok (outAddr k) (by omega) (by omega) bo.2.2
  unfold Riscv.hashArgumentsValid
  rw [hp, ho, hn, W_toNat _ (by omega), r1, Bool.true_and]
  exact r2

end OptimalOTS.RiscvMixedProgram
