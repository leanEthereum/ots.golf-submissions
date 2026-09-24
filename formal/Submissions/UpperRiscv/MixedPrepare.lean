import Submissions.UpperRiscv.MixedChainFrame
import Submissions.UpperRiscv.MixedChainStart

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name OracleComp
open Riscv2Program

/-- The pointer setup preserves all disclosed blocks and completed slices. -/
theorem move_refines (index : RawIdx) (wire : List Bool) (pk : PublicKey)
    (k : Fin 32) (s : MachineState) (x : graph.Assignment) (tail : Code)
    (ctx : Ctx s index pk) (input : s.getReg .x10 = W (prevInput k))
    (len : s.getReg .x11 = W (chainBits k)) (payload : PayloadFrom s wire k)
    (done : Completed s (tops x) k)
    (located : Riscv.CodeAt s s.pc (enterPointers k ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : 2 ≤ fuel)
    (continuation : ∀ u, HashInv index wire pk u x k (wireSlot k) →
      MemBits u (W (wireSlot k)) (ofBits (chainBits k) (wire.drop (wireOffset k))) →
      Riscv.CodeAt u u.pc tail → Riscv.Refines (fuel-2) u Q c) :
    Riscv.Refines fuel s Q (2+c) := by
  have E := enterPointers_effect s k input
  have ready := enterPointers_ready s k
  let u := (enterPointers k).foldl execInstrBr s
  have uctx : Ctx u index pk := ctx.frame (fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl <;> exact E.regs _ (by decide) (by decide)) E.mem E.code
  have urange : 32 ≤ wireSlot k ∧ wireSlot k+24 ≤ 0x78000000 := by
    have h := wireOffset_contained k
    rw [wireSlot_eq]; omega
  have inv : HashInv index wire pk u x k (wireSlot k) := by
    refine ⟨uctx, E.input, urange, ?_, E.out, ?_, ?_⟩
    · rw [E.regs .x11 (by decide) (by decide)]; exact len
    · intro j hj; exact memBits_of_mem_eq E.mem (payload j (by omega))
    · intro j hj; exact memBits_of_mem_eq E.mem (done j hj)
  have held := memBits_of_mem_eq E.mem (payload k le_rfl)
  have loc : Riscv.CodeAt u u.pc tail := by
    rw [E.pc]
    exact located.append_right.code_eq E.code
  rw [show fuel = (enterPointers k).length+(fuel-2) by change fuel=2+(fuel-2); omega]
  exact Riscv.Refines.linear _ located.append_left ready (continuation u inv held loc)

/-- The redirect after an early hash preserves every memory invariant. -/
theorem redirect_refines (index : RawIdx) (wire : List Bool) (pk : PublicKey)
    (k : Fin 32) (base : ℕ) (s : MachineState) (x : graph.Assignment) (tail : Code)
    (inv : HashInv index wire pk s x k base)
    (located : Riscv.CodeAt s s.pc ([.ADDI .x10 .x12 8] ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : 1 ≤ fuel)
    (continuation : ∀ u, HashInv index wire pk u x k (slot k) → u.mem=s.mem →
      Riscv.CodeAt u u.pc tail → Riscv.Refines (fuel-1) u Q c) :
    Riscv.Refines fuel s Q (1+c) := by
  let front : Code := [.ADDI .x10 .x12 8]
  let u := front.foldl execInstrBr s
  have ready : Riscv.LinearReady s front := by
    simp [front, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
  have ui : u.getReg .x10 = W (slot k) := redirect_input s k inv.out
  have urange : 32 ≤ slot k ∧ slot k+24 ≤ 0x78000000 := by have := slot_bounds k; omega
  have inv' : HashInv index wire pk u x k (slot k) :=
    HashInv.frame index wire pk inv (slot k) ui urange (fun r h10 _ => by
      simp [u, front, execInstrBr, getReg_setReg_ite, h10]) rfl rfl
  have loc : Riscv.CodeAt u u.pc tail := located.append_right.code_eq rfl
  rw [show fuel=front.length+(fuel-1) by change fuel=1+(fuel-1); omega]
  exact Riscv.Refines.linear _ located.append_left ready (continuation u inv' rfl loc)

end OptimalOTS.RiscvMixedProgram
