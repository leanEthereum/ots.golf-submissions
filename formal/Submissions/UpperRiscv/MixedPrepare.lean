import Submissions.UpperRiscv.MixedChainFrame

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name OracleComp
open Riscv2Program

variable (index : RawIdx) (v : ℕ) (wire : List Bool) (pk : PublicKey) {a : ℕ}

/-- The pointer setup preserves all values, committed slots and the six bytes past the region. -/
theorem move_refines (k : Fin 33) (s : MachineState) (x : graph.Assignment) (tail : Code)
    (ctx : Ctx s index v pk a) (input : s.getReg .x10 = W (prevInput k))
    (len : s.getReg .x11 = W (chainBits k)) (payload : PayloadFrom s wire k)
    (done : Completed s x k) (tailInv : TailInv index v wire s x k)
    (located : Riscv.CodeAt s s.pc (enterPointers k ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : 2 ≤ fuel)
    (continuation : ∀ u, HashInv index v wire pk a u x k (valueAddr k) →
      MemBits u (W (valueAddr k)) (ofBits (chainBits k) (wire.drop (wireOffset k))) →
      TailInv index v wire u x k →
      Riscv.CodeAt u u.pc tail → Riscv.Refines (fuel-2) u Q c) :
    Riscv.Refines fuel s Q (2+c) := by
  have E := enterPointers_effect s k input
  have ready := enterPointers_ready s k
  let u := (enterPointers k).foldl execInstrBr s
  have uctx : Ctx u index v pk a := ctx.frame (fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact E.regs _ (by decide) (by decide)) E.mem E.code
  have urange : 32 ≤ valueAddr k ∧ valueAddr k+24 ≤ 0x78000000 := by
    have := value_bounds k; unfold payloadAddr tailAddr regionAddr at *; omega
  have utail : TailInv index v wire u x k := memBits_of_mem_eq E.mem tailInv
  have inv : HashInv index v wire pk a u x k (valueAddr k) := by
    refine ⟨uctx, E.input, urange, ?_, E.out, ?_, ?_, fun _ => utail⟩
    · rw [E.regs .x11 (by decide) (by decide)]; exact len
    · intro j hj; exact memBits_of_mem_eq E.mem (payload j (by omega))
    · intro j hj; exact memBits_of_mem_eq E.mem (done j hj)
  have held := memBits_of_mem_eq E.mem (payload k le_rfl)
  have loc : Riscv.CodeAt u u.pc tail := by
    rw [E.pc]
    exact located.append_right.code_eq E.code
  rw [show fuel = (enterPointers k).length+(fuel-2) by change fuel=2+(fuel-2); omega]
  exact Riscv.Refines.linear _ located.append_left ready (continuation u inv held utail loc)

/-- The redirect after an early hash preserves every memory invariant. -/
theorem redirect_refines (k : Fin 33) (base : ℕ) (s : MachineState) (x : graph.Assignment)
    (tail : Code) (inv : HashInv index v wire pk a s x k base)
    (located : Riscv.CodeAt s s.pc (redirectCode k ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : 1 ≤ fuel)
    (continuation : ∀ u, HashInv index v wire pk a u x k (work k) → u.mem=s.mem →
      Riscv.CodeAt u u.pc tail → Riscv.Refines (fuel-1) u Q c) :
    Riscv.Refines fuel s Q (1+c) := by
  let front : Code := redirectCode k
  let u := front.foldl execInstrBr s
  have ready : Riscv.LinearReady s front := by
    simp [front, redirectCode, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
  have ui : u.getReg .x10 = W (work k) := redirect_input s k inv.out
  have urange : 32 ≤ work k ∧ work k+24 ≤ 0x78000000 := by
    have := output_bounds k; have := truncBytes_lt' k
    unfold work; unfold laneBase regionAddr at *; omega
  have inv' : HashInv index v wire pk a u x k (work k) :=
    HashInv.frame index v wire pk inv (work k) ui urange (fun r h10 _ => by
      simp [u, front, redirectCode, execInstrBr, getReg_setReg_ite, h10]) rfl rfl
  have loc : Riscv.CodeAt u u.pc tail := located.append_right.code_eq rfl
  rw [show fuel=front.length+(fuel-1) by change fuel=1+(fuel-1); omega]
  exact Riscv.Refines.linear _ located.append_left ready (continuation u inv' rfl loc)

end OptimalOTS.RiscvMixedProgram
