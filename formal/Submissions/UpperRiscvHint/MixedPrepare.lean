import Submissions.UpperRiscvHint.MixedChainFrame
import Submissions.UpperRiscvHint.MixedChainStart

namespace OptimalOTS.RiscvMixedProgram
open OptimalOTS.Dag
open RiscvZkvm.Rv64 Forest Forest.Name OracleComp
open Riscv2Program

/-- The pointer move from chain `2q + 1` to chain `k = 2q + 2` preserves every value and slice. -/
theorem move_refines (index : RawIdx) (wire : List Bool) (pk : PublicKey)
    (q : Fin 16) (k : Chain) (hk : k.val = 2*q.val+2)
    (s : MachineState) (x : graph.Assignment) (tail : Code)
    (ctx : Ctx s index wire pk) (input : s.getReg .x10 = W (prevInput k))
    (out : s.getReg .x12 = W (outAddr (2*q.val+1)))
    (len : s.getReg .x11 = W (chainBits k)) (payload : PayloadFrom s wire k)
    (done : Completed s (tops x) k)
    (located : Riscv.CodeAt s s.pc (enter k (prevInput k) ++ tail))
    (Q : OracleComp Spec (Option Bool)) (c fuel : ℕ) (hf : 2 ≤ fuel)
    (continuation : ∀ u, HashInv index wire pk u x k (work k) →
      MemBits u (W (work k)) (ofBits (chainBits k) (wire.drop (wireOffset k))) →
      Riscv.CodeAt u u.pc tail → Riscv.Refines (fuel-2) u Q c) :
    Riscv.Refines fuel s Q (2+c) := by
  have E := enter_effect s k input
  have ready := enter_ready s k (prevInput k)
  let u := (enter k (prevInput k)).foldl execInstrBr s
  have prev : prevInput k = work (2*q.val+1) := by
    unfold prevInput; rw [if_neg (by omega)]; congr 1; omega
  have uctx : Ctx u index wire pk :=
    ctx.enter q (input.trans (by rw [prev])) out (E.input.trans (by rw [hk]))
      (E.out.trans (by rw [hk])) E.regs E.mem E.code
  have urange : 32 ≤ work k ∧ work k+24 ≤ 0x78000000 := by
    have h := wireOffset_contained k
    unfold honestViewBits at h
    rw [work_eq_view]; omega
  have inv : HashInv index wire pk u x k (work k) := by
    refine ⟨uctx, E.input, urange, ?_, E.out, ?_, ?_⟩
    · rw [E.regs .x11 (by decide) (by decide)]; exact len
    · intro j hj; exact memBits_of_mem_eq E.mem (payload j (by omega))
    · intro j hj; exact memBits_of_mem_eq E.mem (done j hj)
  have held := memBits_of_mem_eq E.mem (payload k le_rfl)
  have loc : Riscv.CodeAt u u.pc tail := by
    rw [E.pc]
    exact located.append_right.code_eq E.code
  rw [show fuel = (enter k (prevInput k)).length+(fuel-2) by change fuel=2+(fuel-2); omega]
  exact Riscv.Refines.linear _ located.append_left ready (continuation u inv held loc)

end OptimalOTS.RiscvMixedProgram
